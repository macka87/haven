--
-- testbench.vhd: Testbench for BM Converter
-- Copyright (C) 2006 CESNET
-- Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
-- 1. Redistributions of source code must retain the above copyright
--    notice, this list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright
--    notice, this list of conditions and the following disclaimer in
--    the documentation and/or other materials provided with the
--    distribution.
-- 3. Neither the name of the Company nor the names of its contributors
--    may be used to endorse or promote products derived from this
--    software without specific prior written permission.
--
-- This software is provided ``as is'', and any express or implied
-- warranties, including, but not limited to, the implied warranties of
-- merchantability and fitness for a particular purpose are disclaimed.
-- In no event shall the company or contributors be liable for any
-- direct, indirect, incidental, special, exemplary, or consequential
-- damages (including, but not limited to, procurement of substitute
-- goods or services; loss of use, data, or profits; or business
-- interruption) however caused and on any theory of liability, whether
-- in contract, strict liability, or tort (including negligence or
-- otherwise) arising in any way out of the use of this software, even
-- if advised of the possibility of such damage.
--
-- $Id$
--
-- TODO:
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;

use work.all; 

use fl_bfm_rdy_pkg.all;

-- ----------------------------------------------------------------------------
--                            ENTITY DECLARATION                             --
-- ----------------------------------------------------------------------------

entity testbench is
end testbench;

-- ----------------------------------------------------------------------------
--                         ARCHITECTURE DECLARATION                          --
-- ----------------------------------------------------------------------------

architecture behavior of testbench is
   
   -- Simulation constants ----------------------------------------------------
   constant  clk_per           : time     := 10 ns;
   constant  DATA_WIDTH        : integer  := 8;
   constant  rdy_signal_driver : RDYSignalDriver := RND;
   
   -- clock & reset & sync ----------------------------------------------------
   signal CLK                : std_logic; 
   signal RESET              : std_logic; 
   
   -- BM interface ------------------------------------------------------
   signal BM_GLOBAL_ADDR   : std_logic_vector(63 downto 0); 
   signal BM_LOCAL_ADDR    : std_logic_vector(31 downto 0);
   signal BM_LENGTH        : std_logic_vector(11 downto 0);
   signal BM_TAG           : std_logic_vector(15 downto 0);
   signal BM_TRANS_TYPE    : std_logic_vector(1 downto 0);
   signal BM_REQ           : std_logic;
   signal BM_ACK           : std_logic;
   signal BM_OP_TAG        : std_logic_vector(7 downto 0);
   signal BM_OP_DONE       : std_logic;

   -- IB interface -----------------------------------------------------
   signal IB_DATA         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal IB_SOF_N        : std_logic;
   signal IB_EOF_N        : std_logic;
   signal IB_SRC_RDY_N    : std_logic;
   signal IB_DST_RDY_N    : std_logic;
   signal IB_TAG          : std_logic_vector(7 downto 0);
   signal IB_TAG_VLD      : std_logic;
   

begin

   -- -------------------------------------------------------------------------
   --                      BM Converter component mapping                    --
   -- -------------------------------------------------------------------------

   UUT : entity work.BM_CONVERTER
   generic map(
      DATA_WIDTH      => DATA_WIDTH
   )
   port map( 
      CLK             => CLK,
      RESET           => RESET,
      
      BM_GLOBAL_ADDR  => BM_GLOBAL_ADDR,
      BM_LOCAL_ADDR   => BM_LOCAL_ADDR,
      BM_LENGTH       => BM_LENGTH,
      BM_TAG          => BM_TAG,
      BM_TRANS_TYPE   => BM_TRANS_TYPE,
      BM_REQ          => BM_REQ,
      BM_ACK          => BM_ACK,
      BM_OP_TAG       => BM_OP_TAG,
      BM_OP_DONE      => BM_OP_DONE,
      
      IB_DATA         => IB_DATA,
      IB_SOF_N        => IB_SOF_N,
      IB_EOF_N        => IB_EOF_N,
      IB_SRC_RDY_N    => IB_SRC_RDY_N,
      IB_DST_RDY_N    => IB_DST_RDY_N,
      IB_TAG          => IB_TAG,
      IB_TAG_VLD      => IB_TAG_VLD
   );
                   
   -- -------------------------------------------------------------------------
   --                        Monitor component mapping                       --
   -- -------------------------------------------------------------------------
   
   MONITOR_U : entity work.MONITOR
   generic map(
      RX_TX_DATA_WIDTH  => DATA_WIDTH,
      FILE_NAME         => "testbench.log",
      FRAME_PARTS       => 1,
      RDY_DRIVER        => rdy_signal_driver
   )
   port map(
      -- Common interface
      FL_RESET          => RESET,
      FL_CLK            => CLK,

      -- RX Frame link Interface
      RX_DATA           => IB_DATA,
      RX_REM            => (others => '1'),
      RX_SOF_N          => IB_SOF_N,
      RX_EOF_N          => IB_EOF_N,
      RX_SOP_N          => IB_SOF_N,
      RX_EOP_N          => IB_EOF_N,
      RX_SRC_RDY_N      => IB_SRC_RDY_N,
      RX_DST_RDY_N      => IB_DST_RDY_N
     ); 
 
   -- -------------------------------------------------------------------------
   --                    'Generation of input clock' Process                 --
   -- -------------------------------------------------------------------------
 
   clk_perp : process
   begin
      clk <= '1';
      wait for clk_per/2;
      clk <= '0';
      wait for clk_per/2;
   end process clk_perp;

   -- -------------------------------------------------------------------------
   --                       'Reset Generation' Process                       --
   -- -------------------------------------------------------------------------

   resetp : process
   begin
      reset<='1';
      wait for 10*clk_per;
      reset<='0';
      wait;
   end process resetp;

   -- ----------------------------------------------------------------------------
   --                          Main Testbench Process
   -- ----------------------------------------------------------------------------

   tb: process         
      
   -- ----------------------------------------------------------------
   --                        Testbench Body
   -- ----------------------------------------------------------------       
   begin 

      bm_global_addr    <= (others => '0');
      bm_local_addr     <= (others => '0');
      bm_length         <= (others => '0');
      bm_tag            <= (others => '0');
      bm_trans_type     <= "00";
      bm_req            <= '0';

      wait until reset'event and reset = '0';
      wait for clk_per;
      wait for 1 ns;
                   
      -----------------------------------------------------------------------
      
      for i in 1 to 5 loop
      
         bm_global_addr    <= X"0123456789ABCDEF";
         bm_local_addr     <= X"76543210";
         bm_length         <= X"000";
         bm_tag            <= X"4567";
         bm_trans_type     <= "00";
         bm_req            <= '1';
         
         wait until clk'event and clk='1' and bm_ack = '1';
         wait for 1 ns;
         
         bm_global_addr    <= X"2200000AA0000022";
         bm_local_addr     <= X"111EF111";
         bm_length         <= X"123";
         bm_tag            <= X"ABCD";
         bm_trans_type     <= "11";
         bm_req            <= '1';
         
         wait until clk'event and clk='1' and bm_ack = '1';
         wait for 1 ns;
         
         bm_global_addr    <= (others => '0');
         bm_local_addr     <= (others => '0');
         bm_length         <= (others => '0');
         bm_tag            <= (others => '0');
         bm_trans_type     <= "00";
         bm_req            <= '0';
         
         wait for 5*clk_per;
         
         bm_global_addr    <= X"F3300D0BB0DCC33F";
         bm_local_addr     <= X"544AA445";
         bm_length         <= X"FFF";
         bm_tag            <= X"0102";
         bm_trans_type     <= "10";
         bm_req            <= '1';
         
         wait until clk'event and clk='1' and bm_ack = '1';
         
         bm_global_addr    <= (others => '0');
         bm_local_addr     <= (others => '0');
         bm_length         <= (others => '0');
         bm_tag            <= (others => '0');
         bm_trans_type     <= "00";
         bm_req            <= '0';
      
         wait for 50*clk_per;
      
      end loop;
      
      -- ----------------------------------------------------------------------
      -- ----------------------------------------------------------------------      
      wait;
   end process; 

end;


 
