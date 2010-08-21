--
-- testbench.vhd: Testbench for EPI2MI Converter
-- Copyright (C) 2008 CESNET
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
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;

use work.all; 

use work.bmem_func.all;
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
   constant  clk_per        : time     := 10 ns;
   constant  DATA_WIDTH     : integer  := 32;
   constant  ADDR_WIDTH     : integer  := 5;
   
   -- clock & reset & sync ----------------------------------------------------
   signal CLK               : std_logic; 
   signal RESET             : std_logic; 
   
   -- MI interface ---------------------------------------------------------
   signal MI_DWR            : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal MI_ADDR           : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal MI_RD             : std_logic;
   signal MI_WR             : std_logic;
   signal MI_ARDY           : std_logic;
   signal MI_BE             : std_logic_vector(DATA_WIDTH/8-1 downto 0);
   signal MI_DRD            : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal MI_DRDY           : std_logic;
   
   -- IB WR interface ---------------------------------------------------------
   signal WR_REQ            : std_logic;
   signal WR_RDY            : std_logic;
   signal WR_DATA           : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal WR_ADDR           : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal WR_BE             : std_logic_vector(DATA_WIDTH/8-1 downto 0);
   signal WR_LENGTH         : std_logic_vector(11 downto 0);       
   signal WR_SOF            : std_logic;                           
   signal WR_EOF            : std_logic;
   
   -- IB RD interface ---------------------------------------------------------
   signal RD_REQ            : std_logic;
   signal RD_ARDY_ACCEPT    : std_logic;
   signal RD_ADDR           : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal RD_BE             : std_logic_vector(DATA_WIDTH/8-1 downto 0);
   signal RD_LENGTH         : std_logic_vector(11 downto 0);       
   signal RD_SOF            : std_logic;                           
   signal RD_EOF            : std_logic;
   
   signal RD_DATA           : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal RD_SRC_RDY        : std_logic;
   signal RD_DST_RDY        : std_logic;

   
begin

   -- -------------------------------------------------------------------------
   --                   EPI2MI Converter component mapping                   --
   -- -------------------------------------------------------------------------

   UUT : entity work.EPI2MI_CONVERTER
   generic map(
      DATA_WIDTH      => DATA_WIDTH,
      ADDR_WIDTH      => 5
   )
   port map( 
      CLK             => CLK,
      RESET           => RESET,
      
      MI_DWR          => MI_DWR,
      MI_ADDR         => MI_ADDR,
      MI_RD           => MI_RD,
      MI_WR           => MI_WR,
      MI_ARDY         => MI_ARDY,
      MI_BE           => MI_BE,
      MI_DRD          => MI_DRD,
      MI_DRDY         => MI_DRDY,
      
      WR_REQ          => WR_REQ,
      WR_RDY          => WR_RDY,
      WR_DATA         => WR_DATA,
      WR_ADDR         => WR_ADDR,
      WR_BE           => WR_BE,
      WR_LENGTH       => WR_LENGTH,
      WR_SOF          => WR_SOF,
      WR_EOF          => WR_EOF,
      
      RD_REQ          => RD_REQ,
      RD_ARDY_ACCEPT  => RD_ARDY_ACCEPT,
      RD_ADDR         => RD_ADDR,
      RD_BE           => RD_BE,
      RD_LENGTH       => RD_LENGTH,
      RD_SOF          => RD_SOF,
      RD_EOF          => RD_EOF,
      
      RD_DATA         => RD_DATA,
      RD_SRC_RDY      => RD_SRC_RDY,
      RD_DST_RDY      => RD_DST_RDY
   ); 
 
   
   -- -------------------------------------------------------------------------
   --                         Memory component mapping                       --
   -- -------------------------------------------------------------------------

   MEMORY : entity work.SP_BMEM
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      ITEMS          => 32,
      BRAM_TYPE      => 36,
      OUTPUT_REG     => AUTO
   )
   port map(
      RESET          => RESET,
      CLK            => CLK,
      
      PIPE_EN        => '0',
      RE             => MI_RD,
      WE             => MI_WR,
      ADDR           => MI_ADDR,
      DI             => MI_DWR,
      DO_DV          => MI_DRDY,
      DO             => MI_DRD
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

   -- -------------------------------------------------------------------------
   --                 'Generation of DST_RDY signal' Process                 --
   -- -------------------------------------------------------------------------
   
   rdyp: process
   begin
      SetSeed(14374);
      loop
         DriveRdyNRnd(CLK,RD_DST_RDY);
      end loop;
      --RD_DST_RDY <= '1';
      --wait;
   end process;
   
-- ----------------------------------------------------------------------------
--                          Main Testbench Process
-- ----------------------------------------------------------------------------
   
   
   tb: process         
   
   -- ----------------------------------------------------------------
   --                        Testbench Body
   -- ----------------------------------------------------------------       
   begin 

      WR_DATA    <= (others => '0');
      WR_ADDR    <= (others => '0');
      WR_BE      <= (others => '0');
      WR_REQ     <= '0';  
      
      RD_REQ     <= '0';
      RD_ADDR    <= (others => '0');
      RD_BE      <= (others => '0');
      
      wait until reset'event and reset = '0';
      wait for 3*clk_per;
      
      MI_ARDY  <= '1';
      
      -----------------------------------------------------------------------
      
      WRITE : for i in 0 to 10 loop
         
         WR_DATA    <= X"11223300"+i;
         WR_BE      <= "0010";
         WR_ADDR    <= "00000" + ((3*i) rem ADDR_WIDTH);
         WR_REQ     <= '1';
         
         wait for clk_per;
         if (WR_RDY = '0') then
            wait until WR_RDY = '1';
            wait for clk_per;
         end if;
         WR_REQ     <= '0';
         
         WR_DATA    <= X"AABBCC00"+i;
         WR_BE      <= "1111";
         WR_ADDR    <= "00000" + ((3*i+1) rem ADDR_WIDTH);
         WR_REQ     <= '1';
         
         wait for clk_per;
         if (WR_RDY = '0') then
            wait until WR_RDY = '1';
            wait for clk_per;
         end if;
         WR_REQ     <= '0';
         
         
         WR_DATA    <= X"C0000000"+i;
         WR_BE      <= "1001";
         WR_ADDR    <= "00000" + ((3*i+2) rem ADDR_WIDTH);
         WR_REQ     <= '1';
         
         wait for clk_per;
         if (WR_RDY = '0') then
            wait until WR_RDY = '1';
            wait for clk_per;
         end if;
         WR_REQ     <= '0';
         
         
         wait for (i mod 5)*clk_per;
      end loop;
      
      
      WR_DATA    <= (others => '0');
      WR_ADDR    <= (others => '0');
      WR_BE      <= (others => '0');
      WR_REQ     <= '0';  
      
      RD_REQ     <= '0';
      RD_ADDR    <= (others => '0');
      RD_BE      <= (others => '0');
      
      wait for 50*clk_per;
      
      
      READ : for i in 0 to 31 loop
         
         RD_ADDR    <= "00000" + ((5*i+4) rem ADDR_WIDTH);
         RD_REQ     <= '1';
         
         wait for clk_per;
         if (RD_ARDY_ACCEPT = '0') then
            wait until RD_ARDY_ACCEPT = '1';
            wait for clk_per;
         end if;
         RD_REQ   <= '0';
         
         wait for clk_per;
         
         RD_ADDR    <= "00000" + ((5*i) rem ADDR_WIDTH);
         RD_REQ     <= '1';
         
         wait for clk_per;
         if (RD_ARDY_ACCEPT = '0') then
            wait until RD_ARDY_ACCEPT = '1';
            wait for clk_per;
         end if;
         RD_REQ   <= '0';
         
         RD_ADDR    <= "00000" + ((5*i+1) rem ADDR_WIDTH);
         RD_REQ     <= '1';
         
         wait for clk_per;
         if (RD_ARDY_ACCEPT = '0') then
            wait until RD_ARDY_ACCEPT = '1';
            wait for clk_per;
         end if;
         RD_REQ   <= '0';
         
         RD_ADDR    <= "00000" + ((5*i+2) rem ADDR_WIDTH);
         RD_REQ     <= '1';
         
         wait for clk_per;
         if (RD_ARDY_ACCEPT = '0') then
            wait until RD_ARDY_ACCEPT = '1';
            wait for clk_per;
         end if;
         RD_REQ   <= '0';
         
         wait for ((i rem 3)+1)*clk_per;
      end loop;
      
      -- ----------------------------------------------------------------------
      -- ----------------------------------------------------------------------      
      wait;
   end process; 

end;


 
