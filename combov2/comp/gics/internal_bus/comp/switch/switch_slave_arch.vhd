--
-- switch_slave_arch.vhd : IB Slave Switch architecture
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
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

library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--              ARCHITECTURE DECLARATION  --  IB Slave Switch                --
-- ----------------------------------------------------------------------------

architecture ib_switch_slave_arch of IB_SWITCH_SLAVE is

   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------
   constant ZEROS : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '0');
  
   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------   

   -- IB pipeline component signals -------------------------------------------
   signal pipe_out_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal pipe_out_sof_n     : std_logic;
   signal pipe_out_eof_n     : std_logic;
   signal pipe_out_src_rdy_n : std_logic;
   signal pipe_out_dst_rdy_n : std_logic;

   -- Buffers signals ---------------------------------------------------------
   signal buf1_DATA          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal buf1_DATA_VLD      : std_logic;
   signal buf1_SOF_N         : std_logic;
   signal buf1_EOF_N         : std_logic;
   signal buf1_RD_VEC        : std_logic_vector(2 downto 0);

   signal buf2_DATA          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal buf2_DATA_VLD      : std_logic;
   signal buf2_SOF_N         : std_logic;
   signal buf2_EOF_N         : std_logic;
   signal buf2_RD_VEC        : std_logic_vector(2 downto 0);

   -- Auxiliary signals -------------------------------------------------------
   signal transfer_en_n      : std_logic;
   signal wr1                : std_logic;
   signal wr2                : std_logic;
   signal req1               : std_logic;
   signal req2               : std_logic;
   signal buf1_RD            : std_logic;
   signal buf2_RD            : std_logic;
                              
begin
   
   -- Asserts -----------------------------------------------------------------
   assert DATA_WIDTH =  8 or DATA_WIDTH = 16 or DATA_WIDTH = 32 or
          DATA_WIDTH = 64 or DATA_WIDTH = 128
      report "DATA_WIDTH must be one of {8,16,32,64,128}."
      severity error;
   
   assert HEADER_NUM > 0
      report "HEADER_NUM must be at least 1."
      severity error;
   
   -- -------------------------------------------------------------------------
   --                             DOWN DIRECTION                             --
   -- ------------------------------------------------------------------------- 

   -- -------------------------------------------------------------------------
   -- IB PIPELINE (including feedback - dst_rdny_n) ---------------------------                                                
   U_ib_pipe: entity work.IB_PIPE
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH     => DATA_WIDTH
   )
   port map (
      -- Common interface -----------------------------------------------------
      CLK            => CLK,
      RESET          => RESET,
      
      -- Input interface ------------------------------------------------------
      IN_DATA        => PORT0_DOWN_DATA, 
      IN_SOF_N       => PORT0_DOWN_SOF_N,    
      IN_EOF_N       => PORT0_DOWN_EOF_N, 
      IN_SRC_RDY_N   => PORT0_DOWN_SRC_RDY_N,
      IN_DST_RDY_N   => PORT0_DOWN_DST_RDY_N,
 
      -- Output interface -----------------------------------------------------
      OUT_DATA       => pipe_out_data,     
      OUT_SOF_N      => pipe_out_sof_n,    
      OUT_EOF_N      => pipe_out_eof_n,    
      OUT_SRC_RDY_N  => pipe_out_src_rdy_n,
      OUT_DST_RDY_N  => pipe_out_dst_rdy_n
   );
   
   -- -------------------------------------------------------------------------
   -- OUTPUT interface --------------------------------------------------------
   PORT1_DOWN_DATA      <= pipe_out_data;     
   PORT1_DOWN_SOF_N     <= pipe_out_sof_n or transfer_en_n;    
   PORT1_DOWN_EOF_N     <= pipe_out_eof_n or transfer_en_n;    
   PORT1_DOWN_SRC_RDY_N <= pipe_out_src_rdy_n or transfer_en_n;

   PORT2_DOWN_DATA      <= pipe_out_data;     
   PORT2_DOWN_SOF_N     <= pipe_out_sof_n or transfer_en_n;    
   PORT2_DOWN_EOF_N     <= pipe_out_eof_n or transfer_en_n;    
   PORT2_DOWN_SRC_RDY_N <= pipe_out_src_rdy_n or transfer_en_n;

   pipe_out_dst_rdy_n   <= transfer_en_n;
   
   transfer_en_n        <= PORT1_DOWN_DST_RDY_N or PORT2_DOWN_DST_RDY_N;
   
   -- -------------------------------------------------------------------------
   --                              UP DIRECTION                              --
   -- -------------------------------------------------------------------------   

   -- -------------------------------------------------------------------------   
   -- Data Buffer #1 ----------------------------------------------------------

   U_ib_switch_data_buffer1: entity work.IB_SWITCH_BUFFER_DATA  
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH   => DATA_WIDTH,
      -- The number of headers to be stored
      HEADER_NUM   => HEADER_NUM
   )
   port map(
      -- Common interface ---------------------------------
      CLK          => CLK,
      RESET        => RESET,

      -- Input interface ----------------------------------
      IN_DATA      => PORT1_UP_DATA,     
      IN_SOF_N     => PORT1_UP_SOF_N,    
      IN_EOF_N     => PORT1_UP_EOF_N,    
      IN_WR        => wr1,
      IN_FULL      => PORT1_UP_DST_RDY_N,
                   
      -- Output interface ---------------------------------
      OUT_DATA     => buf1_DATA,    
      OUT_DATA_VLD => buf1_DATA_VLD,
      OUT_SOF_N    => buf1_SOF_N,   
      OUT_EOF_N    => buf1_EOF_N,   
      OUT_RD_VEC   => buf1_RD_VEC
   );      

   wr1 <= not PORT1_UP_SRC_RDY_N;

   -- -------------------------------------------------------------------------   
   -- Data Buffer #2 ----------------------------------------------------------

   U_ib_switch_data_buffer2: entity work.IB_SWITCH_BUFFER_DATA  
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH   => DATA_WIDTH,
      -- The number of headers to be stored
      HEADER_NUM   => HEADER_NUM
   )
   port map(
      -- Common interface ---------------------------------
      CLK          => CLK,
      RESET        => RESET,

      -- Input interface ----------------------------------
      IN_DATA      => PORT2_UP_DATA,     
      IN_SOF_N     => PORT2_UP_SOF_N,    
      IN_EOF_N     => PORT2_UP_EOF_N,    
      IN_WR        => wr2,
      IN_FULL      => PORT2_UP_DST_RDY_N,
                   
      -- Output interface ---------------------------------
      OUT_DATA     => buf2_DATA,    
      OUT_DATA_VLD => buf2_DATA_VLD,
      OUT_SOF_N    => buf2_SOF_N,   
      OUT_EOF_N    => buf2_EOF_N,   
      OUT_RD_VEC   => buf2_RD_VEC
   );      

   wr2 <= not PORT2_UP_SRC_RDY_N;   

   -- -------------------------------------------------------------------------   
   -- Output Port Logic -------------------------------------------------------

   U_ib_switch_output_port0: entity work.IB_SWITCH_OUTPUT_PORT
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH     => DATA_WIDTH,
      -- Port number (0/1/2)
      PORT_NUM       => 0
   ) 
   port map (
      -- Common interface ----------------------------------
      CLK            => CLK,  
      RESET          => RESET,

      -- Upstream Port #0 ----------------------------------
      IN0_DATA       => ZEROS,    
      IN0_DATA_VLD   => '0',
      IN0_SOF_N      => '1',   
      IN0_EOF_N      => '1',   
      IN0_RD         => open,      
                     
      IN0_REQ        => '0',
      IN0_ACK        => open,

      -- Downstream Port #1 --------------------------------
      IN1_DATA       => buf1_DATA,     
      IN1_DATA_VLD   => buf1_DATA_VLD, 
      IN1_SOF_N      => buf1_SOF_N,    
      IN1_EOF_N      => buf1_EOF_N,    
      IN1_RD         => buf1_RD,
                     
      IN1_REQ        => req1,
      IN1_ACK        => open,
 
      -- Downstream Port #2 --------------------------------
      IN2_DATA       => buf2_DATA,      
      IN2_DATA_VLD   => buf2_DATA_VLD,  
      IN2_SOF_N      => buf2_SOF_N,     
      IN2_EOF_N      => buf2_EOF_N,     
      IN2_RD         => buf2_RD, 
                                                
      IN2_REQ        => req2, 
      IN2_ACK        => open, 

      -- OUTPUT Port ---------------------------------------
      OUT_DATA       => PORT0_UP_DATA,      
      OUT_SOF_N      => PORT0_UP_SOF_N,     
      OUT_EOF_N      => PORT0_UP_EOF_N,     
      OUT_SRC_RDY_N  => PORT0_UP_SRC_RDY_N, 
      OUT_DST_RDY_N  => PORT0_UP_DST_RDY_N 
   );    

   req1 <= buf1_DATA_VLD and not buf1_SOF_N;    
   req2 <= buf2_DATA_VLD and not buf2_SOF_N;

   buf1_RD_VEC <= '0'&'0'&buf1_RD;
   buf2_RD_VEC <= '0'&'0'&buf2_RD;

end ib_switch_slave_arch;                   



