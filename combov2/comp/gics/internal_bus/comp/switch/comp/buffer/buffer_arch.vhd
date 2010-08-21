--
-- buffer_arch.vhd : IB Switch Buffer architecture
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

use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 
use work.ib_switch_pkg.all;

-- ----------------------------------------------------------------------------
--              ARCHITECTURE DECLARATION  --  IB Switch Buffer               --
-- ----------------------------------------------------------------------------

architecture ib_switch_buffer_arch of IB_SWITCH_BUFFER is
  
   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------   

   -- PORT 0 ------------------------------------------------------------------
   signal OUT0_REQ_VEC_aux  : std_logic_vector(2 downto 0);
   signal OUT0_DATA_VLD_aux : std_logic;
   signal OUT0_SOF_N_aux    : std_logic;

   -- PORT 1 ------------------------------------------------------------------
   signal OUT1_REQ_VEC_aux : std_logic_vector(2 downto 0);   
   signal OUT1_DATA_VLD_aux : std_logic;
   signal OUT1_SOF_N_aux    : std_logic;   

   -- PORT 2 ------------------------------------------------------------------   
   signal OUT2_REQ_VEC_aux : std_logic_vector(2 downto 0);   
   signal OUT2_DATA_VLD_aux : std_logic;
   signal OUT2_SOF_N_aux    : std_logic;   
 
begin

   -- -------------------------------------------------------------------------
   --                                PORT 0                                  --
   -- -------------------------------------------------------------------------

   -- REQUEST BUFFER ----------------------------------------------------------
   U_ib_switch_request_buffer0: entity work.IB_SWITCH_BUFFER_REQUEST
   generic map(
      -- Data Width (1-128)
      DATA_WIDTH   => DATA_WIDTH,
      -- The number of headers to be stored
      HEADER_NUM   => HEADER_NUM
   ) 
   port map (
      -- Common interface -----------------------------------------------------
      CLK          => CLK,
      RESET        => RESET,

      -- Input interface ------------------------------------------------------
      IN_REQ_VEC   => IN0_REQ_VEC,
      IN_REQ_WE    => IN0_REQ_WE, 
      
      -- Output interface -----------------------------------------------------
      OUT_REQ_VEC  => OUT0_REQ_VEC_aux,
      OUT_ACK_VEC  => OUT0_ACK_VEC
   );

   OUT0_REQ_VEC <= (OUT0_REQ_VEC_aux(2) and OUT0_DATA_VLD_aux and not OUT0_SOF_N_aux) &
                   (OUT0_REQ_VEC_aux(1) and OUT0_DATA_VLD_aux and not OUT0_SOF_N_aux) &
                   (OUT0_REQ_VEC_aux(0) and OUT0_DATA_VLD_aux and not OUT0_SOF_N_aux) ;

   -- DATA BUFFER -------------------------------------------------------------
   U_ib_switch_data_buffer0: entity work.IB_SWITCH_BUFFER_DATA  
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH   => DATA_WIDTH,
      -- The number of headers to be stored
      HEADER_NUM   => HEADER_NUM
   )
   port map(
      -- Common interface -----------------------------------------------------
      CLK          => CLK,
      RESET        => RESET,

      -- Input interface ------------------------------------------------------
      IN_DATA      => IN0_DATA, 
      IN_SOF_N     => IN0_SOF_N,
      IN_EOF_N     => IN0_EOF_N,
      IN_WR        => IN0_WR,   
      IN_FULL      => IN0_FULL, 
                   
      -- Output interface -----------------------------------------------------
      OUT_DATA     => OUT0_DATA,    
      OUT_DATA_VLD => OUT0_DATA_VLD_aux,
      OUT_SOF_N    => OUT0_SOF_N_aux,   
      OUT_EOF_N    => OUT0_EOF_N,   
      OUT_RD_VEC   => OUT0_RD_VEC
   );              

   OUT0_DATA_VLD  <= OUT0_DATA_VLD_aux;
   OUT0_SOF_N     <= OUT0_SOF_N_aux;

   -- -------------------------------------------------------------------------
   --                                PORT 1                                  --
   -- -------------------------------------------------------------------------

   -- REQUEST BUFFER ----------------------------------------------------------
   U_ib_switch_request_buffer1: entity work.IB_SWITCH_BUFFER_REQUEST
   generic map(
      -- Data Width (1-128)
      DATA_WIDTH   => DATA_WIDTH,
      -- The number of headers to be stored
      HEADER_NUM   => HEADER_NUM
   ) 
   port map (
      -- Common interface -----------------------------------------------------
      CLK          => CLK,
      RESET        => RESET,

      -- Input interface ------------------------------------------------------
      IN_REQ_VEC   => IN1_REQ_VEC,
      IN_REQ_WE    => IN1_REQ_WE, 
      
      -- Output interface -----------------------------------------------------
      OUT_REQ_VEC  => OUT1_REQ_VEC_aux,
      OUT_ACK_VEC  => OUT1_ACK_VEC
   );

   OUT1_REQ_VEC <= (OUT1_REQ_VEC_aux(2) and OUT1_DATA_VLD_aux and not OUT1_SOF_N_aux) &
                   (OUT1_REQ_VEC_aux(1) and OUT1_DATA_VLD_aux and not OUT1_SOF_N_aux) &
                   (OUT1_REQ_VEC_aux(0) and OUT1_DATA_VLD_aux and not OUT1_SOF_N_aux) ;   

   -- DATA BUFFER -------------------------------------------------------------
   U_ib_switch_data_buffer1: entity work.IB_SWITCH_BUFFER_DATA  
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH   => DATA_WIDTH,
      -- The number of headers to be stored
      HEADER_NUM   => HEADER_NUM
   )
   port map(
      -- Common interface -----------------------------------------------------
      CLK          => CLK,
      RESET        => RESET,

      -- Input interface ------------------------------------------------------
      IN_DATA      => IN1_DATA, 
      IN_SOF_N     => IN1_SOF_N,
      IN_EOF_N     => IN1_EOF_N,
      IN_WR        => IN1_WR,   
      IN_FULL      => IN1_FULL, 
                   
      -- Output interface -----------------------------------------------------
      OUT_DATA     => OUT1_DATA,    
      OUT_DATA_VLD => OUT1_DATA_VLD_aux,
      OUT_SOF_N    => OUT1_SOF_N_aux,   
      OUT_EOF_N    => OUT1_EOF_N,   
      OUT_RD_VEC   => OUT1_RD_VEC
   ); 

   OUT1_DATA_VLD  <= OUT1_DATA_VLD_aux;
   OUT1_SOF_N     <= OUT1_SOF_N_aux;

   -- -------------------------------------------------------------------------
   --                                PORT 2                                  --
   -- -------------------------------------------------------------------------   

   -- REQUEST BUFFER ----------------------------------------------------------
   U_ib_switch_request_buffer2: entity work.IB_SWITCH_BUFFER_REQUEST
   generic map(
      -- Data Width (1-128)
      DATA_WIDTH   => DATA_WIDTH,
      -- The number of headers to be stored
      HEADER_NUM   => HEADER_NUM
   ) 
   port map (
      -- Common interface -----------------------------------------------------
      CLK          => CLK,
      RESET        => RESET,

      -- Input interface ------------------------------------------------------
      IN_REQ_VEC   => IN2_REQ_VEC,
      IN_REQ_WE    => IN2_REQ_WE, 
      
      -- Output interface -----------------------------------------------------
      OUT_REQ_VEC  => OUT2_REQ_VEC_aux,
      OUT_ACK_VEC  => OUT2_ACK_VEC
   );

   OUT2_REQ_VEC <= (OUT2_REQ_VEC_aux(2) and OUT2_DATA_VLD_aux and not OUT2_SOF_N_aux) &
                   (OUT2_REQ_VEC_aux(1) and OUT2_DATA_VLD_aux and not OUT2_SOF_N_aux) &
                   (OUT2_REQ_VEC_aux(0) and OUT2_DATA_VLD_aux and not OUT2_SOF_N_aux) ;   

   -- DATA BUFFER -------------------------------------------------------------
   U_ib_switch_data_buffer2: entity work.IB_SWITCH_BUFFER_DATA  
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH   => DATA_WIDTH,
      -- The number of headers to be stored
      HEADER_NUM   => HEADER_NUM
   )
   port map(
      -- Common interface -----------------------------------------------------
      CLK          => CLK,
      RESET        => RESET,

      -- Input interface ------------------------------------------------------
      IN_DATA      => IN2_DATA, 
      IN_SOF_N     => IN2_SOF_N,
      IN_EOF_N     => IN2_EOF_N,
      IN_WR        => IN2_WR,   
      IN_FULL      => IN2_FULL, 
                   
      -- Output interface -----------------------------------------------------
      OUT_DATA     => OUT2_DATA,    
      OUT_DATA_VLD => OUT2_DATA_VLD_aux,
      OUT_SOF_N    => OUT2_SOF_N_aux,   
      OUT_EOF_N    => OUT2_EOF_N,   
      OUT_RD_VEC   => OUT2_RD_VEC
   ); 

   OUT2_DATA_VLD  <= OUT2_DATA_VLD_aux;
   OUT2_SOF_N     <= OUT2_SOF_N_aux;   

end ib_switch_buffer_arch;   



