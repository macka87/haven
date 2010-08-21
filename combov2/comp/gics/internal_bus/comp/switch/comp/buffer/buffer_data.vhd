--
-- buffer_data.vhd : IB Switch Data Buffer
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
--               ENTITY DECLARATION -- IB Switch Data Buffer                 -- 
-- ----------------------------------------------------------------------------

entity IB_SWITCH_BUFFER_DATA is 
   generic(
      -- Data Width (1-128)
      DATA_WIDTH   : integer:= 64;
      -- The number of headers to be stored
      HEADER_NUM   : integer:=  1     
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK          : in std_logic;  
      RESET        : in std_logic;  

      -- Input interface ------------------------------------------------------
      IN_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_SOF_N     : in  std_logic;
      IN_EOF_N     : in  std_logic;
      IN_WR        : in  std_logic;
      IN_FULL      : out std_logic;      

      -- Output interface -----------------------------------------------------
      OUT_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_DATA_VLD : out std_logic;
      OUT_SOF_N    : out std_logic;
      OUT_EOF_N    : out std_logic;      
      OUT_RD_VEC   : in  std_logic_vector(2 downto 0)
   );
end IB_SWITCH_BUFFER_DATA;

-- ----------------------------------------------------------------------------
--            ARCHITECTURE DECLARATION  --  IB Switch Data Buffer            --
-- ----------------------------------------------------------------------------

architecture ib_switch_data_buffer_arch of IB_SWITCH_BUFFER_DATA is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal empty : std_logic;
   signal re    : std_logic;
   signal din   : std_logic_vector(DATA_WIDTH-1+2 downto 0);
   signal dout  : std_logic_vector(DATA_WIDTH-1+2 downto 0);

begin

   -- DATA BUFFER -------------------------------------------------------------
   U_ib_switch_data_buffer_sh_fifo: entity work.SH_FIFO
   generic map (
      FIFO_WIDTH     => DATA_WIDTH + 2,
      FIFO_DEPTH     => ib_switch_buffer_data_depth(HEADER_NUM, DATA_WIDTH),
      USE_INREG      => false, 
      USE_OUTREG     => false  
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,
      -- write interface
      DIN            => din,
      WE             => IN_WR,
      FULL           => IN_FULL,
      -- read interface
      DOUT           => dout,
      RE             => re,
      EMPTY          => empty,
      -- status
      STATUS         => open
   );

   -- INPUT logic -------------------------------------------------------------
   din          <= IN_SOF_N&IN_EOF_N&IN_DATA;

   -- OUTPUT logic ------------------------------------------------------------
   OUT_DATA     <= dout(DATA_WIDTH-1 downto 0);
   OUT_SOF_N    <= dout(DATA_WIDTH+1) or empty; 
   OUT_EOF_N    <= dout(DATA_WIDTH) or empty;

   OUT_DATA_VLD <= not empty;

   re           <= OUT_RD_VEC(2) or OUT_RD_VEC(1) or OUT_RD_VEC(0);
   
end ib_switch_data_buffer_arch;

                     

