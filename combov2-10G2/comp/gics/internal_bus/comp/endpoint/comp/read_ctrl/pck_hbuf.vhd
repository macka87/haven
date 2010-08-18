--
-- pck_hbuf.vhd : IB Endpoint Read Controller Packed Header Buffer
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
use work.ib_endpoint_pkg.all;

-- ----------------------------------------------------------------------------
--      ENTITY DECLARATION -- IB Endpoint Read Ctrl Packed Header Buffer     -- 
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_READ_CTRL_PCK_HBUF is 
   generic(
      -- Data Width (1-128)
      DATA_WIDTH    : integer := 64;
      -- The number of items to be stored
      ITEMS         : integer :=  1     
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK           : in  std_logic;  
      RESET         : in  std_logic;  

      -- Input interface ------------------------------------------------------
      IN_DATA       : in  std_logic_vector(DATA_WIDTH-1 downto 0); 
      IN_SOF_N      : in  std_logic;
      IN_EOF_N      : in  std_logic;   
      IN_FULL       : out std_logic;       
      IN_WE         : in  std_logic;

      -- Output interface -----------------------------------------------------
      OUT_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_SOF       : out std_logic;
      OUT_EOF       : out std_logic;
      OUT_DATA_VLD  : out std_logic;
      OUT_RE        : in  std_logic
   );
end IB_ENDPOINT_READ_CTRL_PCK_HBUF;

-- ----------------------------------------------------------------------------
--   ARCHITECTURE DECLARATION -- IB Endpoint Read Ctrl Packed Header Buffer  --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_read_ctrl_pck_hbuf_arch of IB_ENDPOINT_READ_CTRL_PCK_HBUF is

   signal empty : std_logic;
   signal din   : std_logic_vector(DATA_WIDTH+1 downto 0);
   signal dout  : std_logic_vector(DATA_WIDTH+1 downto 0);

begin

   -- -------------------------------------------------------------------------
   --                        SHIFT FIFO (MIN. 2 ITEMS)                       --
   -- -------------------------------------------------------------------------

   U_ib_endpoint_pck_hbuf_sh_fifo: entity work.SH_FIFO
   generic map (
      FIFO_WIDTH     => DATA_WIDTH+2,
      FIFO_DEPTH     => ITEMS,
      USE_INREG      => false, 
      USE_OUTREG     => false  
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,
      -- write interface
      DIN            => din,
      WE             => IN_WE,
      FULL           => IN_FULL,
      -- read interface
      DOUT           => dout,
      RE             => OUT_RE,
      EMPTY          => empty,
      -- status
      STATUS         => open
   );

   din <= IN_SOF_N&IN_EOF_N&IN_DATA;

   OUT_SOF  <= not dout(DATA_WIDTH+1) and not empty;
   OUT_EOF  <= not dout(DATA_WIDTH) and not empty;
   OUT_DATA <= dout(DATA_WIDTH-1 downto 0);

   OUT_DATA_VLD <= not empty;

end ib_endpoint_read_ctrl_pck_hbuf_arch;

                     

