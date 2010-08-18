--
-- cpl_buf.vhd : IB Endpoint Read Controller Completion Buffer
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
--    ENTITY DECLARATION -- IB Endpoint Read Controller Completion Buffer    -- 
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_READ_CTRL_CPL_BUF is 
   generic(
      -- Data Width (1-128)
      DATA_WIDTH    : integer := 64;
      -- The number of items to be stored
      ITEMS         : integer :=  16    
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK           : in  std_logic;  
      RESET         : in  std_logic;  

      -- Input interface ------------------------------------------------------
      IN_DATA       : in  std_logic_vector(DATA_WIDTH-1 downto 0); 
      IN_SRC_RDY    : in  std_logic;       
      IN_DST_RDY    : out std_logic;

      -- Output interface -----------------------------------------------------
      OUT_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0); 
      OUT_SRC_RDY   : out std_logic;       
      OUT_DST_RDY   : in  std_logic
   );
end IB_ENDPOINT_READ_CTRL_CPL_BUF;

-- ----------------------------------------------------------------------------
-- ARCHITECTURE DECLARATION -- IB Endpoint Read Controller Completion Buffer --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_read_ctrl_cpl_buf_arch of IB_ENDPOINT_READ_CTRL_CPL_BUF is

   signal out_src_rdy_n : std_logic;
   signal out_dst_rdy_n : std_logic;
   signal in_src_rdy_n  : std_logic;
   signal in_dst_rdy_n  : std_logic;

begin

   -- -------------------------------------------------------------------------
   --                        IB BUFFER SH (MIN. 2 ITEMS)                     --
   -- -------------------------------------------------------------------------

   U_buf: entity work.IB_BUFFER_SH
   generic map (
      DATA_WIDTH    => DATA_WIDTH,
      ITEMS         => ITEMS
   )
   port map (
      -- Common interface ---------------------------------
      CLK           => CLK,
      RESET         => RESET,

      -- Input interface ----------------------------------
      IN_DATA       => IN_DATA,
      IN_SOF_N      => '0',
      IN_EOF_N      => '0',
      IN_SRC_RDY_N  => in_src_rdy_n,
      IN_DST_RDY_N  => in_dst_rdy_n,

      -- Output interface ---------------------------------
      OUT_DATA      => OUT_DATA,
      OUT_SOF_N     => open,
      OUT_EOF_N     => open,
      OUT_SRC_RDY_N => out_src_rdy_n,
      OUT_DST_RDY_N => out_dst_rdy_n
   ); 

   in_src_rdy_n  <= not IN_SRC_RDY;
   IN_DST_RDY    <= not in_dst_rdy_n;
   
   OUT_SRC_RDY   <= not out_src_rdy_n;
   out_dst_rdy_n <= not OUT_DST_RDY;

end ib_endpoint_read_ctrl_cpl_buf_arch;

                     

