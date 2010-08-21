-- fl_composer_ent.vhd: Composes FL from headers/footers and payload (entity)
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_COMPOSER is

   generic(
      -- Enables frame headers
      CTRL_HDR_EN       : boolean := true;
      -- Enables frame footers
      CTRL_FTR_EN       : boolean := true;
       -- FrameLink width
      FL_WIDTH_TX       : integer := 64;
      -- Put FL Relay to the output
      FL_RELAY          : boolean := false
   );

   port(
      -- Common signals
      -- Clock sigal
      CLK               : in std_logic;
      -- Asynchronous reset, active in '1'
      RESET             : in std_logic;

      -- Signals that can be used for debugging the component
      DEBUG_FIFO_SEL    : out std_logic;

      -- Input
      -- Payload
      -- Data
      RX_DATA        : in std_logic_vector(FL_WIDTH_TX-1 downto 0);
      -- Position of the end of the part, valid only if RX_EOP_N is set to '0'.
      RX_REM         : in std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
      -- Start of the part, active in '0'
      RX_SOP_N       : in std_logic;
      -- End of the packet, active in '0'.
      RX_EOP_N       : in std_logic;
      -- Source is ready, active in '0'
      RX_SRC_RDY_N   : in std_logic;
      -- Destination is ready, active in '0'
      RX_DST_RDY_N   : out std_logic;

      -- Packet headres/footers
      -- Part data
      RX_HDATA       : in std_logic_vector(FL_WIDTH_TX-1 downto 0);
      -- Position of the end of the part, valid only if RX_HEOP_N is set to '0'.
      RX_HREM        : in std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
      -- Start of the part, active in '0'
      RX_HSOP_N      : in std_logic;
      -- End of the packet, active in '0'.
      RX_HEOP_N      : in std_logic;
      -- Source is ready, active in '0'
      RX_HSRC_RDY_N  : in std_logic;
      -- Destination is ready, active in '0'
      RX_HDST_RDY_N  : out std_logic;

 
      -- Output FrameLink
      TX_DATA        : out std_logic_vector(FL_WIDTH_TX-1 downto 0);
      TX_REM         : out std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
      TX_SOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in std_logic

   );

end entity FL_COMPOSER;

