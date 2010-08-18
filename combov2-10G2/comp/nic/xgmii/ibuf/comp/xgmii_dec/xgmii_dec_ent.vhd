-- xgmii_dec_ent.vhd: Entity for decoder of aligned SDR XGMII protocol
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

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity XGMII_DEC is
   port(
      -- Common signals
      -- Clock sigal
      CLK               : in std_logic;
      -- Asynchronous reset, active in '1'
      RESET             : in std_logic;

      -- Input Aligned SDR XGMII protocol
      -- Aligned data
      RXD_ALIGNED    : in std_logic_vector(63 downto 0);
      -- Aligned control information
      RXC_ALIGNED    : in std_logic_vector(7 downto 0);
      -- Start of the packet, active in '1'
      SOP_ALIGNED    : in std_logic;

      -- Output
      -- Packet data
      DATA           : out std_logic_vector(63 downto 0);
      -- Start of the packet, active in '1'
      SOP            : out std_logic;
      -- End of the packet, active in '1'.
      EOP            : out std_logic;
      -- Position of the end of the packet, valid only if EOP is set to '1'.
      EOP_POS        : out std_logic_vector(2 downto 0);
      -- Error inside the packet was detected, active in '1'.
      ERR            : out std_logic
   ); 
end entity XGMII_DEC;
