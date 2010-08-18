-- check_ent.vhd: Entity of block checking frame properties
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
--            Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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
use work.ibuf_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity CHECK is

   generic(
      -- Number of MAC addresses that can be placed into CAM
      MAC_COUNT         : integer;
      -- Remove FCS from the packet (false -> remove, true -> don't remove)
      INBANDFCS      : boolean := true
   );

   port(
      -- Common signals
      -- Clock sigal
      CLK               : in std_logic;
      -- Asynchronous reset, active in '1'
      RESET             : in std_logic;

      -- Input
      -- Packet data
      DATA_RX        : in std_logic_vector(63 downto 0);
      -- Start of the packet, active in '1'
      SOP_RX         : in std_logic;
      -- End of the packet, active in '1'.
      EOP_RX         : in std_logic;
      -- Position of the end of the packet, valid only if EOP is set to '1'.
      EOP_POS_RX     : in std_logic_vector(2 downto 0);
      -- Error inside the packet was detected, active in '1'.
      ERR_RX         : in std_logic;

      -- Output
      -- Packet data
      DATA_TX        : out std_logic_vector(63 downto 0);
      -- Start of the packet, active in '1'
      SOP_TX         : out std_logic;
      -- End of the packet, active in '1'.
      EOP_TX         : out std_logic;
      -- Position of the end of the packet, valid only if EOP is set to '1'.
      EOP_POS_TX     : out std_logic_vector(2 downto 0);
      -- Error inside the packet was detected, active in '1'.
      ERR_TX         : out std_logic;

      -- Statistics
      STATS          : out t_stats;

      -- CAM connection
      -- MAC address to be searched
      CAM_DI            : out std_logic_vector(63 downto 0);
      -- MAC address search enable
      CAM_MATCH_EN      : out std_logic;
      -- CAM match reset
      CAM_MATCH_RST     : out std_logic;
      -- Addresses found in CAM
      CAM_MATCH_BUS     : in std_logic_vector(MAC_COUNT-1 downto 0);
      -- CAM_MATCH_BUS is valid, active in '1'
      CAM_MATCH_BUS_VLD : in std_logic;

      -- Data from MI_INT
      MI2CHECK          : in t_mi2check;

      -- Sampling unit signals, signals active in '1'
      -- Request for sampling information
      SAU_REQ        : out std_logic;
      -- Accept incoming frame
      SAU_ACCEPT     : in std_logic;
      -- SAU_ACCEPT is valid
      SAU_DV         : in std_logic

   ); 

end entity CHECK;
