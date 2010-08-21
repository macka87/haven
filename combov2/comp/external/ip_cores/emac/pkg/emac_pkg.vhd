-- emac_pkg.vhd: EMAC layer interface
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
--

library IEEE;
use IEEE.std_logic_1164.all;

package EMAC_PKG is
   -- EMAC Client Receiver Interface
   type t_emac_rx is record
      D                 : std_logic_vector(7 downto 0); -- OUT
      DVLD              : std_logic;                    -- OUT
      GOODFRAME         : std_logic;                    -- OUT
      BADFRAME          : std_logic;                    -- OUT
      FRAMEDROP         : std_logic;                    -- OUT
      STATS             : std_logic_vector(6 downto 0); -- OUT
      STATSVLD          : std_logic;                    -- OUT
      STATSBYTEVLD      : std_logic;                    -- OUT
   end record;

   -- EMAC Client Transmitter Interface
   type t_emac_tx is record
      D                 : std_logic_vector(7 downto 0); -- IN
      DVLD              : std_logic;                    -- IN
      ACK               : std_logic;                    -- OUT
      FIRSTBYTE         : std_logic;                    -- IN
      UNDERRUN          : std_logic;                    -- IN
      COLLISION         : std_logic;                    -- OUT
      RETRANSMIT        : std_logic;                    -- OUT
      IFGDELAY          : std_logic_vector(7 downto 0); -- IN
      SPEEDIS10100      : std_logic;                    -- OUT
      STATS             : std_logic;                    -- OUT
      STATSVLD          : std_logic;                    -- OUT
      STATSBYTEVLD      : std_logic;                    -- OUT
   end record;

   type t_emac_control is record
      -- MAC Control Interface - EMAC0
      PAUSEREQ          : std_logic;                     -- IN
      PAUSEVAL          : std_logic_vector(15 downto 0); -- IN

      --EMAC-MGT link status
      SYNCACQSTATUS     : std_logic;                     -- OUT
      -- EMAC0 Interrupt
      ANINTERRUPT       : std_logic;                     -- OUT
   end record;
   
   -- Generic Host Interface
   type t_emac_host_interface is record
      HOSTCLK           : std_logic;                     -- IN
      HOSTOPCODE        : std_logic_vector(1 downto 0);  -- IN
      HOSTREQ           : std_logic;                     -- IN
      HOSTMIIMSEL       : std_logic;                     -- IN
      HOSTADDR          : std_logic_vector(9 downto 0);  -- IN
      HOSTWRDATA        : std_logic_vector(31 downto 0); -- IN
      HOSTMIIMRDY       : std_logic;                     -- OUT
      HOSTRDDATA        : std_logic_vector(31 downto 0); -- OUT
      HOSTEMAC1SEL      : std_logic;                     -- IN
   end record;
   
end EMAC_PKG;

package body EMAC_PKG is
end EMAC_PKG;

