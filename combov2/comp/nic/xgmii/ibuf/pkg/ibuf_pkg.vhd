-- ibuf_pkg.vhd: Package of records for IBUF components
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
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                         IBUF Stats Package
-- ----------------------------------------------------------------------------
package ibuf_pkg is

   -- Stats record
   -- All items of the record are active in '1'
   type t_stats is record
      MAC_ERR        : std_logic; -- MAC address is not accepted
      MINTU_ERR      : std_logic; -- Frame does not have minimal length
      MTU_ERR        : std_logic; -- Frame is longer than maximal length
      SAU_ERR        : std_logic; -- Discard the frame
      SAU_ERR_VLD    : std_logic; -- SAU_ERR is valid
      CRC_ERR        : std_logic; -- Frame has bad CRC
      -- Frame length (payload, padding, FCS)
      FRAME_LEN      : std_logic_vector(15 downto 0);
   end record;


   -- Record for data from mi_int available to check
   type t_mi2check is record
      MIN_FRAME_LEN  : std_logic_vector(15 downto 0); --minimal length of frame
      MAX_FRAME_LEN  : std_logic_vector(15 downto 0); --maximal length of frame
      -- MAC address checking
      -- 0x0: promiscuous;        0x1: accept only MACs from CAM
      -- 0x2: mode1 + broadcast;  0x3: mode2 + multicast
      MAC_CHECK_MODE : std_logic_vector(1 downto 0);
   end record;


   -- Record for data from mi_int available to buf
   type t_mi2buf is record
      -- IBUF output is enabled, active in '1'
      IBUF_EN     : std_logic;
      -- Specifies which controls will be done
      ERROR_MASK  : std_logic_vector(4 downto 0);
      -- Reset the counters, active in '1'
      CNT_RESET   : std_logic;
   end record;



   -- BUF2MI INTERFACE
   -- Position of status data
   -- PACODAG_OVERFLOW
   constant C_PACODAG_OVF_POS    : integer := 0;
   -- DFIFO_OVERFLOW
   constant C_DFIFO_OVF_POS      : integer := 1;
   -- FRAME_DISCARDED (should be only '0')
   constant C_FR_DISCARDED_POS   : integer := 2;
   -- BUFFER_OVERFLOW (should be only '0')
   constant C_BUFFER_OVF_POS     : integer := 3;
   -- FSM status
   -- 5:4: 00-st_wait, 01-st_frame, 10-st_discard
   constant C_FSM_STATUS_DEBUG_L : integer := 4;
   constant C_FSM_STATUS_DEBUG_H : integer := 5;
   -- HFIFO full
   constant C_HFIFO_FULL_POS     : integer := 6;
   -- HFIFO empty
   constant C_HFIFO_EMPTY_POS    : integer := 7;
   -- DFIFO wr
   constant C_HFIFO_WR_POS       : integer := 8;
   -- DFIFO rd
   constant C_HFIFO_RD_POS       : integer := 9;
   -- DFIFO DO DV
   constant C_HFIFO_DO_DV_POS    : integer := 10;
   -- DFIFO full
   constant C_DFIFO_FULL_POS     : integer := 11;
   -- DFIFO empty
   constant C_DFIFO_EMPTY_POS    : integer := 12;
   -- DFIFO wr
   constant C_DFIFO_WR_POS       : integer := 13;
   -- DFIFO rd
   constant C_DFIFO_RD_POS       : integer := 14;
   -- DFIFO DO DV
   constant C_DFIFO_DO_DV_POS    : integer := 15;
   -- CTRL RDY
   constant C_CTRL_RDY_POS       : integer := 16;

   -- Record for data from buf available to mi_int
   type t_buf2mi is record
      -- Total received frames counter
      TRFC        : std_logic_vector(63 downto 0);
      -- Correct frames counter
      CFC         : std_logic_vector(63 downto 0);
      -- Discarded frames counter
      DFC         : std_logic_vector(63 downto 0);
      -- Counter of frames discarded due to buffer overflow
      BODFC       : std_logic_vector(63 downto 0);
      -- Status data, active in '1', meaning determines constants above
      STATUS      : std_logic_vector(16 downto 0);
   end record;

end ibuf_pkg;


-- ----------------------------------------------------------------------------
--                       IBUF Stats Package body
-- ----------------------------------------------------------------------------
package body ibuf_pkg is

end ibuf_pkg;
