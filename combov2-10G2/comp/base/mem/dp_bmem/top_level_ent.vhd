-- top_level_ent.vhd: Top level FPGA design for dp_bmem
-- Copyright (C) 2003 CESNET
-- Author: Rudolf Cejka <cejkar@fit.vutbr.cz>
--         Martinek Tomas <martinek@liberouter.org>
--         Tobola Jiri <tobola@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;

entity fpga is
   port(

      -- FPGA
      LCLKF    : in    std_logic;

      -- PLX interface
      LAD      : inout std_logic_vector(31 downto 0);
      LBE      : inout std_logic_vector(3 downto 0);
      DP       : inout std_logic_vector(3 downto 0);
      DEN      : inout std_logic;
      DTR      : inout std_logic;
      CCS      : inout std_logic;
      LHOLDA   : inout std_logic;
      BREQI    : inout std_logic;
      LFRAME   : inout std_logic;
      ADS      : in    std_logic;
      BLAST    : in    std_logic;
      LWR      : in    std_logic;
      READY    : inout std_logic;
      WAITIO   : inout std_logic;
      LHOLD    : in    std_logic;
      LINT     : inout std_logic;
      LRESET   : in    std_logic;
      USERI    : inout std_logic;
      LSERR    : inout std_logic;
      EOT      : inout std_logic;
      BIGEND   : inout std_logic;
      USERO    : in    std_logic;
      BTERM    : inout std_logic;
      BREQO    : inout std_logic;
      L_ONOFF  : inout std_logic
   );
end entity;

