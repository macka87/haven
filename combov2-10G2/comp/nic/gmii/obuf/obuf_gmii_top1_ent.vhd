-- obuf_gmii_top1_ent.vhd: Output Buffer - obuf + LB entity
-- Copyright (C) 2003 CESNET
-- Author(s): Mikusek Martin <martin.mikusek@liberouter.org>
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
use work.math_pack.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_gmii_top1 is
   generic(
      ADDR_BASE   : integer;
      ADDR_WIDTH  : integer;
      DATA_PATHS  : integer;
      DFIFO_SIZE  : integer;
      SFIFO_SIZE  : integer;
      CTRL_CMD    : boolean
   );
   port(

      -- ---------------- Control signal -----------------
      RESET     : in  std_logic;
      WRCLK     : in  std_logic;
      REFCLK    : in  std_logic;

      -- -------------- Buffer interface -----------------
      DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      SRC_RDY_N  : in std_logic;
      SOF_N      : in std_logic;
      SOP_N      : in std_logic;
      EOF_N      : in std_logic;
      EOP_N      : in std_logic;
      DST_RDY_N  : out std_logic;

      -- -------------- GMII/MII interface ---------------
      TXCLK    : out std_logic;
      TXD      : out std_logic_vector(7 downto 0);
      TXEN     : out std_logic;
      TXER     : out std_logic;

      -- ---------- Internal bus signals ----------------
      LBCLK    : in    std_logic;
      LBFRAME  : in    std_logic;
      LBHOLDA  : out   std_logic;
      LBAD     : inout std_logic_vector(15 downto 0);
      LBAS     : in    std_logic;
      LBRW     : in    std_logic;
      LBRDY    : out   std_logic;
      LBLAST   : in    std_logic
   );
end entity obuf_gmii_top1;
-- ----------------------------------------------------------------------------
