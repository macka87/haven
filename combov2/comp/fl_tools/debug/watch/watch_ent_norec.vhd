-- watch_ent_norec.vhd: Frame Link watch comp to gather statistics about trafic with no records inside
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--            Jan Stourac <xstour03@stud.fit.vutbr.cz>
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_WATCH_NOREC is
   generic(
      INTERFACES     : integer := 1;  -- At least 1
      CNTR_WIDTH     : integer := 32;
      PIPELINE_LEN   : integer := 1;   -- At least 1
      GUARD          : boolean := true;
      HEADER         : boolean := true;
      FOOTER         : boolean := true;
      SAMPLE         : boolean := false
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      SOF_N          : in std_logic_vector(INTERFACES-1 downto 0);
      EOF_N          : in std_logic_vector(INTERFACES-1 downto 0);
      SOP_N          : in std_logic_vector(INTERFACES-1 downto 0);
      EOP_N          : in std_logic_vector(INTERFACES-1 downto 0);
      DST_RDY_N      : in std_logic_vector(INTERFACES-1 downto 0);
      SRC_RDY_N      : in std_logic_vector(INTERFACES-1 downto 0);

      FRAME_ERR      : out std_logic_vector(INTERFACES-1 downto 0);

      MI_DWR	     : in std_logic_vector(31 downto 0);
      MI_ADDR        : in std_logic_vector(31 downto 0);
      MI_RD	     : in std_logic;
      MI_WR	     : in std_logic;
      MI_BE	     : in std_logic_vector(3 downto 0);
      MI_DRD	     : out std_logic_vector(31 downto 0);
      MI_ARDY	     : out std_logic;
      MI_DRDY	     : out std_logic
   );
end entity FL_WATCH_NOREC;
