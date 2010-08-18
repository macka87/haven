-- fl_watch_2.vhd: Frame Link watch comp to gather statistics about traffic
-- Copyright (C) 2010 CESNET
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
entity FL_WATCH_2 is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      SOF_N          : in std_logic_vector(1 downto 0);
      EOF_N          : in std_logic_vector(1 downto 0);
      SOP_N          : in std_logic_vector(1 downto 0);
      EOP_N          : in std_logic_vector(1 downto 0);
      DST_RDY_N      : in std_logic_vector(1 downto 0);
      SRC_RDY_N      : in std_logic_vector(1 downto 0);

      FRAME_ERR      : out std_logic_vector(1 downto 0);

      MI_DWR	      : in std_logic_vector(31 downto 0);
      MI_ADDR        : in std_logic_vector(31 downto 0);
      MI_RD	         : in std_logic;
      MI_WR	         : in std_logic;
      MI_BE	         : in std_logic_vector(3 downto 0);
      MI_DRD         : out std_logic_vector(31 downto 0);
      MI_ARDY        : out std_logic;
      MI_DRDY        : out std_logic
   );
end entity FL_WATCH_2;

architecture full of fl_watch_2 is
begin

   fl_watch_i : entity FL_WATCH_NOREC
   generic map(
      INTERFACES     => 2,  -- At least 1
      CNTR_WIDTH     => 32,
      PIPELINE_LEN   => 2,   -- At least 1
      GUARD          => true,
      HEADER         => false,
      FOOTER         => false
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
                                 
      SOF_N          => SOF_N,
      EOF_N          => EOF_N,
      SOP_N          => SOP_N,
      EOP_N          => EOP_N,
      DST_RDY_N      => DST_RDY_N,
      SRC_RDY_N      => SRC_RDY_N,
                                 
      FRAME_ERR      => FRAME_ERR,
                                 
      MI_DWR	      => MI_DWR,
      MI_ADDR        => MI_ADDR,
      MI_RD	         => MI_RD,
      MI_WR	         => MI_WR,
      MI_BE	         => MI_BE,
      MI_DRD         => MI_DRD,
      MI_ARDY        => MI_ARDY,
      MI_DRDY        => MI_DRDY
   );

end architecture full;
