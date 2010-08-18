-- fl2cmd_fl16.vhd: FrameLink to Command protocol transformer
-- Copyright (C) 2006 CESNET
-- Author(s): Jiri Tobola <tobola@liberouter.org>
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
use work.math_pack.all;
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity fl2cmd_fl16 is
   generic(
      -- Header data present
      HEADER      : boolean := true;
      -- Footer data present
      FOOTER      : boolean := false
   ); 
   port(

      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interface
      RX             : inout t_fl16;
      
      -- output interfaces
      CMD_DATA       : out std_logic_vector(15 downto 0);
      CMD_COMMAND    : out std_logic_vector(1 downto 0);
      CMD_SRC_RDY    : out std_logic;
      CMD_DST_RDY    : in  std_logic 

   );
end entity fl2cmd_fl16;

architecture full of fl2cmd_fl16 is
begin

   FL2CMD_I: entity work.FL2CMD

   generic map(
      DATA_WIDTH     => 16,
      HEADER         => HEADER,
      FOOTER         => FOOTER
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- input interface
      FL_SOF_N       => RX.SOF_N,
      FL_SOP_N       => RX.SOP_N,
      FL_EOP_N       => RX.EOP_N,
      FL_EOF_N       => RX.EOF_N,
      FL_SRC_RDY_N   => RX.SRC_RDY_N,
      FL_DST_RDY_N   => RX.DST_RDY_N,
      FL_DATA        => RX.DATA,
      FL_REM         => RX.DREM,
      
      -- output interface
      CMD_DATA       => CMD_DATA,
      CMD_COMMAND    => CMD_COMMAND,
      CMD_SRC_RDY    => CMD_SRC_RDY,
      CMD_DST_RDY    => CMD_DST_RDY
   ); 

end architecture full; 

