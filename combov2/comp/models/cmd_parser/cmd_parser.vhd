--
-- CMD_PARSER.vhd: CMD parser for simulation
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use WORK.math_pack.all;
use work.plx_oper.all;
use work.cmd_parser_oper.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity CMD_PARSER is
   port(
      -- Common interface
      RESET             : in  std_logic;
      LCLKF             : in  std_logic;

      -- PLX SIM interface
      OPER              : out t_plx_oper;
      PARAMS            : out t_plx_params;
      STROBE            : out std_logic;
      BUSY              : in  std_logic;
      
      -- CMD_PARSER_INTERFACE
      CMD_ARRAY         : in  t_cmd_parser_ctrl_array;
      CMD_VLD           : in  std_logic;   
      CMD_BUSY          : out std_logic
      );
end entity CMD_PARSER;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture CMD_PARSER_arch of CMD_PARSER is

constant lclkf_per       : time := 20 ns; -- local bus clock

signal plx_ctrl    : t_plx_ctrl;
signal plx_oper    : t_plx_oper := INIT;
signal plx_params  : t_plx_params;   
begin

main : process

-- ----------------------------------------------------------------------------
--                                 Procedures declaration
-- ----------------------------------------------------------------------------
-- Procedure plx_op performs plx operation specified
-- in data structure t_plx_ctrl
--
-- Parameters:
--       ctrl        - structure for plx controling
--       block_wait  - block waiting
--
procedure plx_op(ctrl : in t_plx_ctrl; block_wait : in boolean := false) is
begin
   wait until (LCLKF'event and LCLKF='1' and BUSY = '0');
   wait for 0.1*lclkf_per;
   OPER        <= ctrl.oper;
   PARAMS      <= ctrl.params;
   STROBE      <= '1';

   wait for lclkf_per;
   STROBE      <= '0';

   -- block waiting, if reguired
   if (block_wait) then
      wait until (LCLKF'event and LCLKF='1' and BUSY = '0');
   end if;
end plx_op;

-- ----------------------------------------------------------------
--                        Process Body
-- ----------------------------------------------------------------
begin
CMD_BUSY <= '1';
--wait until (RESET = '0');

plx_op(plx_init, true); -- reset localbus

while true loop
  CMD_BUSY <= '0';
  wait until (CMD_VLD = '1');

  CMD_BUSY <= '1';
  for index in 0 to CMD_ARRAY.COUNT-1 loop
    
    if (CMD_ARRAY.COMMANDS(index).OPER = PLX) then
      plx_op(CMD_ARRAY.COMMANDS(index).PLX_PARAM, true);
    end if;

    if (CMD_ARRAY.COMMANDS(index).OPER = WAITING) then
      wait for CMD_ARRAY.COMMANDS(index).WAIT_PARAM;
    end if;
   
  end loop;  

end loop;  

end process;

end architecture CMD_PARSER_arch;

