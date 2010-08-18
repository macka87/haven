-- fl_guard.vhd: Component for detecting invalid Frame Link frames
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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

-- library containing log2 and min functions
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_GUARD is
   generic(
      HEADER         : boolean := true;
      FOOTER         : boolean := true
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      SOF_N          : in std_logic;
      EOF_N          : in std_logic;
      SOP_N          : in std_logic;
      EOP_N          : in std_logic;
      DST_RDY_N      : in std_logic;
      SRC_RDY_N      : in std_logic;      

      INVALID        : out std_logic
 );
end entity FL_GUARD;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture full of FL_GUARD is

signal reg_eof_n  : std_logic;
signal reg_eop_n  : std_logic;

signal reg_was_sof: std_logic;
signal reg_fend   : std_logic;

signal part1      : std_logic;
signal part2      : std_logic;
signal part3      : std_logic;

signal invld      : std_logic;
signal reg_invld  : std_logic;

begin

-- Register EOF_N to get desired SOF_N
reg_eof_n_p : process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         reg_eof_n <= '0';
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' then
         reg_eof_n <= EOF_N;
      end if;
   end if;
end process;

-- Register EOP_N to get desired SOP_N
reg_eop_n_p : process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         reg_eop_n <= '0';
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' then
         reg_eop_n <= EOP_N;
      end if;
   end if;
end process;

-- Set to 1 when SOF_N is active, set to 0 when EOF_N is active.
reg_was_sof_p : process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         reg_was_sof <= '0';
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' then
         if EOF_N = '0' then
            reg_was_sof <= '0';
         elsif SOF_N = '0' then
            reg_was_sof <= '1';
         end if;
      end if;
   end if;
end process;

-- Used to determine end of frame more exactly. (In situation when 
-- protocol is violated, it can be difficult)
reg_fend_p : process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         reg_fend <= '0';
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' and (EOF_N = '0' or
         (SOF_N = '0' and reg_was_sof = '1')) then
         reg_fend <= '1';
      else
         reg_fend <= '0';
      end if;
   end if;
end process;

-- Set this register to 1 when firt frame part starts, set to 0 when frame ends
part1_p : process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         part1 <= '0';
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' and
         EOF_N = '0' then -- EOF has greater priority than SOF - with shortest
         part1 <= '0';    -- frames, this register will stay at 0
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' and SOF_N = '0' then
         part1 <= '1';
      end if;
   end if;
end process;

-- Set this register to 1 when second frame part starts,set to 0 when frame ends
part2_p : process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         part2 <= '0';
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' and 
         EOF_N = '0' then 
         part2 <= '0';   
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' and SOP_N = '0' and
         part1 = '1' then
         part2 <= '1';
      end if;
   end if;
end process;

-- Set this register to 1 when third frame part starts,set to 0 when frame ends
part3_p : process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         part3 <= '0';
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' and 
         EOF_N = '0' then 
         part3 <= '0';   
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' and SOP_N = '0' and
         part2 = '1' then
         part3 <= '1';
      end if;
   end if;
end process;

detect_invld : process(SOF_N, EOF_N, SOP_N, EOP_N, DST_RDY_N, SRC_RDY_N,
                       part1, part2, part3, reg_eof_n, reg_eop_n)
begin
   invld <= '0';

   if SRC_RDY_N = '0' and DST_RDY_N = '0' then  -- Transfer valid

      if reg_eof_n /= SOF_N then
         invld <= '1';  -- SOF must come immediately after EOF
      end if;

      if reg_eop_n /= SOP_N then
         invld <= '1';  -- SOP must come immediately after EOP
      end if;

      if SOF_N = '0' and SOP_N = '1' then
         invld <= '1';  -- With every SOF, SOP must also come
      end if;
      
      if EOF_N = '0' and EOP_N = '1' then
         invld <= '1';  -- With every EOF, EOP must also come
      end if;
      
      if HEADER = false and FOOTER = false then -- All frames must have 1 part
         if SOF_N = '1' and SOP_N = '0' then
            invld <= '1'; -- SOP not together with SOF means next part.
         end if;
      end if;

      if (HEADER = false and FOOTER = true) or
         (HEADER = true and FOOTER = false) then -- All frames must have 2 parts
         if part2 = '1' and SOP_N = '0' then
            invld <= '1'; -- SOP, but the second part has already started
         end if;

         if EOF_N = '0' and 
            ((part2 = '0' and SOP_N = '1') or part1 = '0') then
            invld <= '1'; -- Frame had only one part
         end if;
      end if;

      if HEADER = true and FOOTER = true then -- All frames must have 3 parts
         if part3 = '1' and SOP_N = '0' then
            invld <= '1'; -- SOP, but the third part has already started
         end if;

         if EOF_N = '0' and 
            ((part3 = '0' and SOP_N = '1') or part2 = '0') then
            invld <= '1'; -- Frame had only one or two parts
         end if;
      end if;

   end if;
end process;

-- register invld
reg_invld_p : process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         reg_invld <= '0';
      elsif reg_fend = '1' then
         reg_invld <= '0';
      elsif invld = '1' then
         reg_invld <= '1';
      end if;
   end if;
end process;

INVALID <= reg_invld when reg_fend = '1' else
           '0';

end architecture full;
