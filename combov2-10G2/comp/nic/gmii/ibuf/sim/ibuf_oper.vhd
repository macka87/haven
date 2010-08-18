-- ibuf_oper.vhd: IBUF operations package
-- Copyright (C) 2006 CESNET
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
-- TODO:

-- Required procedures: ib_op
-- Required packages: IBUF address package (ibuf_addr_pkg)

-- MACRO START
procedure ibuf_enable(id : in integer) is
   variable IBUFN          : std_logic_vector(31 downto 0);
begin

   -- select IBUF
   case id is
      when 0      => IBUFN := IBUF0;
      when 1      => IBUFN := IBUF1;
      when 2      => IBUFN := IBUF2;
      when others => IBUFN := IBUF3;
   end case;

   SendLocalWrite(IBUFN + IBUF_ENABLE_OFFSET, X"ffffffff", 4, 1, X"0000000000000001", IbCmd);
   
end ibuf_enable;
