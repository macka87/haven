--
-- fifo_pkg.vhd: Types used in FIFO implementation
-- Copyright (C) 2006 CESNET
-- Author(s): Jan Kastil <xkasti00@stud.fit.vutbr.cz>
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
--
-- TODO:
--
--


library IEEE;
use IEEE.std_logic_1164.all;
package fifo_pkg is
   --type mem_type is (LUT, SRL16, BRAM);
  -- type block_type is (none, fixed_size, variable_size);
  -- type discard_type is (NoDiscard, WriteDiscard, ReadDiscard,WriteReadDiscard);

   subtype mem_type is integer RANGE 0 to 20;
   subtype block_type is integer range 0 to 20;
   subtype discard_type is integer range 0 to 20;

   CONSTANT LUT:integer := 0;
   CONSTANT BRAM:integer := 1;
   CONSTANT SRL16:integer := 2;

   CONSTANT none:integer := 0;
   CONSTANT fixed_size:integer := 1;
   CONSTANT variable_size:integer := 2;

   CONSTANT NoDiscard:integer := 0;
   CONSTANT WriteDiscard:integer := 1;
   CONSTANT ReadDiscard:integer := 2;
   CONSTANT WriteReadDiscard:integer := 3;
end fifo_pkg;

package body fifo_pkg is
end fifo_pkg;
