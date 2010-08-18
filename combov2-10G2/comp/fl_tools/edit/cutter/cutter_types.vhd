-- cutter_types.vhd: FrameLink cutter: Types package
-- (extract and optionally remove data on defined offset in defined frame part)
-- Copyright (C) 2008 CESNET
-- Author(s): Bronislav Pribyl <xpriby12@stud.fit.vutbr.cz>
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
--
-- TODO:
--
-- ------------------------------------------------------------------
--                   Packake Interface
-- ------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

package cutter_types is

   -- variants of auxiliary register enable (according to FSM Main state)
   type t_aux_en       is (en_start, en_progress, en_end, en_after, en_no_reorder);

end cutter_types;

-- ------------------------------------------------------------------
--                     Packake Body
-- ------------------------------------------------------------------
package body cutter_types is
   
end cutter_types;
