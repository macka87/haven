-- combov2_core_const.vhd: Combov2 core constants
-- Copyright (C) 2008 CESNET
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

library IEEE;
use IEEE.std_logic_1164.all;

package combov2_core_const is

   -- FL_WATCH constants ------------------------------------------------------
   constant FL_WATCH0_IFCS          : integer := 2;
   constant FL_WATCH0_CNTR_WIDTH    : integer := 32;
   constant FL_WATCH0_PIPELINE_LEN  : integer := 2;
   constant FL_WATCH0_GUARD         : boolean := true;
   constant FL_WATCH0_RX_HEADER     : boolean := true;
   constant FL_WATCH0_RX_FOOTER     : boolean := false; 
   constant FL_WATCH0_TX_HEADER     : boolean := false;
   constant FL_WATCH0_TX_FOOTER     : boolean := false; 
   -- -------------------------------------------------------------------------
   
   -- Size of IB_SWITCH input buffer (in number of headers), min. 1
   constant IB_SWITCH_HEADER_NUM    : integer := 1;
   
   -- CHIPSCOPE constants -----------------------------------------------------
   -- Synchronize your choice with ../top/combov2/Makefile (USE_CHIPSCOPE)
   constant GENERATE_CHIPSCOPE      : boolean := true;
   -- constant GENERATE_CHIPSCOPE      : boolean := false;
   -- -------------------------------------------------------------------------

end combov2_core_const;

package body combov2_core_const is
end combov2_core_const;


