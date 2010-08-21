-- fl_extract_empty.vhd: Empty architecture of FrameLink Extract
-- component.
-- Copyright (C) 2007 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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

architecture empty of FL_EXTRACT is

TX_DATA<=RX_DATA;
TX_REM<=RX_REM;
TX_SOF_N<=RX_SOF_N;
TX_EOF_N<=RX_EOF_N;
TX_SOP_N<=RX_SOP_N;
TX_EOP_N<=RX_EOP_N;
TX_SRC_RDY_N<=RX_SRC_RDY_N;
RX_DST_RDY_N<=TX_DST_RDY_N;

EXT_DATA<=(others=>'Z');
EXT_DATA_VLD<='Z';

end architecture empty;
