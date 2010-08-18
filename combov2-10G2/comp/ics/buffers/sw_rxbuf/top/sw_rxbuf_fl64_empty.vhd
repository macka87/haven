-- sw_rxbuf_fl64_empty.vhd: Empty SW RXBuffer cover for 1 SW_RXBUF
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
architecture empty of sw_rxbuf_fl64 is
   -- ------------------ Signals declaration ----------------------------------
   signal empty_sig      : std_logic_vector(141 - 1 downto 0);
begin
   empty_sig <= CLK              & -- 1
                RESET            & -- 1
                RD.ADDR          & -- 32
                RD.BE            & -- 8
                RD.REQ           & -- 1
                RD.SOF_IN        & -- 1
                RD.EOF_IN        & -- 1
                RD.DST_RDY       & -- 1
                RX.SOF_N         & -- 1
                RX.SOP_N         & -- 1
                RX.EOP_N         & -- 1
                RX.EOF_N         & -- 1
                RX.SRC_RDY_N     & -- 1
                RX.DATA          & -- 64
                RX.DREM          & -- 3
                UPS_FL.DST_RDY_N & -- 1
                DNS_FL.DATA      & -- 16
                DNS_FL.SOP_N     & -- 1
                DNS_FL.EOP_N     & -- 1
                DNS_FL.SOF_N     & -- 1
                DNS_FL.EOF_N     & -- 1
                DNS_FL.DREM      & -- 1
                DNS_FL.SRC_RDY_N;  -- 1
                -- ---------------------------------------
                -- 138
                
   -- output signals
   RD.ARDY        <= '0';
   RD.DATA        <= (others => '0');
   RD.SRC_RDY     <= '0';
   RX.DST_RDY_N   <= '0';
   UPS_FL.DATA    <= (others => '0');
   UPS_FL.DREM    <= (others => '1');
   UPS_FL.SOP_N   <= '0';
   UPS_FL.EOP_N   <= '0';
   UPS_FL.SOF_N   <= '0';
   UPS_FL.EOF_N   <= '0';
   UPS_FL.SRC_RDY_N <= '0';
   DNS_FL.DST_RDY_N <= '1';

end architecture empty; 

