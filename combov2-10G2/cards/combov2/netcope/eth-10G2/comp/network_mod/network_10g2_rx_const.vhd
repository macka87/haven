-- network_10g2_rx_const.vhd: User constants for 10G2 RX Network Module
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
use work.fifo_pkg.all;

package network_mod_10g2_rx_const is

   -- To change the data width, you must also modify sources!
   constant DATA_WIDTH              : integer := 128;

   constant PACODAG_HEADER_EN       : boolean := true;
   constant PACODAG_FOOTER_EN       : boolean := false;

   -- ADDRESS SPACE -----------------------------------------------------------
   constant IBUF_BASE_ADDR          : std_logic_vector := X"00001000";
   constant IBUF_LIMIT              : std_logic_vector := X"00000400";
   
   -- IBUF constants ----------------------------------------------------------
   -- fifo item - 16 bits
   constant IBUF_DFIFO_BYTES        : integer := 4096; -- Packet data fifo size
   constant IBUF_HFIFO_BYTES        : integer := 1024;  -- Control fifo size

   -- Determines the length of the counter which guards the link for errors
   -- If error dont occur for 2^CNT_ERROR_SIZE cycles the link is declared to
   -- be up
   constant IBUF_CNT_ERROR_SIZE     : integer := 5;

   constant IBUF_MACS               : integer := 16;   -- Number of MAC addresses (up to 16)
   constant IBUF_HFIFO_MEMTYPE      : mem_type := BRAM;
   constant IBUF_FL_RELAY           : boolean := false;
   -- -------------------------------------------------------------------------

   -- LED constants ----------------------------------------------------------
   -- Length of the internal counter, determines period of blinks
   constant LED_CNTR_SIZE           : integer := 27;
   -- -------------------------------------------------------------------------
end network_mod_10g2_rx_const;

package body network_mod_10g2_rx_const is
end network_mod_10g2_rx_const;


