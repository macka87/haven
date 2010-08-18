-- phyter_i2c_norec.vhd: Empty architecture of phyter control & status
--                       (no MI32 record)
-- component
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
--            Lukas Solanka <solanka@liberouter.org>
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
-- ------------------------------------------------------------------------
--                      Architecture declaration
-- ------------------------------------------------------------------------
architecture empty of PHYTER_I2C_GENERIC_NOREC is

   signal empty_sig  : std_logic_vector(72+2*IFC_CNT-1 downto 0);

begin
   empty_sig <= CLK     & -- 1
                RESET   & -- 1 = 2
                --
                SCL     & -- IFC_CNT
                SDA     & -- IFC_CNT
                --
                MI32_DWR   & -- 32
                MI32_ADDR  & -- 32
                MI32_RD    & -- 1
                MI32_WR    & -- 1
                MI32_BE;     -- 4 = 70
                -------------------
                -- = 2 + 2*IFC_CNT + 70 = 72 + 2*IFC_CNT

   SCL      <= (others => 'Z');
   SDA      <= (others => 'Z');
   --
   PHDIS    <= (others => 'Z');
   --
   MI32_DRD    <= (others => 'Z');
   MI32_ARDY   <= 'Z';
   MI32_DRDY   <= 'Z';

end architecture empty;
