-- phyter_i2c_empty.vhd: Empty architecture of phyter control & status 
-- component.
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
-- ------------------------------------------------------------------------
--                      Architecture declaration
-- ------------------------------------------------------------------------
architecture empty of PHYTER_I2C is

   signal empty_sig  : std_logic_vector(30 downto 0);

begin
   empty_sig <= CLK     & -- 1
                RESET   & -- 1 = 2
                --
                SCL0    & -- 1
                SDA0    & -- 1
                SCL1    & -- 1
                SDA1    & -- 1
                SCL2    & -- 1
                SDA2    & -- 1
                SCL3    & -- 1
                SDA3    & -- 1 = 8
                --
                LBCLK   & -- 1
                LBFRAME & -- 1
                LBAD    & -- 16
                LBAS    & -- 1
                LBRW    & -- 1
                LBLAST;   -- 1 = 21
                -------------------
                -- = 2 + 8 + 21 = 31

   SCL0     <= 'Z';
   SDA0     <= 'Z';
   SCL1     <= 'Z';
   SDA1     <= 'Z';
   SCL2     <= 'Z';
   SDA2     <= 'Z';
   SCL3     <= 'Z';
   SDA3     <= 'Z';
   --
   PHDISA   <= 'Z';
   PHDISB   <= 'Z';
   PHDISC   <= 'Z';
   PHDISD   <= 'Z';
   --
   LBHOLDA  <= 'Z';
   LBAD     <= (others => 'Z');
   LBRDY    <= 'Z';

end architecture empty;
