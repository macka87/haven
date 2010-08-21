-- uh_fifo.vhd: Unified Header FIFO, full implementation of a single UH FIFO
-- Copyright (C) 2003 CESNET, Liberouter project
-- Author(s): Filip Hofer    <fil@liberouter.org>
--            Tomas Martinek <martinek@liberouter.org>
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
use IEEE.STD_LOGIC_1164.ALL;
-- ----------------------------------------------------------------------
--  Architecture declaration: full
-- ----------------------------------------------------------------------

architecture empty of UH_FIFO is
   signal empty_sig : std_logic_vector(47 downto 0);
begin

empty_sig <=
      RESET         &
      HFE_DOUT      &
      HFE_ADDR      &
      HFE_REQ       &
      HFE_WEN       &
      HFE_CLK       &
      LUP_SR_CLEAN  &
      LUP_ADDR      &
      LUP_CLK       &
      ADC_RD        &
      ADC_ADDR;

      HFE_RDY       <= '0';
      LUP_SR_VALID  <= '0';
      LUP_DATA      <= (others => '0');
      ADC_DO        <= (others => '0');

end empty;
