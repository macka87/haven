-- sdram_empty.vhd: DDR SDRAM empty component
--
-- Copyright (C) 2006 CESNET
-- Author(s): Tomas Pecenka <pecenka at liberouter.org>
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
use ieee.std_logic_arith.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

entity SDRAM_EMPTY is
port (
      DD             : inout  std_logic_vector(63 downto 0);
      DCB            : inout  std_logic_vector(7 downto 0);
      DBA            : out    std_logic_vector(2 downto 0);
      DQS            : inout  std_logic_vector(17 downto 0);
      DA             : out    std_logic_vector(13 downto 0);
      DCS_N          : out    std_logic_vector(3 downto 0);
      DCLKE          : out    std_logic_vector(1 downto 0);
      DCAS_N         : out    std_logic;
      DRAS_N         : out    std_logic;
      DWE_N          : out    std_logic;
      DCLK           : out    std_logic;
      DCLK_N         : out    std_logic;
      DCLK2          : in     std_logic;
      RESDDR_N       : out    std_logic;
      DSDA           : inout  std_logic;
      DSCLK          : out    std_logic
);
end entity SDRAM_EMPTY;

----------------------------------------------------------------------------
--                      Architecture declaration
----------------------------------------------------------------------------
architecture empty of SDRAM_EMPTY is

   signal empty_sig : std_logic_vector(91 downto 0);

begin
   empty_sig <=  -- DDR SDRAM signals
                 DD             &  --  64
                 DCB            &  --   8
                 DQS            &  --  18
                 DCLK2          &  --   1
                 DSDA;             --   1 = 92 

   DD       <= (others => 'Z');
   DCB      <= (others => 'Z');
   DBA      <= "000";
   DQS      <= (others => 'Z');
   DA       <= (others => '0');
   DCS_N    <= (others => '1');
   DCLKE    <= (others => '0');
   DCAS_N   <= '1';
   DRAS_N   <= '1';
   DWE_N    <= '1';
   DCLK     <= '0';
   DCLK_N   <= '1';
   RESDDR_N <= '0';
   DSDA     <= 'Z';
   DSCLK    <= '0';

end architecture empty;
 


