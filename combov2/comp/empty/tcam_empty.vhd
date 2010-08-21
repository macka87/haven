--
-- tcam_empty.vhd: TCAM empty entity
--
-- Copyright (C) 2006 CESNET
-- Author(s): Tomas Malek tomalek@liberouter.org
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
-- $ID:$
--
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all; 

-- ----------------------------------------------------------------------------
--                    ENTITY DECLARATION                                     --
-- ---------------------------------------------------------------------------- 

entity TCAM_EMPTY is
   port(
      -- CAM interface
      CD                 : inout std_logic_vector(67 downto 0); -- CAM address/data
      COP                : out   std_logic_vector(8  downto 0); -- CAM instruction 
      COPV               : out   std_logic; -- CAM instruction valid 
      CACK_N             : inout std_logic; -- CAM read acknowledge
      CEOT               : inout std_logic; -- CAM end of burst transfer
      CMF                : in    std_logic; -- CAM match flag
      CMM_N              : in    std_logic; -- CAM multi match flag
      CMV                : in    std_logic; -- CAM match flag valid
      CFF                : in    std_logic; -- CAM full flag
      CPHASE             : out   std_logic; -- CAM phase - half frequency clock
      CRST_N             : out   std_logic; -- CAM reset
      CMCLK              : out   std_logic; -- CAM clock signal
      CSEN_N             : out   std_logic_vector(3 downto 0); -- CAM srch en

      -- CAM Interface - COMBO6X only
      CAD                : in    std_logic_vector(21 downto 0); -- CAM - SRAM address
      CCE_N              : in    std_logic; -- CAM - SRAM chip enable
      CALE_N             : in    std_logic; -- CAM - SRAM address latch enable
      COE_N              : in    std_logic; -- CAM - SRAM output enable
      CWE_N              : in    std_logic; -- CAM - SRAM write enable
      CSCLK              : in    std_logic  -- CAM - SRAM clock 
   );                    
end entity TCAM_EMPTY;


-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture TCAM_EMPTY_arch of TCAM_EMPTY is

   signal empty_sig : std_logic_vector(100 downto 0);

begin
   empty_sig <=   CMF      & --  1
                  CMM_N    & --  1
                  CMV      & --  1
                  CFF      & --  1
                  CAD      & -- 22
                  CCE_N    & --  1
                  CALE_N   & --  1
                  COE_N    & --  1
                  CWE_N    & --  1
                  CSCLK    & --  1
                  CD       & -- 68
                  CACK_N   & --  1
                  CEOT;      --  1
                             --------------
                             --101 = 68+22+11

   -- TCAM interface
   CD      <= (others => 'Z');
   COP     <= (others => '0');
   COPV    <= '0'; 
   CACK_N  <= 'Z';
   CEOT    <= 'Z';
   CPHASE  <= '0';
   CRST_N  <= '1';
   CMCLK   <= '0';
   CSEN_N  <= (others => '1');

end architecture TCAM_EMPTY_arch;  


