--
-- cynse70064a_top.vhd: CYNSE70064A(CAM) vhdl top level
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Dedek     <dedek@liberouter.org>
--            
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
-- $ID: $
--
-- TODO:
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity TCAM_SIM is

   generic (
      cam_mask    : string;
      cam_data    : string;
      cam_clk_per : time
   );

   port(
      -- Clocks and Reset
      CMCLK  : in std_logic; -- Master Clock
      CPHASE : in std_logic; -- Phase
      CRST   : in std_logic; -- Reset

      -- CMD and DQ bus
      COP  : in std_logic_vector(8 downto 0);     -- CMD Bus
      COPV : in std_logic;                        -- CMD Valid
      CD   : inout std_logic_vector(67 downto 0); -- Address/Data Bus

      CACK : inout std_logic; -- Read Acknowledge
      CEOT : inout std_logic; -- End of Transfer
      CMF  : inout std_logic; -- Search Successful Flag
      CMV  : inout std_logic; -- Search Successful Plag Valid

      -- SRAM Interface
      CAD  : inout std_logic_vector(21 downto 0); -- SRAM Address
      CCE  : inout std_logic; -- SRAM Chip Enable
      CWE  : inout std_logic; -- SRAM Write Enable
      COE  : inout std_logic; -- SRAM Output Enable
      CALE : inout std_logic; -- Address Latch Enable

      -- only for backward compability
      CSEN  : in  std_logic_vector(3 downto 0); -- CAM search enable
      CMM   : out std_logic; -- CAM multi match flag
      CFF   : out std_logic -- CAM full flag
   );
end entity TCAM_SIM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture CYNSE70064A_arch of TCAM_SIM is
  
signal lhi  : std_logic_vector(6 downto 0);
signal bhi  : std_logic_vector(2 downto 0);
signal fuli : std_logic_vector(6 downto 0);
signal id   : std_logic_vector(4 downto 0);


signal full  : std_logic;
signal fulo : std_logic_vector(1 downto 0);
signal lho   : std_logic_vector(1 downto 0);
signal bho   : std_logic_vector(2 downto 0);

begin

CYNSE70064A_U : entity work.CYNSE70064A_top
  generic map (
    data_file => cam_data,
    mask_file => cam_mask
  )
  port map(
    CLK2X => CMCLK,
    PHS_L => CPHASE,
    RST_L => CRST,
    DQ	   => CD,
    CMDV  => COPV,          
    CMD   => COP,         
    LHI   => lhi,
    BHI   => bhi,
    ID    => id,
    FULI  => fuli,

    ACK   => CACK,
    EOT   => CEOT,
    SSV   => CMV,
    SSF   => CMF,
    CE_L  => CCE,
    WE_L  => CWE,
    OE_L  => COE,
    ALE_L => CALE,
    SADR  => CAD,
    FULL  => full,
    FULO  => fulo,
    LHO   => lho,
    BHO   => bho  
  );

--Single device settings
id  <= "00000";
lhi <= "0000000";
bhi <= "000";
fuli <= "1111111";

end architecture CYNSE70064A_arch;




