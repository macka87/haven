-- testbench.vhd: Testbench of top level entity
-- Copyright (C) 2003 CESNET
-- Author(s): Belohlavek Jiri <belohlavek@liberouter.org>
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
-- TODO:
--
--
library ieee;
use ieee.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is
   -- 100MHz clock
   constant clkper : time := 10 ns;
   -- 50MHz clock
   constant clk_dv_per : time := 20 ns;

   signal reset : boolean := true;
   signal delay : boolean := true;

   -- Clocks and Reset
   signal CMCLK  : std_logic; -- Master Clock
   signal CPHASE : std_logic; -- Phase
   signal CRST   : std_logic; -- Reset

   -- CMD and DQ bus
   signal COP  : std_logic_vector(8 downto 0);  -- CMD Bus
   signal COPV : std_logic;                     -- CMD Valid
   signal CD   : std_logic_vector(67 downto 0); -- Address/Data Bus

   signal CACK : std_logic; -- Read Acknowledge
   signal CEOT : std_logic; -- End of Transfer
   signal CMF  : std_logic; -- Search Successful Flag
   signal CMV  : std_logic; -- Search Successful Plag Valid

   -- SRAM Interface
   signal CAD  : std_logic_vector(21 downto 0); -- SRAM Address
   signal CCE  : std_logic; -- SRAM Chip Enable
   signal CWE  : std_logic; -- SRAM Write Enable
   signal COE  : std_logic; -- SRAM Output Enable
   signal CALE : std_logic; -- Address Latch Enable

   -- only for backward compability
   signal CSEN : std_logic_vector(3 downto 0); -- CAM search enable
   signal CMM  : std_logic; -- CAM multi match flag
   signal CFF  : std_logic; -- CAM full flag
-- signal CSCLK :  std_logic;  -- CAM SRAM clock?, TCAM haven't

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

-- ----------------------------------------------------
-- UUT mapping

-- ----------------------------------------------------
-- CAM Simulation component
CAM_SIM_U : entity work.tcam_sim
generic map(
   cam_mask =>"cam_mask.txt",
   cam_data =>"cam_data.txt",
   cam_clk_per => 40 ns
)

port map( -- TCAM_CTRL -> TCAM
   -- Clocks and Reset
   CMCLK   => CMCLK,-- Master Clock
   CPHASE  => CPHASE,-- Phase
   CRST    => CRST,-- Reset

   -- CMD and DQ bus
   COP   => COP,    -- CMD Bus
   COPV  => COPV,                       -- CMD Valid
   CD    => CD,-- Address/Data Bus

   CACK  => CACK,-- Read Acknowledge
   CEOT  => CEOT,-- End of Transfer
   CMF   => CMF,-- Search Successful Flag
   CMV   => CMV,-- Search Successful Plag Valid

   -- SRAM Interface
   CAD   => CAD,-- SRAM Address
   CCE   => CCE,-- SRAM Chip Enable
   CWE   => CWE,-- SRAM Write Enable
   COE   => COE,-- SRAM Output Enable
   CALE  => CALE,-- Address Latch Enable

   -- only for backward compability
   CSEN   => CSEN,-- CAM search enable
   CMM    => CMM,-- CAM multi match flag
   CFF    => CFF -- CAM full flag
-- CSCLK :  std_logic;  -- CAM SRAM clock?, TCAM haven't

);
-- ----------------------------------------------------
-- CLK clock generator
clkgen : process
begin
   cmclk <= '1';
   wait for clkper/2;
   cmclk <= '0';
   wait for clkper/2;
end process;

-- CLK_DV clock generator
clkgen_dv : process
begin
   if delay then
      wait for 1 ns;
      delay <= false;
   end if;
   cphase <= '1';
   wait for clk_dv_per/2;
   cphase <= '0';
   wait for clk_dv_per/2;
end process;
-- ----------------------------------------------------------------------------
--                         Main testbench process 
-- ----------------------------------------------------------------------------

tb : process
begin
   -- reset tcam
   if reset then
      CRST <= '1';
      wait for clkper;
      CRST <= '0';
      wait for clkper;
      CRST <= '1';
      reset <= false;
   end if;

   wait for 100*clkper;

   -- single-location read cycle
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait for 1 ns;
   copv <= '1';
   cop  <= "000000000"; -- read cop[1:0]=00
   cd   <= X"00000000000180039"; -- read from internal register INFO
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait for 2 ns;
   copv <= '0';
   cop  <= (others => '0');
   cd   <= (others => 'Z');
 
   wait for 100*clkper;

   -- single write cycle  => preparation burst read
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait for 1 ns;
   copv <= '1';
   cop  <= "000000001"; -- write cop[1:0]=01
   cd   <= X"0000000000018003A"; -- write to internal register RBURREG 58
   -- don't distinquished cycle A or B => GMR index=0   
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait for 2 ns;
   copv <= '0';
   cop  <= (others => '0');
   -- RBURGEG ADR[14:0], BLEN[27:19]
   -- .... 0000 0010 0000 0000 0000 0000 0000
   -- 67   27   23   19   15   11   7    3  0
   cd   <= X"00000000000200000"; -- write data ADR=0, BLEN='100'=4
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait for 5 ns;
   cd   <= (others => 'Z');
 
   wait for 100*clkper;

   -- burst read of the data and mask arrays (BLEN=4)
   -- 1 cycle
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait for 1 ns;
   copv <= '1';
   cop  <= "000000100"; -- burst read cop[2:0]=100
   -- cd [20:19] read from data[00]/mask[01]
   cd   <= X"00000000000000000"; -- read from data[00]
   -- 2 cycle
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait for 2 ns;
   copv <= '0';
   cop  <= (others => '0');
   cd   <= (others => 'Z');
   -- 3 cycle
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   cd   <= (others => 'Z');

   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   
   wait for 100*clkper;


   -- single write cycle => preparation burst write
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait for 1 ns;
   copv <= '1';
   cop  <= "000000001"; -- write cop[1:0]=01
   cd   <= X"0000000000018003B"; -- write to internal register WBURREG 59
   -- don't distinquished cycle A or B => GMR index=0   
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait for 2 ns;
   copv <= '0';
   cop  <= (others => '0');
   -- WBURGEG ADR[14:0], BLEN[27:19]
   -- .... 0000 0010 0000 0000 0000 0000 0000
   -- 67   27   23   19   15   11   7    3  0
   cd   <= X"00000000000200000"; -- write data ADR=0, BLEN='100'=4
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait for 5 ns;
   cd   <= (others => 'Z');
 
   wait for 100*clkper;

   -- burst write to the data and mask arrays (BLEN=4)
   -- 1 cycle
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait for 1 ns;
   copv <= '1';
   cop  <= "000000101"; -- burst write cop[2:0]=101
   -- cd [20:19] write to data[00]/mask[01]
   cd   <= X"00000000000000000"; -- write to data[00]
   -- 2 cycle
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait until (cmclk'event AND cmclk = '0' AND cphase = '1');
   copv <= '0';
   cop  <= (others => '0');
   cd   <= X"99999999999999999";
   -- 3 cycle
   wait until (cmclk'event AND cmclk = '0' AND cphase = '1');
   cd   <= X"11111111111111111";
   -- 4 cycle
   wait until (cmclk'event AND cmclk = '0' AND cphase = '1');
   cd   <= X"22222222222222222";
   -- 5 cycle
   wait until (cmclk'event AND cmclk = '0' AND cphase = '1');
   cd   <= X"33333333333333333";
   -- 6 cycle
   wait until (cmclk'event AND cmclk = '0' AND cphase = '1');
   cd <= (others => 'X');
   -- 7 cycle
   wait until (cmclk'event AND cmclk = '0' AND cphase = '1');
   cd <= (others => 'Z');
   wait until (cmclk'event AND cmclk = '0' AND cphase = '1');

   wait for 100*clkper;

   -- learn Timing Diagram of Learn (TLSZ = 00)
   -- 1 cycle
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   copv <= '1';
   cop  <= "001000011"; -- sadr[8:7], mode 136b[6], comparand reg. index[5:2], learn[1:0]
   --cd   <= (others => 'X');
   -- 2 cycle
   wait until (cphase'event AND cphase = '1' AND cmclk = '1');
   wait until (cphase'event AND cphase = '1' AND cmclk = '1');
   copv <= '0';

   wait for clkper;

   -- learn Timing Diagram of Learn (TLSZ = 00)
   -- 1 cycle
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   copv <= '1';
   cop  <= "001000011"; -- sadr[8:7], mode 136b[6], comparand reg. index[5:2], learn[1:0]
   --cd   <= (others => 'X');
   -- 2 cycle
   wait until (cphase'event AND cphase = '1' AND cmclk = '1');
   wait until (cphase'event AND cphase = '1' AND cmclk = '1');
   copv <= '0';

   wait for 100*clkper;

   -- Timing for 272-bit Search (One Device) HLAT=001, LRAM=1, LDEV=1, CFG=10101010
   -- cycle A
   wait until (cphase'event AND cphase = '1' AND cmclk = '1');
   copv <= '1';
   cop  <= "000000110"; -- [5:3]GMR pair 271:136, [2]='1' 272b, [1:0]="10" search
   cd <= X"11111111111111111"; -- cd 271:204
   -- cycle B
   wait until (cmclk'event AND cmclk = '1' AND cphase = '1');
   wait until (cmclk'event AND cmclk = '0' AND cphase = '0');
   copv <= '1';
   cop(1 downto 0)  <= "10"; -- [1:0]="10" search
   cd <= X"22222222222222222"; -- cd 203:136   
   -- cycle C
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait until (cmclk'event AND cmclk = '0' AND cphase = '1');
   copv <= '1';
   cop  <= "000000010"; -- [8:7] SADR[21:20], [5:3]GMR pair 135:0, [2]='0' 272b, [1:0]="10" search
   cd <= X"33333333333333333"; -- cd 135:68  
   -- cycle D
   wait until (cmclk'event AND cmclk = '1' AND cphase = '1');
   wait until (cmclk'event AND cmclk = '0' AND cphase = '0');
   copv <= '1';
   cop  <= "000000010"; -- [8:6] SRR index, [1:0]="10" search
   cd <= X"44444444444444444"; -- cd 67:0
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait until (cmclk'event AND cmclk = '0' AND cphase = '1');
   copv <= '0';   
   cd <= (others => 'Z');
   
--   wait for clkper;
  
   -- Timing for 272-bit Search (One Device) HLAT=001, LRAM=1, LDEV=1, CFG=10101010
   -- cycle A
   --wait until (cphase'event AND cphase = '1' AND cmclk = '1');
   copv <= '1';
   cop  <= "000000110"; -- [5:3]GMR pair 271:136, [2]='1' 272b, [1:0]="10" search
   cd <= X"11111111111111111"; -- cd 271:204
   -- cycle B
   wait until (cmclk'event AND cmclk = '1' AND cphase = '1');
   wait until (cmclk'event AND cmclk = '0' AND cphase = '0');
   copv <= '1';
   cop(1 downto 0)  <= "10"; -- [1:0]="10" search
   cd <= X"22222222222222222"; -- cd 203:136   
   -- cycle C
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait until (cmclk'event AND cmclk = '0' AND cphase = '1');
   copv <= '1';
   cop  <= "000000010"; -- [8:7] SADR[21:20], [5:3]GMR pair 135:0, [2]='0' 272b, [1:0]="10" search
   cd <= X"33333333333333333"; -- cd 135:68  
   -- cycle D
   wait until (cmclk'event AND cmclk = '1' AND cphase = '1');
   wait until (cmclk'event AND cmclk = '0' AND cphase = '0');
   copv <= '1';
   cop  <= "000000010"; -- [8:6] SRR index, [1:0]="10" search
   cd <= X"44444444444444444"; -- cd 67:0
   wait until (cmclk'event AND cmclk = '1' AND cphase = '0');
   wait until (cmclk'event AND cmclk = '0' AND cphase = '1');
   copv <= '0';   
   cd <= (others => 'Z');

wait for 100*clkper;

end process;

-- ----------------------------------------------------------------
end architecture behavioral;


