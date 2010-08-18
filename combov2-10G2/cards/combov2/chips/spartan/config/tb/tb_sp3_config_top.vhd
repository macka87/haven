--
-- tb_sp3_config_top.vhd: Test bench for sp3_config
-- Copyright (C) 2008  CESNET
-- Author: Milan Malich <malich@mail.muni.cz>
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

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.std_logic_unsigned.all;
USE ieee.numeric_std.ALL;
 
entity tb_sp3_config_top is
end tb_sp3_config_top;
 
architecture behavior of tb_sp3_config_top is
    -- Const
    constant CCLK_period : time := 10 ns;
    
    -- Data flow ( Flash -> Spartan3e -> Virtex 5 )
    
    -- Flash
    component flash_mem is
    port(
      FA           : in  std_logic_vector (25 downto 0);
      FD           : out  std_logic_vector (15 downto 0);
      FWE_N        : in std_logic;
      FCSFLASH_N   : in std_logic;
      FOE_N        : in std_logic;
      FBYTE_N      : in std_logic;
      FRY          : out std_logic
    );
    end component;
    
    -- Spartan3e
    component sp3_config_top
    port(
      CCLK         : in  std_logic;
      RESET_N      : in  std_logic;
      CLED         : out  std_logic_vector(3 downto 0);
      XRCCLK       : out  std_logic;
      XDONE        : in  std_logic;
      XPROGRAM_N   : out  std_logic;
      XM0          : out  std_logic;
      XRRDWR_N     : out  std_logic;
      XRDIN        : out  std_logic;
      XRCS_N       : out  std_logic;
      XRDOUT       : in  std_logic;
      XINIT_N      : in  std_logic;
      XRHSH        : inout  std_logic_vector(11 downto 0);
      XRD          : out  std_logic_vector(7 downto 0);
      FA           : out  std_logic_vector(25 downto 0);
      FD           : in  std_logic_vector(15 downto 0);
      FWE_N        : out  std_logic;
      FCSFLASH_N   : out  std_logic;
      FCSRAM_N     : out std_logic;
      FOE_N        : out  std_logic;
      FBYTE_N      : out  std_logic;
      FRY          : inout  std_logic;
      FLB_N        : out std_logic;     
      FUB_N        : out std_logic;
      FZZ_N        : out std_logic
    );
    end component;
  
    component virtex5
    port(
      XRCCLK       : in std_logic;
      XPROGRAM_N   : in std_logic;
      XM0          : in std_logic;
      XRRDWR_N     : in std_logic;
      XRDIN        : in std_logic;
      XRCS_N       : in std_logic;    
      XRHSH        : inout std_logic_vector(11 downto 0);      
      XDONE        : out std_logic;
      XRDOUT       : out std_logic;
      XINIT_N      : out std_logic;
      XRD          : in std_logic_vector(7 downto 0)
		);
    end component;
    
    -- Control
    signal CCLK : std_logic := '0';
    signal RESET_N : std_logic := '0';
    signal CLED : std_logic_vector(3 downto 0);
    -- Flash <-> Sp3e
    signal FD : std_logic_vector(15 downto 0) := (others=>'0');
    signal FA : std_logic_vector(25 downto 0);
    signal FWE_N : std_logic;
    signal FCSFLASH_N : std_logic;
    signal FCSRAM_N : std_logic;
    signal FOE_N : std_logic;
    signal FBYTE_N : std_logic;
    signal FRY : std_logic;
    signal FLB_N : std_logic;     
    signal FUB_N : std_logic;
    signal FZZ_N : std_logic;
    -- Sp3e <-> Virtex5
    signal XDONE : std_logic := '0';
    signal XRDOUT : std_logic := '0';
    signal XINIT_N : std_logic := '0';
    signal XRDIN : std_logic := '0';
    signal XRHSH : std_logic_vector(11 downto 0) := (others=>'0');
    signal XRCCLK : std_logic;
    signal XPROGRAM_N : std_logic;
    signal XM0 : std_logic;
    signal XRRDWR_N : std_logic;
    signal XRCS_N : std_logic;
    signal XRD : std_logic_vector(7 downto 0) := (others=>'0');
    
BEGIN
 
  INST_CONFIGURATOR_TOP: sp3_config_top 
  port map (
    CCLK => CCLK,
    RESET_N => RESET_N,
    CLED => CLED,
    XRCCLK => XRCCLK,
    XDONE => XDONE,
    XPROGRAM_N => XPROGRAM_N,
    XM0 => XM0,
    XRRDWR_N => XRRDWR_N,
    XRDIN => XRDIN,
    XRCS_N => XRCS_N,
    XRDOUT => XRDOUT,
    XINIT_N => XINIT_N,
    XRHSH => XRHSH,
    XRD => XRD,
    FA => FA,
    FD => FD,
    FWE_N => FWE_N,
    FCSFLASH_N => FCSFLASH_N,
    FCSRAM_N => FCSRAM_N,
    FOE_N => FOE_N,
    FBYTE_N => FBYTE_N,
    FRY => FRY,
    FLB_N => FLB_N,
    FUB_N => FUB_N,
    FZZ_N => FZZ_N
  );
        
  INST_FLASH_MEM: flash_mem
  port map(
		FA => FA,
		FD => FD,
		FWE_N => FWE_N,
		FCSFLASH_N => FCSFLASH_N,
		FOE_N => FOE_N,
		FBYTE_N => FBYTE_N,
		FRY => FRY
	);
  
  
	INST_VIRTEX5: virtex5
  port map(
		XRCCLK => XRCCLK,
		XDONE => XDONE,
		XPROGRAM_N => XPROGRAM_N,
		XM0 => XM0,
		XRRDWR_N => XRRDWR_N,
		XRDIN => XRDIN,
		XRCS_N => XRCS_N,
		XRDOUT => XRDOUT,
		XINIT_N => XINIT_N,
		XRHSH => XRHSH,
		XRD => XRD
	);

  -- Oscilator
  CCLK_process : process
  begin
		CCLK <= '0';
		wait for (CCLK_period / 2);
		CCLK <= '1';
		wait for (CCLK_period / 2);
  end process;
 

   -- Stimulus process
   stim_proc: process
   begin		
      -- hold reset state for 100ms.
      wait for 1 ms;
      RESET_N <= '0';

      wait for CCLK_period * 10;
      RESET_N <= '1';

      -- insert stimulus here 

      wait;
   end process;

END;
