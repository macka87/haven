--
-- virtex5.vhd: Simul Virtex5 config
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

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

---- Uncomment the following library declaration if instantiating
---- any Xilinx primitives in this code.
--library UNISIM;
--use UNISIM.VComponents.all;

entity virtex5 is
port(
    XRCCLK         : in std_logic;
    XDONE          : out std_logic;
    XPROGRAM_N     : in std_logic;
    XM0            : in std_logic;
    XRRDWR_N       : in std_logic;
    XRDIN          : in std_logic;
    XRCS_N         : in std_logic;
    XRDOUT         : out std_logic;
    XINIT_N        : out std_logic;
    --
    XRHSH          : inout std_logic_vector( 11 downto 0 );
    XRD            : in std_logic_vector( 7 downto 0 )
);
end virtex5;

architecture Behavioral of virtex5 is
  constant XC5VLX50T_BITSTREAM_SIZE : integer := 14052352;
  constant TEST_BITSTREAM_SIZE : integer := 16;
  constant BITSTREAM_SIZE : integer := TEST_BITSTREAM_SIZE;
  constant STARTUP_SEQUENCE : integer := 8;
  signal bitstream_counter : integer range 0 to (STARTUP_SEQUENCE + BITSTREAM_SIZE);
  signal xinit_internal : std_logic;
begin
  
  -- Async
  XINIT_N <= XPROGRAM_N after 100 ns;
  xinit_internal <= XPROGRAM_N after 100 ns;
  XRHSH <= (others=>'0');
  XRDOUT <= '0';
  
  process( XPROGRAM_N )
  begin
    if( XPROGRAM_N='0' and XPROGRAM_N'event )then
      REPORT "*************** PROG - Init **********************";
    end if;
  end process;
  
  process( xinit_internal )
  begin
    if( xinit_internal='1' and xinit_internal'event )then
      REPORT "*************** INIT - Done **********************";
    end if;
  end process;
  
  -- Sync
  process( XRCCLK, XPROGRAM_N )
  begin
    if( XPROGRAM_N = '0' )then
      bitstream_counter <= 0;
      XDONE <= '0';
    elsif( XRCCLK='1' and XRCCLK'event )then
      if( not(bitstream_counter = (BITSTREAM_SIZE + STARTUP_SEQUENCE)) ) then
        if( bitstream_counter = 0 ) then
          REPORT "*************** Bitstream loading - start **********************";
        end if;
        if( bitstream_counter = BITSTREAM_SIZE-1 ) then
          REPORT "*************** Bitstream loading - finish **********************";
        end if;
        if( bitstream_counter = BITSTREAM_SIZE ) then
          REPORT "*************** Startup sequence - start **********************";
        end if;
        if( bitstream_counter = (BITSTREAM_SIZE + STARTUP_SEQUENCE - 1) ) then
          XDONE <= '1';
          REPORT "*************** Startup sequence - finish **********************";
        end if;
        bitstream_counter <= bitstream_counter + 1;
      end if;
    end if;
  end process;
  
  
end Behavioral;

