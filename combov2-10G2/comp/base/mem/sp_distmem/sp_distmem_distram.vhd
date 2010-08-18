--
-- sp_distmem_distram.vhd: Generic component encapsulating selected types of
-- Distributed SelectRAM
-- Copyright (C) 2005 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
--
library IEEE;
use IEEE.std_logic_1164.all;
-- auxilarity functions and constant needed to evaluate generic address etc.
use WORK.distmem_func.all;

-- pragma translate_off
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity SP_DISTMEM_DISTRAM is
   generic(
      DISTMEM_TYPE : natural  --only 16,32,64,128
      );

   port(
      -- R/W Port
      DI     : in std_logic;
      WE     : in std_logic;
      WCLK   : in std_logic;
      ADDR   : in std_logic_vector (DISTMEM_ADDR_WIDTH(DISTMEM_TYPE)-1 downto 0);
      DO     : out std_logic
   );
end entity SP_DISTMEM_DISTRAM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture SP_DISTMEM_DISTRAM_ARCH of SP_DISTMEM_DISTRAM is

   -- Distributed RAM 16x1 single port ------------------------------------------
   component RAM16X1S
   -- pragma translate_off
   generic (
      INIT : bit_vector := X"0000"
      );
   -- pragma translate_on
   port (
      D     : in std_logic;
      WE    : in std_logic;
      WCLK  : in std_logic;
      A0    : in std_logic;
      A1    : in std_logic;
      A2    : in std_logic;
      A3    : in std_logic;
      O   : out std_logic
   );
   end component;

   -- Distributed RAM 32x1 single port ------------------------------------------
   component RAM32X1S
   -- pragma translate_off
   generic (
      INIT : bit_vector := X"00000000"
   );
   -- pragma translate_on
   port (
      D     : in std_logic;
      WE    : in std_logic;
      WCLK  : in std_logic;
      A0    : in std_logic;
      A1    : in std_logic;
      A2    : in std_logic;
      A3    : in std_logic;
      A4    : in std_logic;
      O   : out std_logic
   );
   end component;

   -- Distributed RAM 64x1 single port ------------------------------------------
   component RAM64X1S
   -- pragma translate_off
   generic (
      INIT : bit_vector := X"0000000000000000"
   );
   -- pragma translate_on
   port (
      D     : in std_logic;
      WE    : in std_logic;
      WCLK  : in std_logic;
      A0    : in std_logic;
      A1    : in std_logic;
      A2    : in std_logic;
      A3    : in std_logic;
      A4    : in std_logic;
      A5    : in std_logic;
      O   : out std_logic
   );
   end component;


   -- Distributed RAM 128x1 single port ----------------------------------------
   component RAM128X1S
      -- pragma translate_off
     generic (
        INIT : bit_vector := X"00000000000000000000000000000000"
      	);
      -- pragma translate_on
      port (
        	D    : in std_logic;
         WE   : in std_logic;
         WCLK : in std_logic;
         A0   : in std_logic;
         A1   : in std_logic;
         A2   : in std_logic;
         A3   : in std_logic;
         A4   : in std_logic;
         A5   : in std_logic;
         A6   : in std_logic;
         O    : out std_logic
      	);
   end component;


   signal addr_delayed  : std_logic_vector(DISTMEM_ADDR_WIDTH(DISTMEM_TYPE)-1 downto 0);
   signal we_delayed     : std_logic;
   signal di_delayed     : std_logic;

begin
--
-- THIS PART - solves distributed ram simulation problems
--           - delays will be used ONLY in BEHAVIORAL simulation

   -- Control signals for memory ----------------------------------------------
   we_delayed <= WE
   -- pragma translate_off
   after 150 ps -- Solves problem in functional simulation
   -- pragma translate_on
   ;

   -- Distributed RAM requires to keep data on memory input after
   -- write rising clock for a moment. We will include signal, that
   -- ensure that data will keep on memory input.
   di_delayed  <= DI
   -- pragma translate_off
   after 150 ps -- Solves problem in functional simulation
   -- pragma translate_on
   ;

   addr_delayed <= ADDR
   -- pragma translate_off
   after 150 ps -- Solves problem in functional simulation
   -- pragma translate_on
   ;

--
-- END
--

-- Distributed SelectRAM Instantiation
generate_1: if (DISTMEM_TYPE = 16) generate
   U_RAM16X1S: RAM16X1S
     port map (
   	D      => di_delayed, -- insert input signal
   	WE     => we_delayed, -- insert Write Enable signal
   	WCLK   => WCLK, -- insert Write Clock signal
   	A0     => addr_delayed(0), -- insert Address 0 signal port SPO
   	A1     => addr_delayed(1), -- insert Address 1 signal port SPO
   	A2     => addr_delayed(2), -- insert Address 2 signal port SPO
   	A3     => addr_delayed(3), -- insert Address 3 signal port SPO
    	O    => DO  -- insert output signal
   	);
end generate;


-- Distributed SelectRAM Instantiation
generate_2: if (DISTMEM_TYPE = 32) generate
   U_RAM32X1S: RAM32X1S
     port map (
   	D      => di_delayed, -- insert input signal
   	WE     => we_delayed, -- insert Write Enable signal
   	WCLK   => WCLK, -- insert Write Clock signal
   	A0     => addr_delayed(0), -- insert Address 0 signal port SPO
   	A1     => addr_delayed(1), -- insert Address 1 signal port SPO
   	A2     => addr_delayed(2), -- insert Address 2 signal port SPO
   	A3     => addr_delayed(3), -- insert Address 3 signal port SPO
   	A4     => addr_delayed(4), -- insert Address 4 signal port SPO
   	O    => DO  -- insert output signal
   	);
end generate;

-- Distributed SelectRAM Instantiation
generate_3: if (DISTMEM_TYPE = 64) generate
   U_RAM64X1S: RAM64X1S
     port map (
   	D      => di_delayed, -- insert input signal
   	WE     => we_delayed, -- insert Write Enable signal
   	WCLK   => WCLK, -- insert Write Clock signal
   	A0     => addr_delayed(0), -- insert Address 0 signal port SPO
   	A1     => addr_delayed(1), -- insert Address 1 signal port SPO
   	A2     => addr_delayed(2), -- insert Address 2 signal port SPO
   	A3     => addr_delayed(3), -- insert Address 3 signal port SPO
   	A4     => addr_delayed(4), -- insert Address 4 signal port SPO
   	A5     => addr_delayed(5), -- insert Address 5 signal port SPO
   	O      => DO  -- insert output signal
   	);
end generate;



-- Distributed SelectRAM Instantiation
generate_4: if (DISTMEM_TYPE = 128) generate
   U_RAM64X1S: RAM128X1S
     port map (
   	D      => di_delayed, -- insert input signal
   	WE     => we_delayed, -- insert Write Enable signal
   	WCLK   => WCLK, -- insert Write Clock signal
   	A0     => addr_delayed(0), -- insert Address 0 signal port SPO
   	A1     => addr_delayed(1), -- insert Address 1 signal port SPO
   	A2     => addr_delayed(2), -- insert Address 2 signal port SPO
   	A3     => addr_delayed(3), -- insert Address 3 signal port SPO
   	A4     => addr_delayed(4), -- insert Address 4 signal port SPO
   	A5     => addr_delayed(5), -- insert Address 5 signal port SPO
   	A6     => addr_delayed(6), -- insert Address 6 signal port SPO
   	O      => DO  -- insert output signal
   	);
end generate;


end architecture SP_DISTMEM_DISTRAM_ARCH;
