--
-- dp_distmem_distram.vhd: Generic component encapsulating selected types of
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
entity DP_DISTMEM_DISTRAM is
   generic(
      DISTMEM_TYPE : natural := 16  --only 16,32,64
      );

   port(
      -- R/W Port
      DI     : in std_logic;
      WE     : in std_logic;
      WCLK   : in std_logic;
      ADDRA  : in std_logic_vector (DISTMEM_ADDR_WIDTH(DISTMEM_TYPE)-1 downto 0);
      DOA    : out std_logic;
      -- Read Port
      ADDRB  : in std_logic_vector (DISTMEM_ADDR_WIDTH(DISTMEM_TYPE)-1 downto 0);
      DOB    : out std_logic
   );
end entity DP_DISTMEM_DISTRAM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture DP_DISTMEM_DISTRAM_ARCH of DP_DISTMEM_DISTRAM is

   -- Distributed RAM 16x1 dual port ------------------------------------------
   component RAM16X1D
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
      DPRA0 : in std_logic;
      DPRA1 : in std_logic;
      DPRA2 : in std_logic;
      DPRA3 : in std_logic;
      SPO   : out std_logic;
      DPO   : out std_logic
   );
   end component;

   -- Distributed RAM 32x1 dual port ------------------------------------------
   component RAM32X1D
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
      DPRA0 : in std_logic;
      DPRA1 : in std_logic;
      DPRA2 : in std_logic;
      DPRA3 : in std_logic;
      DPRA4 : in std_logic;
      SPO   : out std_logic;
      DPO   : out std_logic
   );
   end component;

   -- Distributed RAM 64x1 dual port ------------------------------------------
   component RAM64X1D
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
      DPRA0 : in std_logic;
      DPRA1 : in std_logic;
      DPRA2 : in std_logic;
      DPRA3 : in std_logic;
      DPRA4 : in std_logic;
      DPRA5 : in std_logic;
      SPO   : out std_logic;
      DPO   : out std_logic
   );
   end component;

   signal addra_delayed  : std_logic_vector(DISTMEM_ADDR_WIDTH(DISTMEM_TYPE)-1 downto 0);
   signal addrb_delayed  : std_logic_vector(DISTMEM_ADDR_WIDTH(DISTMEM_TYPE)-1 downto 0);
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

   addra_delayed <= ADDRA
   -- pragma translate_off
   after 150 ps -- Solves problem in functional simulation
   -- pragma translate_on
   ;

   addrb_delayed <= ADDRB
   -- pragma translate_off
   after 150 ps -- Solves problem in functional simulation
   -- pragma translate_on
   ;
--
-- END
--

-- Distributed SelectRAM Instantiation
generate_1: if (DISTMEM_TYPE = 16) generate
   U_RAM16X1D: RAM16X1D
     port map (
   	D      => di_delayed, -- insert input signal
   	WE     => we_delayed, -- insert Write Enable signal
   	WCLK   => WCLK, -- insert Write Clock signal
   	A0     => addra_delayed(0), -- insert Address 0 signal port SPO
   	A1     => addra_delayed(1), -- insert Address 1 signal port SPO
   	A2     => addra_delayed(2), -- insert Address 2 signal port SPO
   	A3     => addra_delayed(3), -- insert Address 3 signal port SPO
   	DPRA0  => addrb_delayed(0), -- insert Address 0 signal port DPO
   	DPRA1  => addrb_delayed(1), -- insert Address 1 signal port DPO
   	DPRA2  => addrb_delayed(2), -- insert Address 2 signal port DPO
   	DPRA3  => addrb_delayed(3), -- insert Address 3 signal port DPO
   	SPO    => DOA, -- insert output signal
   	DPO    => DOB  -- insert output signal
   	);
end generate;


-- Distributed SelectRAM Instantiation
generate_2: if (DISTMEM_TYPE = 32) generate
   U_RAM32X1D: RAM32X1D
     port map (
   	D      => di_delayed, -- insert input signal
   	WE     => we_delayed, -- insert Write Enable signal
   	WCLK   => WCLK, -- insert Write Clock signal
   	A0     => addra_delayed(0), -- insert Address 0 signal port SPO
   	A1     => addra_delayed(1), -- insert Address 1 signal port SPO
   	A2     => addra_delayed(2), -- insert Address 2 signal port SPO
   	A3     => addra_delayed(3), -- insert Address 3 signal port SPO
   	A4     => addra_delayed(4), -- insert Address 4 signal port SPO
   	DPRA0  => addrb_delayed(0), -- insert Address 0 signal port DPO
   	DPRA1  => addrb_delayed(1), -- insert Address 1 signal port DPO
   	DPRA2  => addrb_delayed(2), -- insert Address 2 signal port DPO
   	DPRA3  => addrb_delayed(3), -- insert Address 3 signal port DPO
   	DPRA4  => addrb_delayed(4), -- insert Address 4 signal port DPO
   	SPO    => DOA, -- insert output signal
   	DPO    => DOB  -- insert output signal
   	);
end generate;

-- Distributed SelectRAM Instantiation
generate_3: if (DISTMEM_TYPE = 64) generate
   U_RAM64X1D: RAM64X1D
     port map (
   	D      => di_delayed, -- insert input signal
   	WE     => we_delayed, -- insert Write Enable signal
   	WCLK   => WCLK, -- insert Write Clock signal
   	A0     => addra_delayed(0), -- insert Address 0 signal port SPO
   	A1     => addra_delayed(1), -- insert Address 1 signal port SPO
   	A2     => addra_delayed(2), -- insert Address 2 signal port SPO
   	A3     => addra_delayed(3), -- insert Address 3 signal port SPO
   	A4     => addra_delayed(4), -- insert Address 4 signal port SPO
   	A5     => addra_delayed(5), -- insert Address 5 signal port SPO
   	DPRA0  => addrb_delayed(0), -- insert Address 0 signal port DPO
   	DPRA1  => addrb_delayed(1), -- insert Address 1 signal port DPO
   	DPRA2  => addrb_delayed(2), -- insert Address 2 signal port DPO
   	DPRA3  => addrb_delayed(3), -- insert Address 3 signal port DPO
   	DPRA4  => addrb_delayed(4), -- insert Address 4 signal port DPO
   	DPRA5  => addrb_delayed(5), -- insert Address 5 signal port DPO
   	SPO    => DOA, -- insert output signal
   	DPO    => DOB  -- insert output signal
   	);
end generate;

end architecture DP_DISTMEM_DISTRAM_ARCH;
