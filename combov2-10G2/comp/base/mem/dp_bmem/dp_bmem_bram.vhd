--
-- dp_bmem_bram.vhd: Generic component encapsulating selected types of Bram
-- Copyright (C) 2004 CESNET
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
--
-- README: This component only enscasulate Block Ram of type
--         defined by generic parameter BRAM_TYPE. Block ram
--         with parity input and output are modified this way.
--         Parity input and normal input is conected together.
--         Outputs is conected sema way.
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
-- auxilarity functions and constant needed to evaluate generic address etc.
use WORK.bmem_func.all;

-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on



-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity DP_BMEM_BRAM is

   generic(
      BRAM_TYPE   : natural := 1;   --only 1,2,4,8,18,36
      -- What operation will be performed first when both WE and RE are
      -- active? Only for behavioral simulation purpose.
      -- WRITE_FIRST(default) | READ_FIRST | NO_CHANGE
      WR_MODE_A   : string := "WRITE_FIRST";
      WR_MODE_B   : string := "WRITE_FIRST"
   );

   port(
      DIA     : in std_logic_vector (BRAM_DATA_WIDTH(BRAM_TYPE)-1
                           + BRAM_PARITY_WIDTH(BRAM_TYPE) downto 0);
   	ADDRA   : in std_logic_vector (BRAM_ADDR_WIDTH(BRAM_TYPE)-1 downto 0);
   	ENA     : in std_logic;
   	WEA     : in std_logic;
   	SSRA    : in std_logic;
   	CLKA    : in std_logic;
   	DOA     : out std_logic_vector (BRAM_DATA_WIDTH(BRAM_TYPE)-1
                           + BRAM_PARITY_WIDTH(BRAM_TYPE) downto 0);
      --
   	DIB     : in std_logic_vector (BRAM_DATA_WIDTH(BRAM_TYPE)-1
                           + BRAM_PARITY_WIDTH(BRAM_TYPE) downto 0);
   	ADDRB   : in std_logic_vector (BRAM_ADDR_WIDTH(BRAM_TYPE)-1 downto 0);
   	ENB     : in std_logic;
   	WEB     : in std_logic;
   	SSRB    : in std_logic;
   	CLKB    : in std_logic;
   	DOB     : out std_logic_vector (BRAM_DATA_WIDTH(BRAM_TYPE)-1
                           + BRAM_PARITY_WIDTH(BRAM_TYPE) downto 0)
   );
end entity DP_BMEM_BRAM;




-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture DP_BMEM_BRAM_ARCH of DP_BMEM_BRAM is

   -- constant definition
   constant data_width : integer := BRAM_DATA_WIDTH(BRAM_TYPE);
   constant parity_width : integer := BRAM_PARITY_WIDTH(BRAM_TYPE);
   constant addr_width : integer := BRAM_ADDR_WIDTH(BRAM_TYPE);

-- Declaration of relevant Block Ram components
-- ----------------------------------------------------------------------------
   component RAMB16_S1_S1
      -- pragma translate_off
      generic (
         WRITE_MODE_A   : string := "WRITE_FIRST";
         WRITE_MODE_B   : string := "WRITE_FIRST"
      );
      -- pragma translate_on
      port (
   	   DIA     : in std_logic_vector (0 downto 0);
      	ADDRA   : in std_logic_vector (13 downto 0);
      	ENA     : in std_logic;
      	WEA     : in std_logic;
      	SSRA    : in std_logic;
      	CLKA    : in std_logic;
      	DOA     : out std_logic_vector (0 downto 0);
         --
      	DIB     : in std_logic_vector (0 downto 0);
      	ADDRB   : in std_logic_vector (13 downto 0);
      	ENB     : in std_logic;
      	WEB     : in std_logic;
      	SSRB    : in std_logic;
      	CLKB    : in std_logic;
      	DOB     : out std_logic_vector (0 downto 0)
   	);
   end component;

-- ----------------------------------------------------------------------------
   component RAMB16_S2_S2
      -- pragma translate_off
      generic (
         WRITE_MODE_A   : string := "WRITE_FIRST";
         WRITE_MODE_B   : string := "WRITE_FIRST"
      );
      -- pragma translate_on
      port (
      	DIA     : in std_logic_vector (1 downto 0);
      	ADDRA   : in std_logic_vector (12 downto 0);
         ENA     : in std_logic;
      	WEA     : in std_logic;
      	SSRA    : in std_logic;
      	CLKA    : in std_logic;
      	DOA     : out std_logic_vector (1 downto 0);
         --
      	DIB     : in std_logic_vector (1 downto 0);
      	ADDRB   : in std_logic_vector (12 downto 0);
      	ENB     : in std_logic;
      	WEB     : in std_logic;
      	SSRB    : in std_logic;
      	CLKB    : in std_logic;
      	DOB     : out std_logic_vector (1 downto 0)
   	);
   end component;


-- ----------------------------------------------------------------------------
   component RAMB16_S4_S4
      -- pragma translate_off
      generic (
         WRITE_MODE_A   : string := "WRITE_FIRST";
         WRITE_MODE_B   : string := "WRITE_FIRST"
      );
      -- pragma translate_on
      port (
      	DIA     : in std_logic_vector (3 downto 0);
      	ADDRA   : in std_logic_vector (11 downto 0);
      	ENA     : in std_logic;
      	WEA     : in std_logic;
      	SSRA    : in std_logic;
      	CLKA    : in std_logic;
      	DOA     : out std_logic_vector (3 downto 0);
         --
      	DIB     : in std_logic_vector (3 downto 0);
      	ADDRB   : in std_logic_vector (11 downto 0);
      	ENB     : in std_logic;
      	WEB     : in std_logic;
      	SSRB    : in std_logic;
      	CLKB    : in std_logic;
      	DOB     : out std_logic_vector (3 downto 0)
      	);
   end component;


-- ----------------------------------------------------------------------------
   component RAMB16_S9_S9
      -- pragma translate_off
      generic (
         WRITE_MODE_A   : string := "WRITE_FIRST";
         WRITE_MODE_B   : string := "WRITE_FIRST"
      );
      -- pragma translate_on
      port (
      	DIA     : in std_logic_vector (7 downto 0);
      	DIPA    : in std_logic_vector (0 downto 0);
      	ADDRA   : in std_logic_vector (10 downto 0);
      	ENA     : in std_logic;
      	WEA     : in std_logic;
      	SSRA    : in std_logic;
      	CLKA    : in std_logic;
      	DOA     : out std_logic_vector (7 downto 0);
      	DOPA    : out std_logic_vector (0 downto 0);
         --
      	DIB     : in std_logic_vector (7 downto 0);
      	DIPB    : in std_logic_vector (0 downto 0);
      	ADDRB   : in std_logic_vector (10 downto 0);
      	ENB     : in std_logic;
      	WEB     : in std_logic;
      	SSRB    : in std_logic;
      	CLKB    : in std_logic;
      	DOB     : out std_logic_vector (7 downto 0);
      	DOPB    : out std_logic_vector (0 downto 0)
   	);
   end component;


-- ----------------------------------------------------------------------------
   component RAMB16_S18_S18
      -- pragma translate_off
      generic (
         WRITE_MODE_A   : string := "WRITE_FIRST";
         WRITE_MODE_B   : string := "WRITE_FIRST"
      );
      -- pragma translate_on
      port (
      	DIA     : in std_logic_vector (15 downto 0);
      	DIPA    : in std_logic_vector (1 downto 0);
      	ADDRA   : in std_logic_vector (9 downto 0);
      	ENA     : in std_logic;
      	WEA     : in std_logic;
      	SSRA    : in std_logic;
      	CLKA    : in std_logic;
      	DOA     : out std_logic_vector (15 downto 0);
      	DOPA    : out std_logic_vector (1 downto 0);
         --
       	DIB     : in std_logic_vector (15 downto 0);
      	DIPB    : in std_logic_vector (1 downto 0);
      	ADDRB   : in std_logic_vector (9 downto 0);
      	ENB     : in std_logic;
      	WEB     : in std_logic;
      	SSRB    : in std_logic;
      	CLKB    : in std_logic;
      	DOB     : out std_logic_vector (15 downto 0);
      	DOPB    : out std_logic_vector (1 downto 0)
      	);
   end component;


-- ----------------------------------------------------------------------------
   component RAMB16_S36_S36
      -- pragma translate_off
      generic (
         WRITE_MODE_A   : string := "WRITE_FIRST";
         WRITE_MODE_B   : string := "WRITE_FIRST"
      );
      -- pragma translate_on
      port (
      	DIA     : in std_logic_vector (31 downto 0);
      	DIPA    : in std_logic_vector (3 downto 0);
      	ADDRA   : in std_logic_vector (8 downto 0);
      	ENA     : in std_logic;
      	WEA     : in std_logic;
      	SSRA    : in std_logic;
      	CLKA    : in std_logic;
      	DOA     : out std_logic_vector (31 downto 0);
      	DOPA    : out std_logic_vector (3 downto 0);
         --
      	DIB     : in std_logic_vector (31 downto 0);
      	DIPB    : in std_logic_vector (3 downto 0);
      	ADDRB   : in std_logic_vector (8 downto 0);
      	ENB     : in std_logic;
      	WEB     : in std_logic;
      	SSRB    : in std_logic;
      	CLKB    : in std_logic;
      	DOB     : out std_logic_vector (31 downto 0);
      	DOPB    : out std_logic_vector (3 downto 0)
      	);
   end component;

   -- attributes definition
   attribute WRITE_MODE_A  : string;
   attribute WRITE_MODE_B  : string;
   attribute WRITE_MODE_A of RAMB16_S1_S1: component is WR_MODE_A;
   attribute WRITE_MODE_B of RAMB16_S1_S1: component is WR_MODE_B;
   attribute WRITE_MODE_A of RAMB16_S2_S2: component is WR_MODE_A;
   attribute WRITE_MODE_B of RAMB16_S2_S2: component is WR_MODE_B;
   attribute WRITE_MODE_A of RAMB16_S4_S4: component is WR_MODE_A;
   attribute WRITE_MODE_B of RAMB16_S4_S4: component is WR_MODE_B;
   attribute WRITE_MODE_A of RAMB16_S9_S9: component is WR_MODE_A;
   attribute WRITE_MODE_B of RAMB16_S9_S9: component is WR_MODE_B;
   attribute WRITE_MODE_A of RAMB16_S18_S18: component is WR_MODE_A;
   attribute WRITE_MODE_B of RAMB16_S18_S18: component is WR_MODE_B;
   attribute WRITE_MODE_A of RAMB16_S36_S36: component is WR_MODE_A;
   attribute WRITE_MODE_B of RAMB16_S36_S36: component is WR_MODE_B;

begin

-- ----------------------------------------------------------------------------
   -- asertion of bram type (some error i can't find it)
   -- assert ((BRAM_TYPE = 1) | (BRAM_TYPE = 2) | (BRAM_TYPE = 4) |
   --    (BRAM_TYPE = 9) | (BRAM_TYPE = 18) | (BRAM_TYPE = 36))
   --    report "illegal bram type - only 1,2,4,9,18,36 is allowed"
   --    severity error;



-- ----------------------------------------------------------------------------
-- Port maping of 1bit blockram
   generate_bram1: if (BRAM_TYPE = 1) generate
      genmem_bram1: RAMB16_S1_S1
         -- pragma translate_off
         generic map (
            WRITE_MODE_A   => WR_MODE_A,
            WRITE_MODE_B   => WR_MODE_B
         )
         -- pragma translate_on
         port map (
            DIA     => DIA,
            ADDRA   => ADDRA,
         	ENA     => ENA,
         	WEA     => WEA,
         	SSRA    => SSRA,
         	CLKA    => CLKA,
         	DOA     => DOA,
            --
         	DIB     => DIB,
         	ADDRB   => ADDRB,
         	ENB     => ENB,
         	WEB     => WEB,
         	SSRB    => SSRB,
         	CLKB    => CLKB,
         	DOB     => DOB
         );
   end generate;


-- ----------------------------------------------------------------------------
-- Port maping of 2bit blockram
   generate_bram2: if (BRAM_TYPE = 2) generate
   genmem_bram2: RAMB16_S2_S2
      -- pragma translate_off
      generic map (
         WRITE_MODE_A   => WR_MODE_A,
         WRITE_MODE_B   => WR_MODE_B
      )
      -- pragma translate_on
      port map (
         DIA     => DIA,
         ADDRA   => ADDRA,
      	ENA     => ENA,
      	WEA     => WEA,
      	SSRA    => SSRA,
      	CLKA    => CLKA,
      	DOA     => DOA,
         --
      	DIB     => DIB,
      	ADDRB   => ADDRB,
      	ENB     => ENB,
      	WEB     => WEB,
      	SSRB    => SSRB,
      	CLKB    => CLKB,
      	DOB     => DOB
      );
   end generate;


-- ----------------------------------------------------------------------------
-- Port maping of 4bit blockram
   generate_bram4: if (BRAM_TYPE = 4) generate
   genmem_bram4: RAMB16_S4_S4
      -- pragma translate_off
      generic map (
         WRITE_MODE_A   => WR_MODE_A,
         WRITE_MODE_B   => WR_MODE_B
      )
      -- pragma translate_on
      port map (
         DIA     => DIA,
         ADDRA   => ADDRA,
      	ENA     => ENA,
      	WEA     => WEA,
      	SSRA    => SSRA,
      	CLKA    => CLKA,
      	DOA     => DOA,
         --
      	DIB     => DIB,
      	ADDRB   => ADDRB,
      	ENB     => ENB,
      	WEB     => WEB,
      	SSRB    => SSRB,
      	CLKB    => CLKB,
      	DOB     => DOB
   	);
   end generate;


-- ----------------------------------------------------------------------------
-- Port maping of 8bit blockram
   generate_bram9: if (BRAM_TYPE = 9) generate
   genmem_bram9: RAMB16_S9_S9
      -- pragma translate_off
      generic map (
         WRITE_MODE_A   => WR_MODE_A,
         WRITE_MODE_B   => WR_MODE_B
      )
      -- pragma translate_on
      port map (
         DIA     => DIA(data_width-1 downto 0),
         DIPA    => DIA(data_width-1 + parity_width downto data_width),
         ADDRA   => ADDRA,
      	ENA     => ENA,
      	WEA     => WEA,
      	SSRA    => SSRA,
      	CLKA    => CLKA,
      	DOA     => DOA(data_width-1 downto 0),
         DOPA    => DOA(data_width-1 + parity_width downto data_width),
         --
      	DIB     => DIB(data_width-1 downto 0),
         DIPB    => DIB(data_width-1 + parity_width downto data_width),
      	ADDRB   => ADDRB,
      	ENB     => ENB,
      	WEB     => WEB,
      	SSRB    => SSRB,
      	CLKB    => CLKB,
      	DOB     => DOB(data_width-1 downto 0),
         DOPB    => DOB(data_width-1 + parity_width downto data_width)
        	);
   end generate;

-- ----------------------------------------------------------------------------
-- Port maping of 16bit blockram
   generate_bram18: if (BRAM_TYPE = 18) generate
   genmem_bram18: RAMB16_S18_S18
      -- pragma translate_off
      generic map (
         WRITE_MODE_A   => WR_MODE_A,
         WRITE_MODE_B   => WR_MODE_B
      )
      -- pragma translate_on
      port map (
         DIA     => DIA(data_width-1 downto 0),
         DIPA    => DIA(data_width-1 + parity_width downto data_width),
         ADDRA   => ADDRA,
      	ENA     => ENA,
      	WEA     => WEA,
      	SSRA    => SSRA,
      	CLKA    => CLKA,
      	DOA     => DOA(data_width-1 downto 0),
         DOPA    => DOA(data_width-1 + parity_width downto data_width),
         --
      	DIB     => DIB(data_width-1 downto 0),
         DIPB    => DIB(data_width-1 + parity_width downto data_width),
      	ADDRB   => ADDRB,
      	ENB     => ENB,
      	WEB     => WEB,
      	SSRB    => SSRB,
      	CLKB    => CLKB,
      	DOB     => DOB(data_width-1 downto 0),
         DOPB    => DOB(data_width-1 + parity_width downto data_width)
     	);
   end generate;


-- ----------------------------------------------------------------------------
-- Port maping of 32bit blockram
   generate_bram36: if (BRAM_TYPE = 36) generate
   genmem_bram36: RAMB16_S36_S36
      -- pragma translate_off
      generic map (
         WRITE_MODE_A   => WR_MODE_A,
         WRITE_MODE_B   => WR_MODE_B
      )
      -- pragma translate_on
      port map (
         DIA     => DIA(data_width-1 downto 0),
         DIPA    => DIA(data_width-1 + parity_width downto data_width),
         ADDRA   => ADDRA,
      	ENA     => ENA,
      	WEA     => WEA,
      	SSRA    => SSRA,
      	CLKA    => CLKA,
      	DOA     => DOA(data_width-1 downto 0),
         DOPA    => DOA(data_width-1 + parity_width downto data_width),
         --
      	DIB     => DIB(data_width-1 downto 0),
         DIPB    => DIB(data_width-1 + parity_width downto data_width),
      	ADDRB   => ADDRB,
      	ENB     => ENB,
      	WEB     => WEB,
      	SSRB    => SSRB,
      	CLKB    => CLKB,
      	DOB     => DOB(data_width-1 downto 0),
         DOPB    => DOB(data_width-1 + parity_width downto data_width)
        	);
   end generate;


end architecture DP_BMEM_BRAM_ARCH;

