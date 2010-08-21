--
-- sp_bmem_bram.vhd: Generic component encapsulating selected types of
--                   Single port BlockRams
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
--
-- README: This component only enscasulate Block Ram of type
--         defined by generic parameter BRAM_TYPE. Block ram
--         with parity input and output are modified this way.
--         Parity input and normal input is conected together.
--         Outputs is conected same way.
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
entity SP_BMEM_BRAM is

   generic(
      BRAM_TYPE : natural --only 1,2,4,8,18,36
   );

   port(
      DI     : in std_logic_vector (BRAM_DATA_WIDTH(BRAM_TYPE)-1
                           + BRAM_PARITY_WIDTH(BRAM_TYPE) downto 0);
   	ADDR   : in std_logic_vector (BRAM_ADDR_WIDTH(BRAM_TYPE)-1 downto 0);
   	EN     : in std_logic;
   	WE     : in std_logic;
   	SSR    : in std_logic;
   	CLK    : in std_logic;
   	DO     : out std_logic_vector (BRAM_DATA_WIDTH(BRAM_TYPE)-1
                           + BRAM_PARITY_WIDTH(BRAM_TYPE) downto 0)
      );
end entity SP_BMEM_BRAM;




-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture SP_BMEM_BRAM_ARCH of SP_BMEM_BRAM is

   -- constant definition
   constant data_width : integer := BRAM_DATA_WIDTH(BRAM_TYPE);
   constant parity_width : integer := BRAM_PARITY_WIDTH(BRAM_TYPE);
   constant addr_width : integer := BRAM_ADDR_WIDTH(BRAM_TYPE);


-- Declaration of relevant Block Ram components
-- ----------------------------------------------------------------------------
   component RAMB16_S1
      port (
      	DI     : in std_logic_vector (0 downto 0);
      	ADDR   : in std_logic_vector (13 downto 0);
      	EN     : in std_logic;
      	WE     : in std_logic;
      	SSR    : in std_logic;
      	CLK    : in std_logic;
      	DO     : out std_logic_vector (0 downto 0)
   	);
   end component;


-- ----------------------------------------------------------------------------
   component RAMB16_S2
      port (
         DI     : in std_logic_vector (1 downto 0);
      	ADDR   : in std_logic_vector (12 downto 0);
      	EN     : in std_logic;
      	WE     : in std_logic;
      	SSR    : in std_logic;
      	CLK    : in std_logic;
      	DO     : out std_logic_vector (1 downto 0)
   	);
   end component;


-- ----------------------------------------------------------------------------
   component RAMB16_S4
      port (
	      DI     : in std_logic_vector (3 downto 0);
      	ADDR   : in std_logic_vector (11 downto 0);
      	EN     : in std_logic;
      	WE     : in std_logic;
      	SSR    : in std_logic;
      	CLK    : in std_logic;
      	DO     : out std_logic_vector (3 downto 0)
   	);
   end component;


-- ----------------------------------------------------------------------------
   component RAMB16_S9
      port (
      	DI     : in std_logic_vector (7 downto 0);
      	DIP    : in std_logic_vector (0 downto 0);
      	ADDR   : in std_logic_vector (10 downto 0);
      	EN     : in std_logic;
      	WE     : in std_logic;
      	SSR    : in std_logic;
      	CLK    : in std_logic;
      	DO     : out std_logic_vector (7 downto 0);
      	DOP    : out std_logic_vector (0 downto 0)
   	);
   end component;


-- ----------------------------------------------------------------------------
   component RAMB16_S18
      port (
      	DI     : in std_logic_vector (15 downto 0);
      	DIP    : in std_logic_vector (1 downto 0);
      	ADDR   : in std_logic_vector (9 downto 0);
      	EN     : in std_logic;
      	WE     : in std_logic;
      	SSR    : in std_logic;
      	CLK    : in std_logic;
      	DO     : out std_logic_vector (15 downto 0);
      	DOP    : out std_logic_vector (1 downto 0)
   	);
   end component;


-- ----------------------------------------------------------------------------
   component RAMB16_S36
      port (
        	DI     : in std_logic_vector (31 downto 0);
        	DIP    : in std_logic_vector (3 downto 0);
        	ADDR   : in std_logic_vector (8 downto 0);
        	EN     : in std_logic;
         WE     : in std_logic;
         SSR    : in std_logic;
        	CLK    : in std_logic;
        	DO     : out std_logic_vector (31 downto 0);
        	DOP    : out std_logic_vector (3 downto 0)
     	);
   end component;


begin

-- ----------------------------------------------------------------------------
-- Port maping of 1bit blockram
   generate_bram1: if (BRAM_TYPE = 1) generate
      genmem_bram1: RAMB16_S1
         port map (
            DI     => DI,
            ADDR   => ADDR,
         	EN     => EN,
         	WE     => WE,
         	SSR    => SSR,
         	CLK    => CLK,
         	DO     => DO
         );
   end generate;


-- ----------------------------------------------------------------------------
-- Port maping of 2bit blockram
   generate_bram2: if (BRAM_TYPE = 2) generate
   genmem_bram2: RAMB16_S2
      port map (
         DI     => DI,
         ADDR   => ADDR,
      	EN     => EN,
      	WE     => WE,
      	SSR    => SSR,
      	CLK    => CLK,
      	DO     => DO
      );
   end generate;


-- ----------------------------------------------------------------------------
-- Port maping of 4bit blockram
   generate_bram4: if (BRAM_TYPE = 4) generate
   genmem_bram4: RAMB16_S4
      port map (
         DI     => DI,
         ADDR   => ADDR,
      	EN     => EN,
      	WE     => WE,
      	SSR    => SSR,
      	CLK    => CLK,
      	DO     => DO
   	);
   end generate;


-- ----------------------------------------------------------------------------
-- Port maping of 8bit blockram
   generate_bram9: if (BRAM_TYPE = 9) generate
   genmem_bram9: RAMB16_S9
      port map (
         DI     => DI(data_width-1 downto 0),
         DIP    => DI(data_width-1 + parity_width downto data_width),
         ADDR   => ADDR,
      	EN     => EN,
      	WE     => WE,
      	SSR    => SSR,
      	CLK    => CLK,
      	DO     => DO(data_width-1 downto 0),
         DOP    => DO(data_width-1 + parity_width downto data_width)
     	);
   end generate;

-- ----------------------------------------------------------------------------
-- Port maping of 16bit blockram
   generate_bram18: if (BRAM_TYPE = 18) generate
   genmem_bram18: RAMB16_S18
      port map (
         DI     => DI(data_width-1 downto 0),
         DIP    => DI(data_width-1 + parity_width downto data_width),
         ADDR   => ADDR,
      	EN     => EN,
      	WE     => WE,
      	SSR    => SSR,
      	CLK    => CLK,
      	DO     => DO(data_width-1 downto 0),
         DOP    => DO(data_width-1 + parity_width downto data_width)
     	);
   end generate;


-- ----------------------------------------------------------------------------
-- Port maping of 32bit blockram
   generate_bram36: if (BRAM_TYPE = 36) generate
   genmem_bram36:  RAMB16_S36
      port map (
         DI     => DI(data_width-1 downto 0),
         DIP    => DI(data_width-1 + parity_width downto data_width),
         ADDR   => ADDR,
        	EN     => EN,
        	WE     => WE,
        	SSR    => SSR,
        	CLK    => CLK,
        	DO     => DO(data_width-1 downto 0),
         DOP    => DO(data_width-1 + parity_width downto data_width)
       	);
   end generate;


end architecture SP_BMEM_BRAM_ARCH;

