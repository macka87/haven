--
-- test_dp_bmem.vhd: Component for testing dp_bmem.vhd
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
-- README: This component is useful only for testing. We can't test
--         generic components directly. It must be encapsulated into
--         not generic component.
--         You can change testing constant in test_param.vhd
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use work.math_pack.all;
use WORK.bmem_func.all; -- functions for enumerating generic parameters
use WORK.test_par.all;  -- constant for generic testing - TEST_*

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TEST_DP_BMEM is
   -- same interface like genmem_dp
   port(
      -- Common interface
      RESET  : in    std_logic;

      -- Interface A
      CLKA   : in    std_logic;
      PIPE_ENA : in  std_logic; -- Pipe Enable
      REA    : in    std_logic;
      WEA    : in    std_logic;
      ADDRA  : in    std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
      DIA    : in    std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
      DOA_DV : out   std_logic;
      DOA    : out   std_logic_vector(TEST_DATA_WIDTH-1 downto 0);

      -- Interface B
      CLKB   : in    std_logic;
      PIPE_ENB : in  std_logic; -- Pipe Enable
      REB    : in    std_logic;
      WEB    : in    std_logic;
      ADDRB  : in    std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
      DIB    : in    std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
      DOB_DV : out   std_logic;
      DOB    : out   std_logic_vector(TEST_DATA_WIDTH-1 downto 0)

   );
end entity TEST_DP_BMEM;




-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture TEST_DP_BMEM_ARCH of TEST_DP_BMEM is

component DP_BMEM
   generic(
      BRAM_TYPE   : integer;
      DATA_WIDTH  : integer;
      ITEMS : integer;
      OUTPUT_REG  : TOUTPUT_REG;
      DEBUG   : boolean
         );
   port(
      -- Common interface
      RESET  : in    std_logic;

      -- Interface A
      CLKA   : in    std_logic;
      PIPE_ENA : in  std_logic; -- Pipe Enable
      REA    : in    std_logic;
      WEA    : in    std_logic;
      ADDRA  : in    std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
      DIA    : in    std_logic_vector(DATA_WIDTH-1 downto 0);
      DOA_DV : out   std_logic; -- Data valid
      DOA    : out   std_logic_vector(DATA_WIDTH-1 downto 0);

      -- Interface B
      CLKB   : in    std_logic;
      PIPE_ENB : in  std_logic; -- Pipe Enable
      REB    : in    std_logic;
      WEB    : in    std_logic;
      ADDRB  : in    std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
      DIB    : in    std_logic_vector(DATA_WIDTH-1 downto 0);
      DOB_DV : out   std_logic; -- Data valid
      DOB    : out   std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end component;


begin
-- maping genmem_dp to TEST_GENMEM
genmem_dp_map: DP_BMEM
   generic map (
      BRAM_TYPE => TEST_BRAM_TYPE,
      DATA_WIDTH => TEST_DATA_WIDTH,
      ITEMS => TEST_ITEMS,
      OUTPUT_REG => TEST_OUTPUT_REG,
      DEBUG  => TEST_DEBUG
   )
   port map(
	   RESET => reset,
      -- Interface A
      CLKA => clka,
      PIPE_ENA => pipe_ena,
      REA => rea,
      WEA => wea,
      ADDRA => addra,
      DIA => dia,
      DOA_DV =>doa_dv,
      DOA => doa,
      -- Interface B
      CLKB => clkb,
      PIPE_ENB => pipe_enb,
      REB => reb,
      WEB => web,
      ADDRB => addrb,
      DIB => dib,
      DOB_DV =>  dob_dv,
      DOB => dob
   );
end architecture TEST_DP_BMEM_ARCH;

