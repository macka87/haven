-- dp_bmem_be.vhd: Byte enable supported BRAM memory cover
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;
use work.bmem_func.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity DP_BMEM_BE is
   generic(
      DATA_WIDTH  : integer;
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS       : integer;
      -- Output directly from BlockRams or throw register
      OUTPUT_REG  : TOUTPUT_REG := auto;
      -- debug prints
      DEBUG       : boolean := false
   );
   port(
      -- Common interface
      RESET       : in  std_logic; -- Reset only if output_reg

      -- Interface A
      CLKA        : in  std_logic; -- Clock A
      PIPE_ENA    : in  std_logic; -- Pipe Enable
      REA         : in  std_logic; -- Read Enable
      WEA         : in  std_logic; -- Write Enable
      BEA         : in  std_logic_vector((DATA_WIDTH/8)-1 downto 0);
      ADDRA       : in  std_logic_vector(log2(ITEMS)-1 downto 0); -- Address A
      DIA         : in  std_logic_vector(DATA_WIDTH-1 downto 0); -- Data A In
      DOA_DV      : out std_logic; -- Data A Valid
      DOA         : out std_logic_vector(DATA_WIDTH-1 downto 0); -- Data A Out

      -- Interface B
      CLKB        : in  std_logic; -- Clock B
      PIPE_ENB    : in std_logic; -- Pipe Enable
      REB         : in  std_logic; -- Read Enable
      WEB         : in  std_logic; -- Write Enable
      BEB         : in  std_logic_vector((DATA_WIDTH/8)-1 downto 0);
      ADDRB       : in  std_logic_vector(log2(ITEMS)-1 downto 0); -- Address B
      DIB         : in  std_logic_vector(DATA_WIDTH-1 downto 0); -- Data B In
      DOB_DV      : out std_logic; -- Data B Valid
      DOB         : out std_logic_vector(DATA_WIDTH-1 downto 0) -- Data B Out
   );
end entity DP_BMEM_BE;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of DP_BMEM_BE is
   -- ------------------ Constants declaration --------------------------------
   constant OUTPUT_REG_BOOL : boolean :=
                              BRAM_OUT_REG_TO_BOOL(OUTPUT_REG, (DATA_WIDTH/8));

   -- ------------------ Signals declaration ----------------------------------
   -- registers
   signal aux_wea_array    : std_logic_vector((DATA_WIDTH/8)-1 downto 0);
   signal aux_web_array    : std_logic_vector((DATA_WIDTH/8)-1 downto 0);
   signal reg_doa          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_doa_dv1      : std_logic;
   signal reg_doa_dv2      : std_logic;
   signal aux_doa          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_dob          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_dob_dv1      : std_logic;
   signal reg_dob_dv2      : std_logic;
   signal aux_dob          : std_logic_vector(DATA_WIDTH-1 downto 0);
begin
   
   -- generate auxiliary WEx arrays 
   GEN_WE_ARRAYS : for i in 0 to (DATA_WIDTH/8)-1 generate
      aux_wea_array(i) <= WEA and BEA(i);
      aux_web_array(i) <= WEB and BEB(i);
   end generate;

   GEN_8BIT_BRAMS : for i in 0 to (DATA_WIDTH/8)-1 generate
      DP_BMEM_I : entity work.DP_BMEM
         generic map(
            DATA_WIDTH  => 8,
            ITEMS       => ITEMS,
            BRAM_TYPE   => 9,
            OUTPUT_REG  => false,
            DEBUG       => DEBUG
         )
         port map(
            -- Common interface
            RESET       => RESET,
            -- Interface A
            CLKA        => CLKA,
            PIPE_ENA    => PIPE_ENA,
            REA         => REA,
            WEA         => aux_wea_array(i),
            ADDRA       => ADDRA,
            DIA         => DIA((i+1)*8-1 downto i*8),
            DOA_DV      => open,
            DOA         => aux_doa((i+1)*8-1 downto i*8),
            -- Interface B
            CLKB        => CLKB,
            PIPE_ENB    => PIPE_ENB,
            REB         => REB,
            WEB         => aux_web_array(i),
            ADDRB       => ADDRB,
            DIB         => DIB((i+1)*8-1 downto i*8),
            DOB_DV      => open,
            DOB         => aux_dob((i+1)*8-1 downto i*8)
         );

   end generate;

   -- ------------------------ Output registers -------------------------------
   GEN_OUTPUT_REG : if (OUTPUT_REG_BOOL) generate
      -- DOA Register
      process(RESET, CLKA)
      begin
         if (RESET = '1') then
            reg_doa     <= (others => '0');
            reg_doa_dv1 <= '0';
            reg_doa_dv2 <= '0';
         elsif (CLKA'event AND CLKA = '1') then
            if (PIPE_ENA = '1') then
               reg_doa     <= aux_doa;
               reg_doa_dv1 <= REA;
               reg_doa_dv2 <= reg_doa_dv1;
            end if;
         end if;
      end process;
   
      -- DOB Register
      process(RESET, CLKB)
      begin
         if (RESET = '1') then
            reg_dob     <= (others => '0');
            reg_dob_dv1 <= '0';
            reg_dob_dv2 <= '0';
         elsif (CLKB'event AND CLKB = '1') then
            if (PIPE_ENB = '1') then
              reg_dob     <= aux_dob;
              reg_dob_dv1 <= REB;
              reg_dob_dv2 <= reg_dob_dv1;
            end if;
         end if;
      end process;
   
      -- mapping registers to output
      DOA      <= reg_doa;
      DOB      <= reg_dob;
      DOA_DV   <= reg_doa_dv2;
      DOB_DV   <= reg_dob_dv2;

   end generate;

   -- --------------------- No Output registers -------------------------------
   GEN_NO_OUTPUT_REG : if (not OUTPUT_REG_BOOL) generate
      process(RESET, CLKA)
      begin
         if (RESET = '1') then
            DOA_DV <= '0';
         elsif (CLKA'event AND CLKA = '1') then
            if (PIPE_ENA = '1') then
               DOA_DV <= REA;
            end if;
         end if;
      end process;
   
      process(RESET, CLKB)
      begin
         if (RESET = '1') then
            DOB_DV <= '0';
         elsif (CLKB'event AND CLKB = '1') then
            if (PIPE_ENB = '1') then
               DOB_DV <= REB;
            end if;
         end if;
      end process;

      -- mapping multipex to output
      DOA  <= aux_doa;
      DOB  <= aux_dob;
   end generate;

end architecture full;
