--
-- sp_bmem.vhd: Single port generic memory composed from Block Rams
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
-- auxilarity functions and constant needed to evaluate generic address etc.
use WORK.bmem_func.all;

-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture SP_BMEM_ARCH of SP_BMEM is


-- ------------- Generic Block Ram Component Declaration ----------------------
   component SP_BMEM_BRAM
      generic(
         BRAM_TYPE : natural
      );

      port(
         DI    : in std_logic_vector (BRAM_DATA_WIDTH(BRAM_TYPE)-1
                        + BRAM_PARITY_WIDTH(BRAM_TYPE) downto 0);
      	ADDR  : in std_logic_vector (BRAM_ADDR_WIDTH(BRAM_TYPE)-1 downto 0);
      	EN    : in std_logic;
      	WE    : in std_logic;
      	SSR   : in std_logic;
      	CLK   : in std_logic;
      	DO    : out std_logic_vector (BRAM_DATA_WIDTH(BRAM_TYPE)-1
                        + BRAM_PARITY_WIDTH(BRAM_TYPE) downto 0)
         );
   end component;



-- -------------- Constants declaration ---------------------------------------
   -- Block Rams rows count
   constant BRAM_ROWS      : integer := BRAM_ROWS_COUNT(BRAM_TYPE,DATA_WIDTH);
   -- Block Rams cols count
   constant BRAM_COLS      : integer := BRAM_COLUMN_COUNT(BRAM_TYPE, ITEMS);
   -- Extra address bits for addresing cols
   constant EXTR_ADDR      : integer := COLUMN_ADDR_WIDTH(BRAM_COLS);
   -- Block Ram address bits
   constant BRAM_ADDR      : integer := BRAM_ADDR_WIDTH(BRAM_TYPE);
   -- Full address bits = extra + normal address
   constant FULL_ADDR      : integer := EXTR_ADDR + BRAM_ADDR;
   --Address width of generic memory reduced by needed items
   constant REDUCED_FULL_ADDR : integer := LOG2(ITEMS);
   -- Block Ram Data Width = data input + parity input
   constant RAM_DATA_WIDTH : integer := BRAM_DATA_WIDTH(BRAM_TYPE)
                                        + BRAM_PARITY_WIDTH(BRAM_TYPE);
   constant OUTPUT_REG_BOOL : boolean :=
                              BRAM_OUT_REG_TO_BOOL(OUTPUT_REG, BRAM_COLS);


-- ------------------ Types declaration ---------------------------------------
   -- Output array from each column - it will be multiplexed
   type t_out_arr is array (0 to (BRAM_COLS-1)) of
                          std_logic_vector(BRAM_ROWS*BRAM_TYPE-1 downto 0);





-- ------------------ Signals declaration -------------------------------------
   signal gnd : std_logic; -- Ground

-- Port A internal signals
   signal aux_addr           : std_logic_vector(FULL_ADDR-1 downto 0);
   signal we_i               : std_logic_vector(BRAM_COLS-1 downto 0);
   signal en_i               : std_logic;
   signal do_i               : t_out_arr;
   signal do_to_reg          : std_logic_vector(BRAM_ROWS*BRAM_TYPE-1 downto 0);
   signal reg_do             : std_logic_vector(BRAM_ROWS*BRAM_TYPE-1 downto 0);
   signal reg_do_dv1         : std_logic;
   signal reg_do_dv2         : std_logic;

  -- aux signal data bram in out ... not all bits are maped in or out
   signal aux_null          : std_logic_vector(BRAM_ROWS*BRAM_TYPE-DATA_WIDTH
                                                downto 0);
   signal aux_null_addr     : std_logic_vector(FULL_ADDR-REDUCED_FULL_ADDR
                                                                    downto 0);
   signal di_to_bram       : std_logic_vector(BRAM_ROWS*BRAM_TYPE-1 downto 0);
   signal aux_do           : std_logic_vector(BRAM_ROWS*BRAM_TYPE-1 downto 0);


   -- it isn't EXTR_ADDR-1 -> when EXTR_ADDR=0 -> -1 downto 0 ->can't translate
   signal reg_cols_addr      : std_logic_vector(EXTR_ADDR downto 0);

begin




-- ----------------- Writing informations about structure ---------------------
GEN_DEBUG: if (DEBUG) generate
  -- pragma translate_off
  assert false report "BRAM_ROWS: " & integer'image(BRAM_ROWS) severity note;
  assert false report "BRAM_COLS: " & integer'image(BRAM_COLS) severity note;
  assert false report "EXTR_ADDR: " & integer'image(EXTR_ADDR) severity note;
  assert false report "BRAM_ADDR: " & integer'image(BRAM_ADDR) severity note;
  assert false report "FULL_ADDR: " & integer'image(FULL_ADDR) severity note;
  assert false report "REDUCED_FULL_ADDR: " & integer'image(REDUCED_FULL_ADDR)
      severity note;
  assert false report "OUTPU_REG: " & boolean'image(OUTPUT_REG_BOOL)
      severity note;
  assert false report "RAM_DATA_WIDTH: " & integer'image(RAM_DATA_WIDTH)
      severity note;
  -- pragma translate_on
end generate;




gnd <= '0'; -- Ground
en_i <= (RE or WE); --and (PIPE_EN);


-- --------Maping data in to bram data in and data out to genmem out-----------
GEN_BRAM_DATA_IN1: if (DATA_WIDTH = (BRAM_ROWS*BRAM_TYPE)) generate
  di_to_bram <= DI;
  DO <= aux_do;
end generate;

GEN_BRAM_DATA_IN2: if (DATA_WIDTH /= (BRAM_ROWS*BRAM_TYPE)) generate
  aux_null <= (others =>'0');
  di_to_bram <= aux_null(BRAM_ROWS*BRAM_TYPE-DATA_WIDTH-1 downto 0) & DI;
  DO <= aux_do(DATA_WIDTH-1 downto 0);
end generate;


-- --------Maping address------------------------------------------------------
GEN_BRAM_ADDR1: if (REDUCED_FULL_ADDR = FULL_ADDR) generate
   aux_addr <= ADDR;
end generate;

GEN_BRAM_ADDR2: if (REDUCED_FULL_ADDR /= FULL_ADDR) generate
   aux_null_addr <= (others =>'0');
   aux_addr <= aux_null_addr(FULL_ADDR-REDUCED_FULL_ADDR-1 downto 0)
                                                               & ADDR;
end generate;




-- --------- Generating and maping blockrams ----------------------------------
   ENMEM_ROW: for i in 0 to (BRAM_ROWS-1) generate
      GENMEM_COL: for j in 0 to (BRAM_COLS-1) generate
         GEN_BRAM_INST: SP_BMEM_BRAM
            generic map (
               BRAM_TYPE =>  BRAM_TYPE
            )
            port map (
               DI => di_to_bram( (RAM_DATA_WIDTH-1+RAM_DATA_WIDTH*i) downto
                                 RAM_DATA_WIDTH*i),
               ADDR => aux_addr(BRAM_ADDR-1 downto 0),
               EN => en_i,
               WE => we_i(j),
   	         SSR => gnd,
   	         CLK => CLK,
   	         DO => do_i(j)( (RAM_DATA_WIDTH-1+RAM_DATA_WIDTH*i) downto
                                       RAM_DATA_WIDTH*i )
               );
      end generate;
   end generate;




-- ------------------ WEA Decoder ---------------------------------------------
   MORE_BRAMS1 : if (BRAM_COLS > 1) generate
   process(aux_addr, WE)
   begin
      we_i <= (others => '0');
      for i in 0 to (BRAM_COLS-1) loop
         if (conv_std_logic_vector(i, EXTR_ADDR) = aux_addr(FULL_ADDR-1
                                       downto FULL_ADDR-EXTR_ADDR)) then
            we_i(i) <= WE;
         end if;
      end loop;
   end process;
   end generate;

   ONE_BRAMS1 : if (BRAM_COLS = 1) generate
      we_i(0) <= WE;
   end generate;


-- ------------------- Column address register --------------------------------
   MORE_BRAMS2 : if (BRAM_COLS > 1) generate
   -- Column addra register
   process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_cols_addr <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         reg_cols_addr(EXTR_ADDR-1 downto 0) <= aux_addr(FULL_ADDR-1 downto
                                                            BRAM_ADDR);
      end if;
   end process;
   end generate;


-- ------------------------ Output multipexors --------------------------------
   MORE_BRAMS3 : if (EXTR_ADDR > 0) generate
   -- DOA output multiplexor
   process(aux_addr, do_i)
   begin
      do_to_reg <= (others => '0');
      for i in 0 to (BRAM_COLS-1) loop
         if (conv_std_logic_vector(i, EXTR_ADDR) = reg_cols_addr) then
            do_to_reg <= do_i(i);
         end if;
      end loop;
   end process;
   end generate;

   ONE_BRAMS3 : if (EXTR_ADDR = 0) generate
      -- when one column no output multiplexor
      do_to_reg <= do_i(0);
   end generate;




-- ------------------------ Output registers ----------------------------------
   OUTPUTREG : if (OUTPUT_REG_BOOL) generate
   -- DOA Register
   process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_do     <= (others => '0');
         reg_do_dv1 <= '0';
         reg_do_dv2 <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (PIPE_EN = '1') then
            reg_do     <= do_to_reg;
            reg_do_dv1 <= RE and PIPE_EN; -- delay data valid for one period
            reg_do_dv2 <= reg_do_dv1;
         end if;
      end if;
   end process;

   -- mapping registers to output
   aux_do <= reg_do;
   DO_DV <= reg_do_dv2;
   end generate;


-- --------------------- No Output registers ----------------------------------
   NOOUTPUTREG : if not OUTPUT_REG_BOOL generate
   process(RESET, CLK)
   begin
      if (RESET = '1') then
         DO_DV <= '0';
      elsif (CLK'event AND CLK = '1') then
         DO_DV <= RE; -- synchronize with clock
      end if;
   end process;
       -- mapping multipex to output
   aux_do <= do_to_reg;
   end generate;


end architecture SP_BMEM_ARCH;
