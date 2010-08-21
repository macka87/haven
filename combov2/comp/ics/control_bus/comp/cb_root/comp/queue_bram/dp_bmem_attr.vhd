-- dp_bmem_attr.vhd: Dual port generic memory composed from Block Rams
-- Copyright (C) 2004 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--            Viktor Pus <pus@liberouter.org>
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
-- auxilarity functions and constant needed to evaluate generic address etc.
use WORK.math_pack.all;
use WORK.bmem_func.all;

-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity DP_BMEM_ATTR is
   -- Capacity of 1, 2, 4 Block rams is 16384 bits
   -- Capacity of 9, 18, 36 Block rams is 18432 bits
   generic(
      DATA_WIDTH  : integer;
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS : integer;
      -- Block Ram Type, only 1, 2, 4, 9, 18, 36 bits
      BRAM_TYPE   : integer := 4;
      -- Output directly from BlockRams or throw register
      -- TRUE, FALSE, AUTO (when column count > 1 then true)
      OUTPUT_REG  : TOUTPUT_REG := auto;
      -- debug prints
      DEBUG   : boolean := false
   );

   port(
      -- Common interface
      RESET  : in    std_logic; -- Reset only if output_reg

      -- Interface A
      CLKA   : in    std_logic; -- Clock A
      PIPE_ENA : in  std_logic; -- Pipe Enable
      REA    : in    std_logic; -- Read Enable
      WEA    : in    std_logic; -- Write Enable
      ADDRA  : in    std_logic_vector(LOG2(ITEMS)-1 downto 0); -- Address A
      DIA    : in    std_logic_vector(DATA_WIDTH-1 downto 0); -- Data A In
      DOA_DV : out   std_logic; -- Data A Valid
      DOA    : out   std_logic_vector(DATA_WIDTH-1 downto 0); -- Data A Out

      -- Interface B
      CLKB   : in    std_logic; -- Clock B
      PIPE_ENB : in  std_logic; -- Pipe Enable
      REB    : in    std_logic; -- Read Enable
      WEB    : in    std_logic; -- Write Enable
      ADDRB  : in    std_logic_vector(LOG2(ITEMS)-1 downto 0); -- Address B
      DIB    : in    std_logic_vector(DATA_WIDTH-1 downto 0); -- Data B In
      DOB_DV : out   std_logic; -- Data B Valid
      DOB    : out   std_logic_vector(DATA_WIDTH-1 downto 0) -- Data B Out
   );
end entity DP_BMEM_ATTR;





-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture DP_BMEM_ARCH of DP_BMEM_ATTR is


-- ------------- Generic Block Ram Component Declaration ----------------------
   component DP_BMEM_BRAM_ATTR
      generic(
         BRAM_TYPE : natural := 1  --only 1,2,4,8,18,36
      );

      port(
         DIA    : in std_logic_vector (BRAM_DATA_WIDTH(BRAM_TYPE)-1
                        + BRAM_PARITY_WIDTH(BRAM_TYPE) downto 0);
      	ADDRA  : in std_logic_vector (BRAM_ADDR_WIDTH(BRAM_TYPE)-1 downto 0);
      	ENA    : in std_logic;
      	WEA    : in std_logic;
      	SSRA   : in std_logic;
      	CLKA   : in std_logic;
      	DOA    : out std_logic_vector (BRAM_DATA_WIDTH(BRAM_TYPE)-1
                        + BRAM_PARITY_WIDTH(BRAM_TYPE) downto 0);
         --
      	DIB    : in std_logic_vector (BRAM_DATA_WIDTH(BRAM_TYPE)-1
                        + BRAM_PARITY_WIDTH(BRAM_TYPE) downto 0);
      	ADDRB  : in std_logic_vector (BRAM_ADDR_WIDTH(BRAM_TYPE)-1 downto 0);
      	ENB    : in std_logic;
      	WEB    : in std_logic;
      	SSRB   : in std_logic;
      	CLKB   : in std_logic;
      	DOB    : out std_logic_vector (BRAM_DATA_WIDTH(BRAM_TYPE)-1
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
   signal aux_addra               : std_logic_vector(FULL_ADDR-1 downto 0);
   signal wea_i               : std_logic_vector((BRAM_COLS-1) downto 0);
   signal ena_i               : std_logic;
   signal doa_i               : t_out_arr;
   signal doa_to_reg          : std_logic_vector(BRAM_ROWS*BRAM_TYPE-1 downto 0);
   signal reg_doa             : std_logic_vector(BRAM_ROWS*BRAM_TYPE-1 downto 0);
   signal reg_doa_dv1         : std_logic;
   signal reg_doa_dv2         : std_logic;

   -- aux signal data bram in out ... not all bits are maped in or out
   signal dia_to_bram       : std_logic_vector(BRAM_ROWS*BRAM_TYPE-1 downto 0);
   signal aux_doa           : std_logic_vector(BRAM_ROWS*BRAM_TYPE-1 downto 0);

  -- Port B internal signals
   signal aux_addrb               : std_logic_vector(FULL_ADDR-1 downto 0);
   signal web_i               : std_logic_vector((BRAM_COLS-1) downto 0);
   signal enb_i               : std_logic;
   signal dob_i               : t_out_arr;
   signal dob_to_reg          : std_logic_vector(BRAM_ROWS*BRAM_TYPE-1 downto 0);
   signal reg_dob             : std_logic_vector(BRAM_ROWS*BRAM_TYPE-1 downto 0);
   signal reg_dob_dv1         : std_logic;
   signal reg_dob_dv2         : std_logic;

   -- aux signal data bram in out ... not all bits are maped in or out
   signal aux_null          : std_logic_vector(BRAM_ROWS*BRAM_TYPE-DATA_WIDTH
                                                downto 0);
   signal aux_null_addr     : std_logic_vector(FULL_ADDR-REDUCED_FULL_ADDR
                                                                     downto 0);

   signal dib_to_bram       : std_logic_vector(BRAM_ROWS*BRAM_TYPE-1 downto 0);
   signal aux_dob           : std_logic_vector(BRAM_ROWS*BRAM_TYPE-1 downto 0);


   -- it isn't EXTR_ADDR-1 -> when EXTR_ADDR=0 -> -1 downto 0 ->can't translate
   signal reg_cols_addra      : std_logic_vector(EXTR_ADDR downto 0);
   signal reg_cols_addrb      : std_logic_vector(EXTR_ADDR downto 0);





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
-- memories enable
ena_i <= (REA or WEA) and (PIPE_ENA);
enb_i <= (REB or WEB) and (PIPE_ENB);


-- --------Maping data in to bram data in and data out to genmem out-----------
GEN_BRAM_DATA_IN1: if (DATA_WIDTH = (BRAM_ROWS*BRAM_TYPE)) generate
  dia_to_bram <= DIA;
  dib_to_bram <= DIB;
  DOA <= aux_doa;
  DOB <= aux_dob;
end generate;

GEN_BRAM_DATA_IN2: if (DATA_WIDTH /= (BRAM_ROWS*BRAM_TYPE)) generate
  aux_null <= (others =>'0');
  dia_to_bram <= aux_null(BRAM_ROWS*BRAM_TYPE-DATA_WIDTH-1 downto 0) & DIA;
  dib_to_bram <= aux_null(BRAM_ROWS*BRAM_TYPE-DATA_WIDTH-1 downto 0) & DIB;
  DOA <= aux_doa(DATA_WIDTH-1 downto 0);
  DOB <= aux_dob(DATA_WIDTH-1 downto 0);
end generate;


-- --------Maping address------------------------------------------------------
GEN_BRAM_ADDR1: if (REDUCED_FULL_ADDR = FULL_ADDR) generate
   aux_addra <= ADDRA;
   aux_addrb <= ADDRB;
end generate;

GEN_BRAM_ADDR2: if (REDUCED_FULL_ADDR /= FULL_ADDR) generate
   aux_null_addr <= (others =>'0');
   aux_addra <= aux_null_addr(FULL_ADDR-REDUCED_FULL_ADDR-1 downto 0)
                                                               & ADDRA;
   aux_addrb <= aux_null_addr(FULL_ADDR-REDUCED_FULL_ADDR-1 downto 0)
                                                               & ADDRB;
end generate;




-- --------- Generating and maping blockrams ----------------------------------
   ENMEM_ROW: for i in 0 to (BRAM_ROWS-1) generate
      GENMEM_COL: for j in 0 to (BRAM_COLS-1) generate
         GEN_BRAM_INST: DP_BMEM_BRAM_ATTR
            generic map (
               BRAM_TYPE =>  BRAM_TYPE
            )
            port map (
               DIA => dia_to_bram( (RAM_DATA_WIDTH-1+RAM_DATA_WIDTH*i) downto
                                 RAM_DATA_WIDTH*i),
               ADDRA => aux_addra(BRAM_ADDR-1 downto 0),
               ENA => ena_i,
               WEA => wea_i(j),
   	         SSRA => gnd,
   	         CLKA => CLKA,
   	         DOA => doa_i(j)( (RAM_DATA_WIDTH-1+RAM_DATA_WIDTH*i) downto
                                       RAM_DATA_WIDTH*i ),
               --
               DIB => dib_to_bram(RAM_DATA_WIDTH-1+RAM_DATA_WIDTH*i downto
                                 RAM_DATA_WIDTH*i),
               ADDRB => aux_addrb(BRAM_ADDR-1 downto 0),
               ENB => enb_i,
               WEB => web_i(j),
               SSRB => gnd,
               CLKB => CLKB,
               DOB => dob_i(j)( (RAM_DATA_WIDTH-1+RAM_DATA_WIDTH*i) downto
                                       RAM_DATA_WIDTH*i )
            );
      end generate;
   end generate;




-- ------------------ WEA Decoder ---------------------------------------------
   MORE_BRAMS1 : if (BRAM_COLS > 1) generate
   process(aux_addra, WEA)
   begin
      wea_i <= (others => '0');
      for i in 0 to (BRAM_COLS-1) loop
         if (conv_std_logic_vector(i, EXTR_ADDR) = aux_addra(FULL_ADDR-1
                                       downto FULL_ADDR-EXTR_ADDR)) then
            wea_i(i) <= WEA;
         end if;
      end loop;
   end process;
   end generate;

   ONE_BRAMS1 : if (BRAM_COLS = 1) generate
      wea_i(0) <= WEA;
   end generate;


-- ----------------- WEB Decoder ----------------------------------------------
   MORE_BRAMS2 : if (BRAM_COLS > 1) generate
   process(aux_addrb, WEB)
   begin
      web_i <= (others => '0');
      for i in 0 to (BRAM_COLS-1) loop
         if (conv_std_logic_vector(i, EXTR_ADDR) = aux_addrb(FULL_ADDR-1
                                       downto FULL_ADDR-EXTR_ADDR)) then
            web_i(i) <= WEB;
         end if;
      end loop;
   end process;
   end generate;

   ONE_BRAMS2 : if (BRAM_COLS = 1) generate
      web_i(0) <= WEB;
   end generate;


-- ------------------- Column address register --------------------------------
   MORE_BRAMS3 : if (BRAM_COLS > 1) generate
   -- Column addra register
   process(RESET, CLKA)
   begin
      if (RESET = '1') then
         reg_cols_addra <= (others => '0');
      elsif (CLKA'event AND CLKA = '1') then
         if (PIPE_ENA = '1') then
            reg_cols_addra(EXTR_ADDR-1 downto 0) <= aux_addra(FULL_ADDR-1
                                 downto BRAM_ADDR);
         end if;
      end if;
   end process;

   -- Column addrb register
   process(RESET, CLKB)
   begin
      if (RESET = '1') then
         reg_cols_addrb <= (others => '0');
      elsif (CLKB'event AND CLKB = '1') then
         if (PIPE_ENB = '1') then
            reg_cols_addrb(EXTR_ADDR-1 downto 0) <= aux_addrb(FULL_ADDR-1
                                 downto BRAM_ADDR);
         end if;
      end if;
   end process;
   end generate;



-- ------------------------ Output multipexors --------------------------------
   MORE_BRAMS4 : if (EXTR_ADDR > 0) generate
   -- DOA output multiplexor
   process(aux_addra, doa_i, reg_cols_addra)
   begin
      doa_to_reg <= (others => '0');
      for i in 0 to (BRAM_COLS-1) loop
         if (conv_std_logic_vector(i, EXTR_ADDR) = reg_cols_addra) then
            doa_to_reg <= doa_i(i);
         end if;
      end loop;
   end process;

   -- DOB output multiplexor
   process(aux_addrb, dob_i, reg_cols_addrb)
   begin
      dob_to_reg <= (others => '0');
      for i in 0 to (BRAM_COLS-1) loop
         if (conv_std_logic_vector(i, EXTR_ADDR) = reg_cols_addrb) then
            dob_to_reg <= dob_i(i);
         end if;
      end loop;
   end process;
   end generate;

   ONE_BRAMS4 : if (EXTR_ADDR = 0) generate
      -- when one column no output multiplexor
      doa_to_reg <= doa_i(0);
      dob_to_reg <= dob_i(0);
   end generate;




-- ------------------------ Output registers ----------------------------------
   OUTPUTREG : if (OUTPUT_REG_BOOL) generate
   -- DOA Register
   process(RESET, CLKA)
   begin
      if (RESET = '1') then
         reg_doa     <= (others => '0');
         reg_doa_dv1 <= '0';
         reg_doa_dv2 <= '0';
      elsif (CLKA'event AND CLKA = '1') then
         if (PIPE_ENA = '1') then
            reg_doa     <= doa_to_reg;
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
           reg_dob     <= dob_to_reg;
           reg_dob_dv1 <= REB;
           reg_dob_dv2 <= reg_dob_dv1;
         end if;
      end if;
   end process;

 -- mapping registers to output
   aux_doa <= reg_doa;
   aux_dob <= reg_dob;
   DOA_DV <= reg_doa_dv2;
   DOB_DV <= reg_dob_dv2;
   end generate;


-- --------------------- No Output registers ----------------------------------
   NOOUTPUTREG : if not OUTPUT_REG_BOOL generate
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
   aux_doa <= doa_to_reg;
   aux_dob <= dob_to_reg;
   end generate;

end architecture DP_BMEM_ARCH;
