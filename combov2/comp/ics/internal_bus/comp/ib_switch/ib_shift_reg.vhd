--
-- ib_shift_reg.vhd: Internal Bus Shift Register
-- Copyright (C) 2006 CESNET
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
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_SHIFT_REG is
   generic (
      DATA_WIDTH       : integer:=64
      );
   port(
      -- Common Interface
      CLK          : in  std_logic;
      RESET        : in  std_logic;

      -- Input Interface
      DATA_IN      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      SOP_IN       : in  std_logic;
      EOP_IN       : in  std_logic;
      DATA_IN_VLD  : in  std_logic;
      WR_EN        : in  std_logic;
      DST_RDY      : out std_logic;

      --Output Interface
      DATA_OUT     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DATA_OUT_VLD : out std_logic;
      SOP_OUT      : out std_logic;
      EOP_OUT      : out std_logic;
      OUT_FSM_RDY  : in  std_logic
      );
end entity IB_SHIFT_REG;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_SHIFT_REG_ARCH of IB_SHIFT_REG is

-- Signal Declaration ---------------------------------------------------------
   signal srl_data_in     : std_logic_vector(DATA_WIDTH-1 downto 0); 
   signal srl_data_out    : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal srl_en          : std_logic;
   signal srl_addr        : std_logic_vector(3 downto 0);
   signal counter         : std_logic_vector(2 downto 0);
   signal cntr_reg_up     : std_logic;
   signal cntr_reg_down   : std_logic;
   signal eop_shift_reg0  : std_logic;
   signal eop_shift_reg1  : std_logic;
   signal sop_shift_reg0  : std_logic;
   signal sop_shift_reg1  : std_logic;

-- component declaration ------------------------------------------------------
component SRL16E
   generic(
      INIT : bit_vector(15 downto 0) := X"0000"
   );
   port (
      D    : in std_logic;
      CE   : in std_logic;
      CLK  : in std_logic;
      A0   : in std_logic;
      A1   : in std_logic;
      A2   : in std_logic;
      A3   : in std_logic;
      Q    : out std_logic
   );
end component;


begin
DST_RDY      <= '1' when counter(0) = '1' or OUT_FSM_RDY = '1' else '0';
DATA_OUT     <= srl_data_out(DATA_WIDTH-1 downto 0);
EOP_OUT      <= eop_shift_reg1 when (counter(2) = '1') else eop_shift_reg0;
SOP_OUT      <= sop_shift_reg1 when (counter(2) = '1') else sop_shift_reg0;
DATA_OUT_VLD <= not counter(0); -- Not empty
srl_data_in  <= DATA_IN;
srl_en       <= DATA_IN_VLD and WR_EN;
srl_addr     <= "0001" when (counter(2) = '1') else "0000";

-- Count Up when DATA_IN_VLD and (DST_NOT_RDY or Counter = 0)
cntr_reg_up   <= '1' when (DATA_IN_VLD = '1' and WR_EN='1' and (OUT_FSM_RDY = '0' or counter(0) = '1') ) else '0';
-- Count Down when OUT_FSM_RDY and DATA_IN_NOT_VLD and Counter > 0
cntr_reg_down <= '1' when (OUT_FSM_RDY = '1' and (DATA_IN_VLD = '0' or  WR_EN='0') and counter(0) = '0') else '0';

-- data couner ------------------------------------------------------------------
-- Actual count of item in SHR
datacounterp: process(RESET, CLK)
begin
   if (RESET = '1') then
      counter <= "001";
   else
      if (CLK'event AND CLK = '1') then
         if (cntr_reg_up = '1') then
            counter(0)  <= '0';
            counter(1)  <= counter(0);
            counter(2)  <= counter(1);
         end if;
         if (cntr_reg_down = '1') then
            counter(0)  <= counter(1);
            counter(1)  <= counter(2);
            counter(2)  <= '0';
         end if;
      end if;  
   end if;
end process;

-- Due to problems with SRL16E Output Delay (3 ns)
-- register eop_shift_reg ------------------------------------------------------
eop_shift_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      eop_shift_reg0 <= '0';
      eop_shift_reg1 <= '0';
   else 
      if (CLK'event AND CLK = '1') then
         if (srl_en = '1') then
            eop_shift_reg0 <= EOP_IN;
            eop_shift_reg1 <= eop_shift_reg0;
         end if;
      end if;
   end if;
end process;

-- Due to problems with SRL16E Output Delay (3 ns)
-- register eop_shift_reg ------------------------------------------------------
sop_shift_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      sop_shift_reg0 <= '0';
      sop_shift_reg1 <= '0';
   else 
      if (CLK'event AND CLK = '1') then
         if (srl_en = '1') then
            sop_shift_reg0 <= SOP_IN;
            sop_shift_reg1 <= sop_shift_reg0;
         end if;
      end if;
   end if;
end process;

-- ----------------------------------------------------------------------------
-- Generate Shift Register
SH_REG_GEN : for i in 0 to DATA_WIDTH-1 generate
  U_SRL16E: SRL16E
    generic map (
      INIT => X"0000"
    )
    port map (
	   D      => srl_data_in(i),
	   CE     => srl_en,
	   CLK    => CLK,
	   A0     => srl_addr(0),
	   A1     => srl_addr(1),
	   A2     => srl_addr(2),
	   A3     => srl_addr(3),
	   Q      => srl_data_out(i)
      );
end generate;

end architecture IB_SHIFT_REG_ARCH;

