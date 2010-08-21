-- tsu_cv2_core.vhd: core component of GPS synchronized timestamp unit
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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
-- TODO:
-- 

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

Library UNISIM;
use UNISIM.vcomponents.all;

Library UNIMACRO;
use UNIMACRO.vcomponents.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity tsu_cv2_core is
 generic (
   REGISTER_TS_OUTPUT : boolean := false
 );
 -- PORTS
 port (
   -- Clock and reset signals for MI_32 interface
   MI32_CLK       : in std_logic;
   MI32_RESET     : in std_logic;

   -- In / Out SW interface via MI_32
   DWR            : in std_logic_vector(31 downto 0);
   ADDR           : in std_logic_vector(31 downto 0);
   RD             : in std_logic;
   WR             : in std_logic;
   BE             : in std_logic_vector(3 downto 0);
   DRD            : out std_logic_vector(31 downto 0);
   ARDY           : out std_logic;
   DRDY           : out std_logic;

   -- Input PPS_N signal
   PPS_N         : in std_logic;

   -- TSU core clock
   TSU_CORE_CLK   : in std_logic;
   TSU_CORE_RESET : in std_logic;

   -- Output pacodag interface
   TS             : out std_logic_vector(63 downto 0);
   TS_DV          : out std_logic  -- timestamp is valid (one cycle), depends on INTA reg
 );
end tsu_cv2_core;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of tsu_cv2_core is
   -- Register signals
   signal reg_realtime            : std_logic_vector(95 downto 0);
   signal incr_value              : std_logic_vector(38 downto 0);
   signal reg_pulsepsec           : std_logic_vector(95 downto 0);
   signal reg_write               : std_logic;
   signal core_reg_ts_dv          : std_logic;
   signal second_reg_realtime     : std_logic_vector(63 downto 0);
   signal second_reg_ts_dv        : std_logic;

   -- Direction of data flow
   signal core_reg_mi_data_input  : std_logic_vector(95 downto 0);

   -- MI32 interface signals
   signal ardy_mux_out            : std_logic;
   signal ardy_reg_cntrl_mux_in   : std_logic;
   signal ardy_inta_mux_in        : std_logic;
   signal ardy_reg_core_reg_mux_in : std_logic;
   signal drdy_input_async        : std_logic;
   signal drdy_input_sync         : std_logic;

   -- Common MI32 register
   signal core_reg_mi_data_low        : std_logic_vector(31 downto 0);
   signal core_reg_mi_data_middle     : std_logic_vector(31 downto 0);
   signal core_reg_mi_data_high       : std_logic_vector(31 downto 0);
   signal mi_reg_mi_data_low          : std_logic_vector(31 downto 0);
   signal mi_reg_mi_data_middle       : std_logic_vector(31 downto 0);
   signal mi_reg_mi_data_high         : std_logic_vector(31 downto 0);

   -- MI32 control register
   signal mi_reg_cntrl            : std_logic_vector(2 downto 0);

   -- MUX select signals
   signal sel_reg_rtr_rd          : std_logic;
   signal sel_reg_rtr_wr          : std_logic;
   signal sel_reg_incr_val_rd     : std_logic;
   signal sel_reg_incr_val_wr     : std_logic;
   signal sel_reg_pulsepsec_wr    : std_logic;
   signal sel_reg_mi_data_low     : std_logic;
   signal sel_reg_mi_data_middle  : std_logic;
   signal sel_reg_mi_data_high    : std_logic;
   signal sel_reg_cntrl           : std_logic;
   signal sel_reg_inta            : std_logic;

   -- Write enable signals
   signal reg_rtr_we_0            : std_logic;
   signal reg_rtr_we_1            : std_logic;
   signal reg_rtr_we_2            : std_logic;
   signal reg_incr_val_we         : std_logic;
   signal core_reg_cntrl_write    : std_logic;
   signal core_reg_mi_data_low_we : std_logic;
   signal core_reg_mi_data_middle_we : std_logic;
   signal core_reg_mi_data_high_we : std_logic;
   signal core_reg_ts_dv_we       : std_logic;
   signal mi_reg_ts_dv_we         : std_logic;
   signal mi_reg_cntrl_we         : std_logic;
   signal mi_reg_mi_data_low_we : std_logic;
   signal mi_reg_mi_data_middle_we : std_logic;
   signal mi_reg_mi_data_high_we : std_logic;

   signal pps_wr_en               : std_logic;

   -- Read enable signals

   signal drd_mux_addr            : std_logic_vector(1 downto 0);
   signal drdy_mux_addr           : std_logic;

   signal drd_input               : std_logic_vector(31 downto 0);
   signal ardy_mux_addr           : std_logic_vector(2 downto 0);

   -- DSP48 signals
   signal add_result : std_logic_vector(95 downto 0);
   signal add_result_low_0 : std_logic_vector(47 downto 0);
   signal add_result_low_1 : std_logic_vector(47 downto 0);
   signal add_input_low : std_logic_vector(47 downto 0);
   signal add_input_high : std_logic_vector(47 downto 0);
   signal add_result_high_0 : std_logic_vector(47 downto 0);
   signal add_result_high_1 : std_logic_vector(47 downto 0);
   signal extended_incr : std_logic_vector(47 downto 0);
   signal carry : std_logic;
   signal b_input : std_logic_vector(47 downto 0);

begin

-- ----------------------------------------------------------------------------
--                            TSU CORE CLK DOMAIN
-- ----------------------------------------------------------------------------
-- If REGISTER_TS_OUTPUT is set to TRUE - register TS and TS_DV for one more time
registered_ts : if REGISTER_TS_OUTPUT = true generate
   registered_ts_process : process(TSU_CORE_CLK)
   begin
      if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
         second_reg_realtime <= reg_realtime(95 downto 32);
         second_reg_ts_dv <= core_reg_ts_dv;
      end if;
   end process;

   TS    <= second_reg_realtime;
   TS_DV <= second_reg_ts_dv;
end generate registered_ts;

-- Else connect them directly to output
not_registered_ts : if REGISTER_TS_OUTPUT = false generate
   TS    <= reg_realtime(95 downto 32);
   TS_DV <= core_reg_ts_dv;
end generate not_registered_ts;

-- -------------------------------------------------------
-- TS_DV register (if set, timestamp is assumed as valid) (INTA register)
-- mi -> tsu_core
core_ts_dv_register : process(TSU_CORE_CLK)
begin
   if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
      if (TSU_CORE_RESET = '1') then
         core_reg_ts_dv <= '0';
      elsif (core_reg_ts_dv_we = '1' and BE(0) = '1') then
         core_reg_ts_dv <= DWR(0); --mi_reg_ts_dv;
      end if;
   end if;
end process;

-- --------------------------------------------------------------------------------
--   BASIC THREE RESISTERS OF THE TIMESTAMP UNIT WHICH PRESERVE TIME INFORMATION
-- --------------------------------------------------------------------------------

-- -------------------------------------------------------
-- RTR (real-time register)
reg_rtr : process(TSU_CORE_CLK)
begin
   if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
      if (reg_rtr_we_0 = '1') then
         reg_realtime <= mi_reg_mi_data_high & mi_reg_mi_data_middle & mi_reg_mi_data_low;
      else
         reg_realtime <= add_result;
      end if;
   end if;
end process;

add_result <= add_result_high_1 & add_result_low_1;

-- -------------------------------------------------------
-- Registered rtr_we signal
reg_rtr_we_register : process(TSU_CORE_CLK)
begin
   if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
      reg_rtr_we_1 <= reg_rtr_we_0;
      reg_rtr_we_2 <= reg_rtr_we_1;
   end if;
end process;

-- -------------------------------------------------------
-- -------------------------------------------------------
-- First adder branch
-- -------------------------------------------------------
-- Multiplexor for first dsp adder
first_adder_input_mux : process(reg_rtr_we_1, reg_realtime, add_result_low_0)
begin
   case (reg_rtr_we_1) is
      when '1' => add_input_low <= reg_realtime(47 downto 0);
      when others => add_input_low <= add_result_low_0;
   end case;
end process;

extended_incr <= X"00" & '0' & incr_value;

-- -------------------------------------------------------
-- First adder
ADDSUB_MACRO_inst_low : ADDSUB_MACRO
generic map (
   DEVICE => "VIRTEX5", -- Target Device: "VIRTEX5", "VIRTEX6", "SPARTAN6" 
   LATENCY => 1,        -- Desired clock cycle latency, 0-2
   WIDTH => 48)         -- Input / Output bus width, 1-48
port map (
   CARRYOUT => carry, -- 1-bit carry-out output signal
   RESULT => add_result_low_0,   -- Add/sub result output, width defined by WIDTH generic
   A => add_input_low,       -- Input A bus, width defined by WIDTH generic
   ADD_SUB => '1',   -- 1-bit add/sub input, high selects add, low selects subtract
   B => extended_incr,               -- Input B bus, width defined by WIDTH generic
   CARRYIN => '0',   -- 1-bit carry-in input
   CE => '1',             -- 1-bit clock enable input
   CLK => TSU_CORE_CLK,  -- 1-bit clock input
   RST => TSU_CORE_RESET      -- 1-bit active high synchronous reset
);

-- -------------------------------------------------------
-- Register for first adder branch
first_adder_branch_reg : process(TSU_CORE_CLK)
begin
   if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
      add_result_low_1 <= add_result_low_0;
   end if;
end process;

-- -------------------------------------------------------
-- -------------------------------------------------------
-- Second adder branch
-- -------------------------------------------------------
-- Register for second adder branch
second_adder_branch_reg : process(TSU_CORE_CLK)
begin
   if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
      add_result_high_0 <= reg_realtime(95 downto 48);
   end if;
end process;
 
-- -------------------------------------------------------
-- Multiplexor for second dsp adder
second_adder_input_mux : process(reg_rtr_we_2, add_result_high_0, add_result_high_1)
begin
   case (reg_rtr_we_2) is
      when '1' => add_input_high <= add_result_high_0;
      when others => add_input_high <= add_result_high_1;
   end case;
end process;

-- -------------------------------------------------------
-- Second adder
ADDSUB_MACRO_inst_high : ADDSUB_MACRO
generic map (
   DEVICE => "VIRTEX5", -- Target Device: "VIRTEX5", "VIRTEX6", "SPARTAN6" 
   LATENCY => 1,        -- Desired clock cycle latency, 0-2
   WIDTH => 48)         -- Input / Output bus width, 1-48
port map (
   CARRYOUT => open, -- 1-bit carry-out output signal
   RESULT => add_result_high_1,    -- Add/sub result output, width defined by WIDTH generic
   A => add_input_high,       -- Input A bus, width defined by WIDTH generic
   ADD_SUB => '1',   -- 1-bit add/sub input, high selects add, low selects subtract
   B => b_input,               -- Input B bus, width defined by WIDTH generic
   CARRYIN => '0',   -- 1-bit carry-in input
   CE => '1',             -- 1-bit clock enable input
   CLK => TSU_CORE_CLK,  -- 1-bit clock input
   RST => TSU_CORE_RESET      -- 1-bit active high synchronous reset
);

b_input <= X"00000000000" & "000" & carry;

-- --------------------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- --------------------------------------------------------------------------------
-- INCR_REG - Incremental value register
reg_incr_value : process(TSU_CORE_CLK)
begin
   if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
      if (reg_incr_val_we = '1') then
         incr_value <= mi_reg_mi_data_middle(6 downto 0) & mi_reg_mi_data_low;
      end if;
   end if;
end process reg_incr_value;

-- -------------------------------------------------------
-- PPS_REG (puls per second register). Due to inverted
-- PPS_N signal we save RTR on descending edge of PPS_N
reg_pulseps : process(TSU_CORE_CLK)
begin
   if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
      if (PPS_N = '0' and pps_wr_en = '1') then
         reg_pulsepsec <= reg_realtime;
      end if;
   end if;
end process;

-- -------------------------------------------------------
-- Register for enabling write into reg_pulseps register
reg_pps_en : process(TSU_CORE_CLK)
begin
   if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
      pps_wr_en <= PPS_N;
   end if;
end process;

-- --------------------------------------------------------------------------------


-- --------------------------------------------------------------------------------
-- Write into control register indicator
reg_write_req : process(TSU_CORE_CLK)
begin
   if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
      if (core_reg_cntrl_write = '1') then
         reg_write <= '1';
      else
         reg_write <= '0';
      end if;
   end if;
end process reg_write_req;

-- --------------------------------------------------------------------------------
-- Choose register by address in reg_cntrl
select_register : process(mi_reg_cntrl)
begin
   -- Implicit values of select
   sel_reg_rtr_rd <= '0';
   sel_reg_rtr_wr <= '0';
   sel_reg_incr_val_rd <= '0';
   sel_reg_incr_val_wr <= '0';
   sel_reg_pulsepsec_wr <= '0';

   case (mi_reg_cntrl) is
      when "000" => sel_reg_incr_val_rd <= '1';    -- PCI -> Incrementation register chosen
      when "001" => sel_reg_rtr_rd <= '1';         -- PCI -> RTR register
 --     when "010" => sel_reg_ <= '1';         -- PCI -> TSR register
 --     when "011" => sel_reg_ <= '1';         -- PCI -> REG_PPS
      when "100" => sel_reg_incr_val_wr <= '1';    -- Iincrementation reg. -> PCI
      when "101" => sel_reg_rtr_wr <= '1';         -- RTR -> PCI
--      when "110" => sel_reg_ <= '1';         -- TSR -> PCI
      when "111" => sel_reg_pulsepsec_wr <= '1';   -- REG_PPS -> PCI
      when others => null;
   end case;

end process select_register;

-- --------------------------------------------------------------------------------
-- Set write enable into register   
  reg_rtr_we_0            <= sel_reg_rtr_rd and reg_write;
  reg_incr_val_we         <= sel_reg_incr_val_rd and reg_write; 

-- -------------------------------------------------------
-- MI32 common data register low
core_reg_mi_common_data_low : process(TSU_CORE_CLK)
begin
   if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
      if (core_reg_mi_data_low_we = '1') then
         core_reg_mi_data_low <= core_reg_mi_data_input(31 downto 0);
      end if;
   end if;
end process;

-- -------------------------------------------------------
-- MI32 common data register middle
core_reg_mi_common_data_middle : process(TSU_CORE_CLK)
begin
   if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
      if (core_reg_mi_data_middle_we = '1') then
         core_reg_mi_data_middle <= core_reg_mi_data_input(63 downto 32);
      end if;
   end if;
end process;

-- -------------------------------------------------------
-- MI32 common data register high
core_reg_mi_common_data_high : process(TSU_CORE_CLK)
begin
   if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
      if (core_reg_mi_data_high_we = '1') then
         core_reg_mi_data_high <= core_reg_mi_data_input(95 downto 64);
      end if;
   end if;
end process;

-- --------------------------------------------------------------------------------
-- Write to core_reg_mi_common_data mux
to_core_reg_mi_common_data_mux : process(mi_reg_cntrl(1 downto 0), incr_value, reg_realtime, reg_pulsepsec)
begin
   core_reg_mi_data_input <= (others => '0');

   case (mi_reg_cntrl(1 downto 0)) is
      when "00" => core_reg_mi_data_input(38 downto 0) <= incr_value;  -- Iincrementation reg. -> PCI
      when "01" => core_reg_mi_data_input <= reg_realtime;             -- RTR -> PCI
--      when "10" => sel_reg_ <= '1';         -- TSR -> PCI
      when "11" => core_reg_mi_data_input <= reg_pulsepsec;            -- REG_PPS -> PCI
      when others => null;
   end case;
end process;

-- ----------------------------------------------------------------------------
--                              MI32 CLK DOMAIN
-- ----------------------------------------------------------------------------
ARDY <= ardy_mux_out;

-- -------------------------------------------------------
-- Register for control where data from/to MI32 bus should go, CNTRL_REG
-- mi -> tsu_core
mi_reg_control : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      if (mi_reg_cntrl_we = '1') then
         if (BE(0) = '1') then mi_reg_cntrl <= DWR(2 downto 0); end if;
      end if;
   end if;
end process;

-- -------------------------------------------------------
-- MI32 common data register low
mi_reg_mi_common_data_low : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      if (mi_reg_mi_data_low_we = '1') then
         for i in 0 to BE'high loop
            if BE(i) = '1' then
               mi_reg_mi_data_low(8*i+7 downto 8*i) <= DWR(8*i+7 downto 8*i);
            end if;
         end loop;
      end if;
   end if;
end process;

-- -------------------------------------------------------
-- MI32 common data register middle
mi_reg_mi_common_data_middle : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      if (mi_reg_mi_data_middle_we = '1') then
         for i in 0 to BE'high loop
            if BE(i) = '1' then
               mi_reg_mi_data_middle(8*i+7 downto 8*i) <= DWR(8*i+7 downto 8*i);
            end if;
         end loop;
      end if;
   end if;
end process;

-- -------------------------------------------------------
-- MI32 common data register high
mi_reg_mi_common_data_high : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      if (mi_reg_mi_data_high_we = '1') then
         for i in 0 to BE'high loop
            if BE(i) = '1' then
               mi_reg_mi_data_high(8*i+7 downto 8*i) <= DWR(8*i+7 downto 8*i);
            end if;
         end loop;
      end if;
   end if;
end process;

-- -------------------------------------------------------
-- mux for ARDY
ardy_mux : process(ardy_mux_addr, ardy_reg_cntrl_mux_in, ardy_inta_mux_in, WR, RD)
begin
   case (ardy_mux_addr) is
      when "001" => ardy_mux_out <= ardy_reg_cntrl_mux_in;
      when "010" => ardy_mux_out <= ardy_inta_mux_in;
      when "100" => ardy_mux_out <= drdy_input_async;
      when others => ardy_mux_out <= WR or RD;
   end case;
end process;

-- --------------------------------------------------------------------------------
-- Register MI32.DRD (data output)
reg_mi32_drd : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      DRD <= drd_input;
      DRDY <= drdy_input_sync;
   end if;
end process reg_mi32_drd;

process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      drdy_input_sync <= drdy_input_async;
   end if;
end process;

-- --------------------------------------------------------------------------------
-- Choose data for DRD register
core_data_to_drd_mux : process(drd_mux_addr, core_reg_mi_data_low, core_reg_mi_data_middle, core_reg_mi_data_high)
begin
   case(drd_mux_addr) is
      when "01" => drd_input <= core_reg_mi_data_low;
      when "10" => drd_input <= core_reg_mi_data_middle;
      when others => drd_input <= core_reg_mi_data_high;
   end case;
end process core_data_to_drd_mux;

-- --------------------------------------------------------------------------------
-- Choose register by address in MI32.ADDR
select_demux : process(ADDR)
begin
   -- Implicit values of select
   sel_reg_mi_data_low <= '0';
   sel_reg_mi_data_middle <= '0';
   sel_reg_mi_data_high <= '0';
   sel_reg_cntrl <= '0';
   sel_reg_inta <= '0';

   case (ADDR(31 downto 0)) is
      when X"00000000" => sel_reg_mi_data_low <= '1';       -- Low part of common mi32 data register
      when X"00000004" => sel_reg_mi_data_middle <= '1';    -- Middle part of common mi32 data register
      when X"00000008" => sel_reg_mi_data_high <= '1';      -- High part of common mi32 data register
      when X"0000000C" => sel_reg_cntrl <= '1';             -- MI32 control register
--      when X"00000010" => sel_detect_regs <= '1';           -- Detection registers of sources PPS0 and PPS1
      when X"00000014" => sel_reg_inta <= '1';              -- INTA register selected
--      when X"00000018" => sel_pps_mux_cntrl <= '1';         -- Input source multiplexor address
--      when X"0000001C" => sel_freq <= '1';                  -- TSU frequency
      when others => null;
   end case;

end process select_demux;

-- --------------------------------------------------------------------------------
-- Set write enable into register
  mi_reg_mi_data_low_we    <= sel_reg_mi_data_low and WR;
  mi_reg_mi_data_middle_we <= sel_reg_mi_data_middle and WR;
  mi_reg_mi_data_high_we   <= sel_reg_mi_data_high and WR;
  mi_reg_cntrl_we          <= sel_reg_cntrl and WR;
  mi_reg_ts_dv_we          <= sel_reg_inta and WR;

  --ardy_mux_addr <= mi_reg_ts_dv_we & mi_reg_cntrl_we & mi_reg_mi_data_high_we & mi_reg_mi_data_middle_we & mi_reg_mi_data_low_we;
  --ardy_mux_addr <= sel_reg_inta & sel_reg_cntrl;
  ardy_mux_addr <= drdy_input_async & sel_reg_inta & sel_reg_cntrl;
  --ardy_mux_addr <= drdy_input_async & mi_reg_ts_dv_we & mi_reg_cntrl_we;

-- --------------------------------------------------------------------------------
-- Set write enable into register
  core_reg_mi_data_low_we      <= (sel_reg_rtr_wr or sel_reg_incr_val_wr or sel_reg_pulsepsec_wr) and reg_write;
  core_reg_mi_data_middle_we   <= (sel_reg_rtr_wr or sel_reg_incr_val_wr or sel_reg_pulsepsec_wr) and reg_write;
  core_reg_mi_data_high_we     <= (sel_reg_rtr_wr or sel_reg_pulsepsec_wr) and reg_write;

  --drd_mux_addr <= core_reg_mi_data_middle_re & core_reg_mi_data_low_re;
  drd_mux_addr <= sel_reg_mi_data_middle & sel_reg_mi_data_low;

-- --------------------------------------------------------------------------------
-- Set drdy_input_async
  drdy_input_async <= (sel_reg_mi_data_low or sel_reg_mi_data_middle or sel_reg_mi_data_high) and RD; 

-- ----------------------------------------------------------------------------
--                       TRANSITIONS BETWEEN CLK DOMAINS
-- ----------------------------------------------------------------------------

-- --------------------------------------------------------
-- INTA mi32 --> INTA tsu_core
ts_dv_sync : entity work.async
   port map (
      -- input clk and data
      IN_CLK     => MI32_CLK,
      -- data write request
      RQST       => mi_reg_ts_dv_we,
      -- address ready signal - when we are ready for another transaction
      RDY        => ardy_inta_mux_in,

      -- output clk and data
      OUT_CLK    => TSU_CORE_CLK,
      OUT_RQST   => core_reg_ts_dv_we
   );

-- --------------------------------------------------------
-- reg_cntrl mi32 --> reg_cntrl tsu_core
reg_cntrl_sync : entity work.async
   port map (
      -- input clk and data
      IN_CLK     => MI32_CLK,
      -- data write request
      RQST       => mi_reg_cntrl_we,
      -- address ready signal - when we are ready for another transaction
      RDY        => ardy_reg_cntrl_mux_in,

      -- output clk and data
      OUT_CLK    => TSU_CORE_CLK,
      OUT_RQST   => core_reg_cntrl_write
   );
end architecture behavioral; 
