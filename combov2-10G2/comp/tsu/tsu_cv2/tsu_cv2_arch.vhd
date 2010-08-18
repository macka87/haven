-- tsu_cv2_arch.vhd: architecture of GPS synchronized timestamp unit
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
-- $Id$:
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;


-- ----------------------------------------------------------------------------
-- ----------------------------------------------------------------------------
-- ------------------------------- Version 2.1 --------------------------------
-- ----------------------------------------------------------------------------
-- ----------------------------------------------------------------------------

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of tsu_cv2 is

   -- clk mux
   component BUFGMUX
      port (O : out STD_ULOGIC;
            I0 : in STD_ULOGIC;
            I1 : in STD_ULOGIC;
            S : in STD_ULOGIC);
   end component;

   -- Register signals
   signal detect_pps_bits         : std_logic_vector(1 downto 0);
   signal mi_detect_pps_bits0     : std_logic_vector(1 downto 0);
   signal mi_detect_pps_bits1     : std_logic_vector(1 downto 0);
   signal mi_det_clk              : std_logic_vector(1 downto 0);
   signal state_bits              : std_logic_vector(31 downto 0);
   signal det_cv_clk              : std_logic;
   signal det_ptm_clk             : std_logic;
   signal mi_cv_ref_now           : std_logic;  
   signal mi_cv_ref_old           : std_logic;
   signal mi_ptm_prec_now         : std_logic;  
   signal mi_ptm_prec_old         : std_logic;  
   signal mi_cv_ref_rec0          : std_logic;
   signal mi_ptm_prec_rec0        : std_logic;
   signal detect_pps0_reg         : std_logic;
   signal detect_pps1_reg         : std_logic;
   signal clk_mux_reg             : std_logic;
   signal clk_mux_reg_reclock0    : std_logic;
   signal clk_mux_reg_reclock1    : std_logic;

   -- PPS pipelines
   signal reg0_pps                : std_logic;
   signal reg0_pps2               : std_logic;
   signal reg0_pps3               : std_logic;
   signal pps0_pipe               : std_logic_vector(2 downto 0);
   signal sync_pps0_n             : std_logic;
   signal sync_pps1_n             : std_logic;

   signal old_sync_pps0_n         : std_logic;
   signal old_sync_pps1_n         : std_logic;
   signal xor_sync_pps0_n         : std_logic;
   signal xor_sync_pps1_n         : std_logic;
   signal cv_ref_xor              : std_logic;
   signal ptm_prec_xor            : std_logic;

   -- PPS counters
   signal pps0_cnt_reg            : std_logic_vector(28 downto 0);
   signal pps1_cnt_reg            : std_logic_vector(28 downto 0);
   signal cnt_pps_n               : std_logic;

   -- CLK counters
   signal mi_cv_ref_cnt           : std_logic_vector(4 downto 0);-- := "00000";
   signal cv_ref_cnt              : std_logic_vector(3 downto 0);-- := "0000";
   signal mi_ptm_prec_cnt         : std_logic_vector(4 downto 0);-- := "00000";
   signal ptm_prec_cnt            : std_logic_vector(3 downto 0);-- := "0000";

   -- PPS mux signals
   signal pps_mux_cntrl           : std_logic;
   signal pps_mux_out             : std_logic;
   signal pps_mux_cntrl_reclock0  : std_logic;
   signal pps_mux_cntrl_reclock1  : std_logic;

   -- MI32 interface signals

   -- MUX select signals
   signal sel_state_reg           : std_logic;
   signal sel_pps_mux_cntrl       : std_logic;
   signal sel_freq                : std_logic;
   signal sel_tsu_core_clk_mux_cntrl : std_logic;

   signal drd_input               : std_logic_vector(31 downto 0);
   signal drdy_input              : std_logic;

   -- Write enable signals
   signal reg_pps_mux_cntrl_we    : std_logic;
   signal reg_tsu_core_clk_mux_cntrl_we : std_logic;

   -- Read enable signals
   signal reg_freq_re             : std_logic;
   signal reg_state_reg_re        : std_logic;

   signal tsu_core_pps_n          : std_logic;
   signal tsu_core_clk            : std_logic;
   signal tsu_core_reset          : std_logic;
   signal tsu_core_reset_mx       : std_logic;
   signal reg_tsu_core_reset      : std_logic;

   signal cnt_reset_pps_reg       : std_logic_vector(8 downto 0);
   signal cnt_pps_apx_reg         : std_logic_vector(27 downto 0); -- maximum frequency supported 268435455 HZ
   signal comparator_reg          : std_logic;

   signal tsu_core_frequency      : std_logic_vector(31 downto 0);
   signal drd_input_from_tsu_core : std_logic_vector(31 downto 0);
   signal drd_input_mux_cntrl     : std_logic_vector(1 downto 0);

   signal tsu_core_drdy           : std_logic;
   signal tsu_core_ardy           : std_logic;
   signal detect_drdy             : std_logic;
   signal freq_drdy               : std_logic;

   -- Fractional part to ns conversion signals
   signal ts_from_tsu_core        : std_logic_vector(63 downto 0);
   signal ts_to_ts_ns             : std_logic_vector(63 downto 0);
   -- signals used with DSP's enabled code block
   signal reg_input1              : std_logic_vector(31 downto 0);
   signal reg_input2              : std_logic_vector(31 downto 0);
   signal reg_input3              : std_logic_vector(31 downto 0);
   signal reg_output1             : std_logic_vector(31 downto 0);
   signal reg_output2             : std_logic_vector(31 downto 0);
   signal reg_output3             : std_logic_vector(31 downto 0);
   signal multt                   : std_logic_vector(63 downto 0);

   signal reg_upper_ts1           : std_logic_vector(31 downto 0);
   signal reg_upper_ts2           : std_logic_vector(31 downto 0);
   signal reg_upper_ts3           : std_logic_vector(31 downto 0);
   signal reg_upper_ts4           : std_logic_vector(31 downto 0);
   signal reg_upper_ts5           : std_logic_vector(31 downto 0);
   signal reg_upper_ts6           : std_logic_vector(31 downto 0);
   -- signals used with DSP's disabled code block
   signal no_dsp_reg_input1       : std_logic_vector(31 downto 0);
   signal no_dsp_reg_input2       : std_logic_vector(31 downto 0);
   signal no_dsp_reg_output1      : std_logic_vector(29 downto 0);
   signal no_dsp_reg_output2      : std_logic_vector(29 downto 0);
   signal no_dsp_multt            : std_logic_vector(47 downto 0);
   signal no_dsp_shift_reg_input2_2: std_logic_vector(34 downto 0);
   signal no_dsp_sum1             : std_logic_vector(34 downto 0);
   signal no_dsp_sum2             : std_logic_vector(43 downto 0);
   signal no_dsp_sum              : std_logic_vector(47 downto 0);

   signal no_dsp_reg_upper_ts1    : std_logic_vector(31 downto 0);
   signal no_dsp_reg_upper_ts2    : std_logic_vector(31 downto 0);
   signal no_dsp_reg_upper_ts3    : std_logic_vector(31 downto 0);
   signal no_dsp_reg_upper_ts4    : std_logic_vector(31 downto 0);

   attribute use_dsp48 : string;
   attribute use_dsp48 of no_dsp_multt : signal is "no";

begin

 -- ---------------------------------------------------------------------------
 -- Instance of core unit of whole timestamp unit - inside there are registers
 -- for counting real-time
 -- ---------------------------------------------------------------------------
 tsu_cv2_core_instance : entity work.tsu_cv2_core
 generic map (
   REGISTER_TS_OUTPUT => false
 )
 port map (
   -- Clock and reset signals for MI_32 interface
   MI32_CLK       => MI32_CLK,
   MI32_RESET     => MI32_RESET,

   -- In / Out SW interface via MI_32
   DWR            => DWR,
   ADDR           => ADDR,
   RD             => RD,
   WR             => WR,
   BE             => BE,
   DRD            => drd_input_from_tsu_core,
   ARDY           => tsu_core_ardy,
   DRDY           => tsu_core_drdy,

   -- Input PPS_N signal
   PPS_N          => tsu_core_pps_n,

   -- TSU core clock
   TSU_CORE_CLK   => tsu_core_clk,
   TSU_CORE_RESET => tsu_core_reset,

   -- Output pacodag interface
   TS             => ts_from_tsu_core,
   TS_DV          => TS_DV
 );

-- ----------------------------------------------------------------------------
-- TIMESTAMP FORMAT CONVERT - FRACTIONAL TO NANOSECOND
-- ----------------------------------------------------------------------------

-- generate code that uses DSP blocks for timestamp format conversion
use_mult_dsp : if TS_MULT_USE_DSP = true generate
   -- pipelined conversion of fractinal part of timestamp to ns format
   frac_part_to_ns : process(tsu_core_clk)
   begin
      if (tsu_core_clk'event and tsu_core_clk = '1') then
         reg_input1 <= ts_from_tsu_core(31 downto 0);
         reg_input2 <= reg_input1;
         reg_input3 <= reg_input2;
         reg_output1 <= multt(63 downto 32);
         reg_output2 <= reg_output1;
         reg_output3 <= reg_output2;

         reg_upper_ts1 <= ts_from_tsu_core(63 downto 32);
         reg_upper_ts2 <= reg_upper_ts1;
         reg_upper_ts3 <= reg_upper_ts2;
         reg_upper_ts4 <= reg_upper_ts3;
         reg_upper_ts5 <= reg_upper_ts4;
         reg_upper_ts6 <= reg_upper_ts5;
      end if;
   end process;

   -- actual conversion of fractinal part of timestamp to ns format
   -- it is made by multiplying every lower part of timestamp (31 downto 0) by a constant X"3B9ACA00"

   multt <= reg_input3 * X"3B9ACA00";

   -- connection to ts_ns port
   ts_to_ts_ns <= reg_upper_ts6 & reg_output3;
end generate use_mult_dsp;

-- generate code that uses just logic (no DSP's) for timestamp format conversion
dont_use_mult_dsp : if TS_MULT_USE_DSP = false generate
   -- pipelined conversion of fractinal part of timestamp to ns format
   frac_part_to_ns : process(tsu_core_clk)
   begin
      if (tsu_core_clk'event and tsu_core_clk = '1') then
         no_dsp_reg_input1  <= ts_from_tsu_core(31 downto 0);
         no_dsp_reg_input2  <= no_dsp_reg_input1;
         no_dsp_reg_output1 <= no_dsp_sum(47 downto 18);
         no_dsp_reg_output2 <= no_dsp_reg_output1;

         no_dsp_reg_upper_ts1 <= ts_from_tsu_core(63 downto 32);
         no_dsp_reg_upper_ts2 <= no_dsp_reg_upper_ts1;
         no_dsp_reg_upper_ts3 <= no_dsp_reg_upper_ts2;
         no_dsp_reg_upper_ts4 <= no_dsp_reg_upper_ts3;
      end if;
   end process;

   -- actual conversion of fractinal part of timestamp to ns format
   -- it is made by multiplying every lower part of timestamp (31 downto 0) by a constant X"3B9ACA00"

   -- As problem with constrains doesn't allow us to use integrated DSP'S for multiplying we have to make
   -- it as a logic. Therefore there is some kind of optimalizations to make it more cheaper for sources usage:
   no_dsp_multt <= no_dsp_reg_input2 * "1110111001101011"; -- use just part of 3B9ACA00 constant (lower 14 bits are cutted off here)

   -- two bits of 14 that were cutted from 3B9ACA00 constant has value 1 => add particular value to incoming timestamp
   no_dsp_shift_reg_input2_2 <= "0" & no_dsp_reg_input2(31 downto 0) & "00"; -- multiply 4 - add first non-null bit
   no_dsp_sum1 <= no_dsp_reg_input2 + no_dsp_shift_reg_input2_2; -- add second non-null bit
   no_dsp_sum2 <= no_dsp_sum1 & "000000000";

   -- finally add counted value to multiplied part
   no_dsp_sum <= no_dsp_multt + no_dsp_sum1(34 downto 5);

   ts_to_ts_ns <= no_dsp_reg_upper_ts4 & "00" & no_dsp_reg_output2;
end generate dont_use_mult_dsp;

-- ----------------------------------------------------------------------------
-- END OF TIMESTAMP CONVERT
-- ----------------------------------------------------------------------------

TS <= ts_from_tsu_core;
TS_NS <= ts_to_ts_ns;

 -- -------------------------------------------------------
 -- CLK MUX, S = 0 --> O = I0
 --          S = 1 --> O = I1
 clk_mux : BUFGMUX
 port map (
    O  => tsu_core_clk,
    I0 => COMBOV2_REF_CLK,
    I1 => PTM_PRECISE_CLK,
    S  => clk_mux_reg_reclock1
 );

TS_CLK <= tsu_core_clk;

 -- -------------------------------------------------------
 -- RESET MUX
 reset_mux : process(clk_mux_reg, PTM_PRECISE_RESET, COMBOV2_REF_RESET)
 begin
    case (clk_mux_reg) is
       when '0' => tsu_core_reset_mx <= COMBOV2_REF_RESET;
       when others => tsu_core_reset_mx <= PTM_PRECISE_RESET;
    end case;
 end process;

 reset_reg_p : process(tsu_core_clk)
 begin
   if tsu_core_clk'event and tsu_core_clk = '1' then
      tsu_core_reset <= reg_tsu_core_reset;
      reg_tsu_core_reset <= tsu_core_reset_mx;
   end if;
 end process;

 -- -------------------------------------------------------
 -- tsu_core frequency mux
 clk_frequency_mux : process(clk_mux_reg)
 begin
    case (clk_mux_reg) is
       when '0' => tsu_core_frequency <= conv_std_logic_vector(COMBOV2_REF_CLK_FREQUENCY, 32);
       when others => tsu_core_frequency <= conv_std_logic_vector(PTM_PRECISE_CLK_FREQUENCY, 32);
    end case;
 end process;

-- --------------------------------------------------------
--         Detection of active source clk signals
-- --------------------------------------------------------
-- Detection of COMBOV2_REF_CLK
clk_det_cnt_cv : process(COMBOV2_REF_CLK)
begin
   if (COMBOV2_REF_CLK'event and COMBOV2_REF_CLK = '1') then
      cv_ref_cnt <= cv_ref_cnt + '1';
   end if;
end process;

reclock_detect_combo_ref_clk : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      mi_cv_ref_rec0 <= cv_ref_cnt(3);
      mi_cv_ref_now <= mi_cv_ref_rec0;
      mi_cv_ref_old <= mi_cv_ref_now;
   end if;
end process;

cv_ref_xor <= mi_cv_ref_now xor mi_cv_ref_old;

clk_det_cnt_cv_mi : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      if (cv_ref_xor = '1') then
         mi_cv_ref_cnt <= (others => '0');
      else
         mi_cv_ref_cnt <= mi_cv_ref_cnt + '1';
      end if;
   end if;
end process;

cv_clk_detect_register : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      if (mi_cv_ref_cnt(4) = '1') then
         det_cv_clk <= '0';
      else
         if (cv_ref_xor = '1') then
            det_cv_clk <= '1';
         end if;
      end if;
   end if;
end process;

-- Detection of PTM_PRECISE_CLK
clk_det_cnt_ptm : process(PTM_PRECISE_CLK)
begin
   if (PTM_PRECISE_CLK'event and PTM_PRECISE_CLK = '1') then
      ptm_prec_cnt <= ptm_prec_cnt + '1';
   end if;
end process;

reclock_detect_ptm_prec_clk : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      mi_ptm_prec_rec0 <= ptm_prec_cnt(3);
      mi_ptm_prec_now <= mi_ptm_prec_rec0;
      mi_ptm_prec_old <= mi_ptm_prec_now;
   end if;
end process;

ptm_prec_xor <= mi_ptm_prec_now xor mi_ptm_prec_old;

clk_det_cnt_ptm_mi : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      if (ptm_prec_xor = '1') then
         mi_ptm_prec_cnt <= (others => '0');
      else
         mi_ptm_prec_cnt <= mi_ptm_prec_cnt + '1';
      end if;
   end if;
end process;

ptm_clk_detect_register : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      if (mi_ptm_prec_cnt(4) = '1') then
         det_ptm_clk <= '0';
      else
         if (ptm_prec_xor = '1') then
            det_ptm_clk <= '1';
         end if;
      end if;
   end if;
end process;

-- --------------------------------------------------------
mi_det_clk <= det_ptm_clk & det_cv_clk;
-- --------------------------------------------------------

-- --------------------------------------------------------

-- --------------------------------------------------------
--         Aproximation of PPS_N pulse
-- --------------------------------------------------------

-- --------------------------------------------------------
-- Comparator detects if cnt_pps_apx_reg is zero
comparator_prcs : process(tsu_core_clk)
begin
   if (tsu_core_clk'event and tsu_core_clk = '1') then
      if (cnt_pps_apx_reg = X"0000000") then
         comparator_reg <= '1';
      else
         comparator_reg <= '0';
      end if; 
   end if; 
end process;

-- --------------------------------------------------------
-- Counter decreasing it's value from constant which depends on FREQUENCY
cnt_pps_approximate : process(tsu_core_clk)
begin
   if (tsu_core_clk'event and tsu_core_clk = '1') then
      if (tsu_core_reset = '1' or comparator_reg = '1') then
      -- minus 2 because one count takes the comparator to set comparator_reg
         if (clk_mux_reg = '0') then -- we have to use 
            cnt_pps_apx_reg <= conv_std_logic_vector(COMBOV2_REF_CLK_FREQUENCY - 2,28);
         else
            cnt_pps_apx_reg <= conv_std_logic_vector(PTM_PRECISE_CLK_FREQUENCY - 2,28);
         end if;
      else
         cnt_pps_apx_reg <= cnt_pps_apx_reg - '1';
      end if; 
   end if; 
end process;

-- --------------------------------------------------------
-- Counter for delayed reset of fake PPS_N pulse register
cnt_reset_pps : process(tsu_core_clk)
begin
   if (tsu_core_clk'event and tsu_core_clk = '1') then
      if (tsu_core_reset = '1' or cnt_reset_pps_reg(8) = '1') then
         cnt_reset_pps_reg <= (others => '0');
      elsif (cnt_pps_n = '0') then
         cnt_reset_pps_reg <= cnt_reset_pps_reg + '1';
      end if;
   end if;
end process;

-- --------------------------------------------------------
-- Fake PPS_N pulse register
pps_approximate_reg_prcs : process(tsu_core_clk)
begin
   if (tsu_core_clk'event and tsu_core_clk = '1') then
      if (tsu_core_reset = '1' or cnt_reset_pps_reg(8) = '1') then
         cnt_pps_n <= '1';
      elsif (comparator_reg = '1') then
         cnt_pps_n <= '0';
      end if;
   end if;
end process;

sync_pps1_n <= cnt_pps_n;

-- --------------------------------------------------------
--         Processing of PPS_N signal
-- --------------------------------------------------------

-- -------------------------------------------------------
-- registered PPS0_N signal
pps0_n_reg : process(tsu_core_clk)
begin
   if (tsu_core_clk'event and tsu_core_clk = '1') then
      reg0_pps  <= GPS_PPS_N;
      reg0_pps2 <= reg0_pps;
      reg0_pps3 <= reg0_pps2;
   end if;
end process;

-- -------------------------------------------------------
-- PPS0 pulse pipeline (because transition might not be fast enough
pps0_pipe <= reg0_pps & reg0_pps2 & reg0_pps3;

-- -------------------------------------------------------
-- makes one single signal from GPS_PPS_N and pps0_pipe
sync_pps0 : process(pps0_pipe, reg0_pps)
begin
   case (pps0_pipe) is
      -- when "000" => sync_pps0_n <= GPS_PPS_N; 
      -- Changed by pus: This makes all following signals constrained
      when "000" => sync_pps0_n <= reg0_pps;
      when others => sync_pps0_n <= '1';
   end case;
end process;

-- -------------------------------------------------------
-- registring last value of pps_n
process(tsu_core_clk)
begin
   if (tsu_core_clk'event and tsu_core_clk = '1') then
      if (tsu_core_reset = '1') then
         old_sync_pps0_n <= '1';
      else
         old_sync_pps0_n <= sync_pps0_n;
      end if;
   end if;
end process;

-- -------------------------------------------------------
-- sync_pps0_n counter for distinguishing if the source pulse
-- per second is active or not
pps0_counter : process(tsu_core_clk)
begin
   if (tsu_core_clk'event and tsu_core_clk = '1') then
      -- if RESET or PPS from GPS or pps0_cnt_reg is equal to X"10000000"
      if (tsu_core_reset = '1' or xor_sync_pps0_n = '1' or pps0_cnt_reg(28) = '1') then
         pps0_cnt_reg <= (others => '0');
      else
         pps0_cnt_reg <= pps0_cnt_reg + '1';
      end if;
   end if;
end process;

xor_sync_pps0_n <= sync_pps0_n xor old_sync_pps0_n;

-- -------------------------------------------------------
-- registring last value of pps_n
process(tsu_core_clk)
begin
   if (tsu_core_clk'event and tsu_core_clk = '1') then
      if (tsu_core_reset = '1') then
         old_sync_pps1_n <= '1';
      else
         old_sync_pps1_n <= sync_pps1_n;
      end if;
   end if;
end process;

-- -------------------------------------------------------
-- sync_pps1_n counter for distinguishing if the source pulse
-- per second is active or not
pps1_counter : process(tsu_core_clk)
begin
   if (tsu_core_clk'event and tsu_core_clk = '1') then
      -- if RESET or PPS from GPS or pps1_cnt_reg is equal to X"10000000"
      if (tsu_core_reset = '1' or xor_sync_pps1_n = '1' or pps1_cnt_reg(28) = '1') then
         pps1_cnt_reg <= (others => '0');
      else
         pps1_cnt_reg <= pps1_cnt_reg + '1';
      end if;
   end if;
end process;

xor_sync_pps1_n <= sync_pps1_n xor old_sync_pps1_n;

-- -------------------------------------------------------
-- Multiplexor for choosing which source PPS signal should
-- be used 
pps_mux : process(pps_mux_cntrl_reclock1, sync_pps0_n, sync_pps1_n, detect_pps0_reg, detect_pps1_reg)
begin
   -- Implicit values
   pps_mux_out <= sync_pps0_n or not detect_pps0_reg;

   case (pps_mux_cntrl_reclock1) is
      -- if pps signal is not active -> should be at 1 -> therefore the "or not..." statements
      when '0' => pps_mux_out <= sync_pps0_n or not detect_pps0_reg;
      when '1' => pps_mux_out <= sync_pps1_n or not detect_pps1_reg;
      when others => null;
   end case;
end process;

tsu_core_pps_n <= pps_mux_out;

-- -------------------------------------------------------
-- Detection bit if PPS0 source is active or not
detect_pps0 : process(tsu_core_clk)
begin
   if (tsu_core_clk'event and tsu_core_clk = '1') then
      if (tsu_core_reset = '1' or pps0_cnt_reg(28) = '1') then
         detect_pps0_reg <= '0';
      elsif (xor_sync_pps0_n = '1') then
         detect_pps0_reg <= '1';
      end if;
   end if;
end process;

-- -------------------------------------------------------
-- Detection bit if PPS1 source is active or not
detect_pps1 : process(tsu_core_clk)
begin
   if (tsu_core_clk'event and tsu_core_clk = '1') then
      if (tsu_core_reset = '1' or pps1_cnt_reg(28) = '1') then
         detect_pps1_reg <= '0';
      elsif (xor_sync_pps1_n = '1') then
         detect_pps1_reg <= '1';
      end if;
   end if;
end process;

detect_pps_bits <= detect_pps1_reg & detect_pps0_reg;

-- -------------------------------------------------------
-- Reclocked detection bits to MI32 frequency
-- Detection registers of PPSX_N pulse activity 
-- tsu_core --> mi
detect_reclock : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      mi_detect_pps_bits0 <= detect_pps_bits;
      mi_detect_pps_bits1 <= mi_detect_pps_bits0;
   end if;
end process;

-- -------------------------------------------------------
-- Registered pps_mux_cntrl signal for use in tsu_core_clk
-- clk domain -> reclocked to tsu_core_clk
-- path from pps_mux_cntrl to pps_mux_cntrl_reclock0 should be TIGed
pps_mux_reclock_p : process(tsu_core_clk)
begin
   if (tsu_core_clk'event and tsu_core_clk = '1') then
      pps_mux_cntrl_reclock0 <= pps_mux_cntrl;
      pps_mux_cntrl_reclock1 <= pps_mux_cntrl_reclock0;
   end if;
end process;

-- ----------------------------------------------------------------------------
--                              MI32 CLK DOMAIN
-- ----------------------------------------------------------------------------

-- -------------------------------------------------------
-- Address register for mux to choose source PPS signal
-- controlled by SW, SEL_PPS register
pps_mux_cntrl_reg : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      if (MI32_RESET = '1') then
         pps_mux_cntrl <= '0';
      elsif (reg_pps_mux_cntrl_we = '1' and BE(0) = '1') then
         pps_mux_cntrl <= DWR(0);
      end if;
   end if;
end process;

-- -------------------------------------------------------
-- Address register for mux to choose source CLK signal
-- for tsu_cv2_core controlled by SW, SEL_CORE_CLK register
tsu_core_clk_mux_cntrl_reg : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      if (MI32_RESET = '1') then
         clk_mux_reg <= '0';
      elsif (reg_tsu_core_clk_mux_cntrl_we = '1' and BE(0) = '1') then
         clk_mux_reg <= DWR(0);
      end if;
   end if;
end process;

-- Reclock reg_clk_mux to COMBOV2_REF_CLK, 
-- path to reg_clk_mux_reclock0 should be TIGed
clk_mux_reg_reclock_p : process(COMBOV2_REF_CLK)
begin
   if (COMBOV2_REF_CLK'event and COMBOV2_REF_CLK = '1') then
      clk_mux_reg_reclock1 <= clk_mux_reg_reclock0;
      clk_mux_reg_reclock0 <= clk_mux_reg;
   end if;
end process;

-- --------------------------------------------------------------------------------
-- drdy signal for read from frequency register
ardy_drdy_detect_pps_n : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      freq_drdy <= RD;
      detect_drdy <= RD;
   end if;
end process;

-- --------------------------------------------------------------------------------
-- Register MI32.DRD (data output)
reg_mi32_drd : process(MI32_CLK)
begin
   if (MI32_CLK'event and MI32_CLK = '1') then
      DRD <= drd_input;
      DRDY <= drdy_input;
   end if;
end process reg_mi32_drd;

-- --------------------------------------------------------------------------------
-- Choose data for DRD
data_to_drd_mux : process(drd_input_mux_cntrl, tsu_core_frequency, state_bits, drd_input_from_tsu_core)
begin
   case(drd_input_mux_cntrl) is
      when "01" => drd_input <= tsu_core_frequency;
      when "10" => drd_input <= state_bits;
      when others => drd_input <= drd_input_from_tsu_core;
   end case;
end process;

-- -------------------------------------------------------
-- State registers in the unit connected to mi32
state_bits <= X"0000000" & mi_det_clk & mi_detect_pps_bits1;

-- --------------------------------------------------------------------------------
-- Mux for DRDY signal
drdy_mux : process(drd_input_mux_cntrl, freq_drdy, tsu_core_drdy, detect_drdy)
begin
   case(drd_input_mux_cntrl) is
      when "01" => drdy_input <= freq_drdy;
      when "10" => drdy_input <= detect_drdy;
      when others => drdy_input <= tsu_core_drdy;
   end case;
end process;

-- --------------------------------------------------------------------------------
-- Mux for ARDY signal
ardy_mux : process(drd_input_mux_cntrl, freq_drdy, detect_drdy, tsu_core_ardy)
begin
   case(drd_input_mux_cntrl) is
      when "01" => ARDY <= freq_drdy;
      when "10" => ARDY <= detect_drdy;
      when others => ARDY <= tsu_core_ardy;
   end case;
end process;

-- --------------------------------------------------------------------------------
-- Choose register by address in MI32.ADDR
select_demux : process(ADDR)
begin
   -- Implicit values of select
   sel_state_reg <= '0';
   sel_pps_mux_cntrl <= '0';
   sel_freq <= '0';
   sel_tsu_core_clk_mux_cntrl <= '0';

   case (ADDR(31 downto 0)) is
--      when X"00000000" => sel_reg_mi_data_low <= '1';       -- Low part of common mi32 data register
--      when X"00000004" => sel_reg_mi_data_middle <= '1';    -- Middle part of common mi32 data register
--      when X"00000008" => sel_reg_mi_data_high <= '1';      -- High part of common mi32 data register
--      when X"0000000C" => sel_reg_cntrl <= '1';             -- MI32 control register
      when X"00000010" => sel_state_reg <= '1';              -- State register (detects clk and pps sources)
--      when X"00000014" => sel_reg_inta <= '1';              -- INTA register selected
      when X"00000018" => sel_pps_mux_cntrl <= '1';         -- Input source multiplexor address
      when X"0000001C" => sel_freq <= '1';                  -- TSU frequency
      when X"00000020" => sel_tsu_core_clk_mux_cntrl <= '1'; -- tsu_core clk select
      when others => null;
   end case;

end process;

-- --------------------------------------------------------------------------------
-- Set write enable into register
  reg_pps_mux_cntrl_we          <= sel_pps_mux_cntrl and WR;
  reg_tsu_core_clk_mux_cntrl_we <= sel_tsu_core_clk_mux_cntrl and WR;

-- --------------------------------------------------------------------------------
-- Set read enable from register
  reg_state_reg_re        <= sel_state_reg and RD;
  reg_freq_re             <= sel_freq and RD;

  drd_input_mux_cntrl     <= reg_state_reg_re & reg_freq_re;

end architecture behavioral;
