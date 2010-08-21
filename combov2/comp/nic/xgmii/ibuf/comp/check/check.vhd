-- check.vhd: Architecture of IBUF block checking frame properties
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
--            Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.ibuf_pkg.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture CHECK_ARCH of CHECK is

   -- Constants definition
   -- Length of the pipeline
   constant CONST_PIPELINE_LEN      : integer := 6;
   -- Size of the FIFO:
   -- CONST_PIPELINE_LEN - 2 (reg1_sop-1, inreg-1, fifo-1, reg_sau_next_item+1)
   constant CONST_FIFO_LEN          : integer := CONST_PIPELINE_LEN - 2;
   -- Width of the control bits and data (1+1+3+1+64)
   constant CONST_CTRL_DATA_WIDTH   : integer := 70;
   -- Position of SOP in ctrl_data signals
   constant CONST_POS_SOP           : integer := 0;
   -- Position of EOP in ctrl_data signals
   constant CONST_POS_EOP           : integer := 1;
   -- Position of LSB of EOP_POS in ctrl_data signals
   constant CONST_LSB_EOP_POS       : integer := 2;
   -- Position of MSB of EOP_POS in ctrl_data signals
   constant CONST_MSB_EOP_POS       : integer := 4;
   -- Position of ERR in ctrl_data signals
   constant CONST_POS_ERR           : integer := 5;
   -- Position of LSB of data in ctrl_data signals
   constant CONST_LSB_DATA          : integer := 6;
   -- Position of SOP in ctrl_data signals
   constant CONST_MSB_DATA          : integer := 69;

   ---------- Signals declaration ----------
   ---------- CRC removing ----------
   -- not trimered signals for CRC checking
   signal data_in_crc               : std_logic_vector(63 downto 0);
   signal eop_in_crc                : std_logic;
   signal eop_pos_in_crc            : std_logic_vector(2 downto 0);
   
   -- delay of all input signals (because of CRC removing)
   signal reg1_eop                  : std_logic;
   signal reg1_eop_pos              : std_logic_vector(2 downto 0);
   signal reg1_err                  : std_logic;
   
   signal data_in                   : std_logic_vector(63 downto 0);
   signal sop_in                    : std_logic;
   signal eop_in                    : std_logic;
   signal eop_pos_in                : std_logic_vector(2 downto 0);
   signal err_in                    : std_logic;

   -- input signals after CRC removing
   signal reg2_data_without_crc     : std_logic_vector(63 downto 0);
   signal reg2_sop_without_crc      : std_logic;
   signal reg2_eop_without_crc      : std_logic;
   signal eop_pos_without_crc       : std_logic_vector(2 downto 0);
   signal reg2_err_without_crc      : std_logic;
   signal reg7_earlier_eop          : std_logic;

   -- eop_pos after word removing
   signal new_eop_pos_in            : std_logic_vector(2 downto 0);

   -- select signal for multiplexers
   signal remove_word               : std_logic;
   signal reg1_remove_word         : std_logic;
   
   -- mx_delayed multiplexers
   signal mx_delayed_eop            : std_logic;
   signal mx_delayed_eop_pos        : std_logic_vector(2 downto 0);
   
   -- mx_erasing multiplexers
   signal mx_erasing_eop            : std_logic;


   -- Signals from mi_int
   signal mintu_len                 : std_logic_vector(15 downto 0);
   signal mtu_len                   : std_logic_vector(15 downto 0);
   signal check_mode                : std_logic_vector(1 downto 0);

   -- Signals connected to the output
   signal data_out                  : std_logic_vector(63 downto 0);
   signal sop_out                   : std_logic;
   signal eop_out                   : std_logic;
   signal eop_pos_out               : std_logic_vector(2 downto 0);
   signal err_pos_out               : std_logic;

   -- Signals for the shift register
   signal shreg_ctrldata_in         : std_logic_vector(CONST_CTRL_DATA_WIDTH-1
                                                                    downto 0);
   signal shreg_ctrldata_out        : std_logic_vector(CONST_CTRL_DATA_WIDTH-1
                                                                    downto 0);

   -- PIPELINE
   -- mx_add signals
   signal mx_add_in_0               : std_logic_vector(3 downto 0);
   signal mx_add_in_1               : std_logic_vector(3 downto 0);
   signal mx_add                    : std_logic_vector(3 downto 0);
   signal mx_add_sel                : std_logic;

   -- 1st pipeline stage
   signal reg1_add                  : std_logic_vector(3 downto 0);
   signal reg1_sop                  : std_logic;

   -- 2nd pipeline stage
   signal reg2_sop                  : std_logic;
   signal cnt2_len                  : std_logic_vector(15 downto 0);
   signal cnt2_len_ld               : std_logic;

   -- 3rd pipeline stage
   signal mintu_fault               : std_logic;
   signal mtu_fault                 : std_logic;
   signal reg3_broadcast_err_in     : std_logic;
   signal reg3_broadcast_err_we     : std_logic;
   signal reg3_broadcast_err        : std_logic;
   signal reg3_multicast_err_in     : std_logic;
   signal reg3_multicast_err_we     : std_logic;
   signal reg3_multicast_err        : std_logic;
   signal reg3_mintu_err            : std_logic;
   signal reg3_mtu_err              : std_logic;

   -- 4th pipeline stage
   signal reg4_match_bus_in         : std_logic_vector(MAC_COUNT-1 downto 0);
   signal reg4_match_bus_we         : std_logic;
   signal reg4_match_bus            : std_logic_vector(MAC_COUNT-1 downto 0);
   signal reg4_broadcast_err        : std_logic;
   signal reg4_multicast_err        : std_logic;
   signal reg4_mintu_err            : std_logic;
   signal reg4_mtu_err              : std_logic;

   -- 5th pipeline stage
   signal reg5_mode1_err            : std_logic;
   signal reg5_mode1_err_in         : std_logic;
   signal reg5_broadcast_err        : std_logic;
   signal reg5_multicast_err        : std_logic;
   signal reg5_mintu_err            : std_logic;
   signal reg5_mtu_err              : std_logic;

   -- 6th pipeline stage
   signal mode2_err                 : std_logic;
   signal mode3_err                 : std_logic;
   signal mx_mac_error              : std_logic;
   signal reg6_mac_err              : std_logic;
   signal reg6_mintu_err            : std_logic;
   signal reg6_mtu_err              : std_logic;

   -- 7th pipeline stage (used when CRC is trimmed)
   signal reg7_mac_err              : std_logic;
   signal reg7_mintu_err            : std_logic;
   signal reg7_mtu_err              : std_logic;
   signal reg7_crc_err              : std_logic;
   signal reg7_frame_len            : std_logic_vector(15 downto 0);


   -- Sampling unit signals
   signal sau_err_fifo_in           : std_logic_vector(0 downto 0);
   signal sau_err                   : std_logic_vector(0 downto 0);
   signal sau_fifo_empty            : std_logic;
   signal sau_err_vld               : std_logic;
   signal reg_sau_next_item         : std_logic;


   -- CRC part signals
   -- mx_crc_frame signals
   signal mx_crc_frame_in_0         : std_logic_vector(31 downto 0);
   signal mx_crc_frame_in_1         : std_logic_vector(31 downto 0);
   signal mx_crc_frame_in_2         : std_logic_vector(31 downto 0);
   signal mx_crc_frame_in_3         : std_logic_vector(31 downto 0);
   signal mx_crc_frame_in_4         : std_logic_vector(31 downto 0);
   signal mx_crc_frame_in_5         : std_logic_vector(31 downto 0);
   signal mx_crc_frame_in_6         : std_logic_vector(31 downto 0);
   signal mx_crc_frame_in_7         : std_logic_vector(31 downto 0);
   signal mx_crc_frame              : std_logic_vector(31 downto 0);
   signal mx_crc_frame_sel          : std_logic_vector(2 downto 0);

   -- 1st pipeline stage
   signal reg1_crc_frame            : std_logic_vector(31 downto 0);
   signal reg1_crc_frame_we         : std_logic;
   signal reg1_data                 : std_logic_vector(63 downto 0);
   signal reg1_crc_eop              : std_logic;
   signal reg1_crc_eop_we           : std_logic;
   signal reg1_mask                 : std_logic_vector(2 downto 0);

   -- Signals of 2nd pipeline stage multiplexers
   signal eop_pos_crc               : std_logic_vector(2 downto 0);
   signal eop_shift                 : std_logic;
   signal mx_mask_shift             : std_logic_vector(2 downto 0);
   signal mx_mask_shift_sel         : std_logic;
   signal mx_eop_shift              : std_logic;
   signal reg_mx_eop_shift          : std_logic;
   signal mx_eop_shift_sel          : std_logic;

   -- CRC module input signals
   signal crc_data                  : std_logic_vector(63 downto 0);
   signal crc_di_dv                 : std_logic;
   signal crc_reset                 : std_logic;
   signal crc_mask                  : std_logic_vector(2 downto 0);

   -- CRC module output signals
   signal crc_do                    : std_logic_vector(31 downto 0);
   signal crc_do_dv                 : std_logic;

   -- 2nd pipeline stage
   signal reg2_crc_frame            : std_logic_vector(31 downto 0);

   -- 3rd pipeline stage
   signal reg3_crc_frame            : std_logic_vector(31 downto 0);
   signal reg3_frame_len            : std_logic_vector(15 downto 0);

   -- 4th pipeline stage
   signal reg4_crc_in               : std_logic_vector(31 downto 0);
   signal reg4_crc                  : std_logic_vector(31 downto 0);
   signal reg4_crc_do_dv            : std_logic;
   signal reg4_frame_len            : std_logic_vector(15 downto 0);

   -- 5th pipeline stage
   signal reg5_crc_err_in           : std_logic;
   signal reg5_crc_err_we           : std_logic;
   signal reg5_crc_err              : std_logic;
   signal reg5_frame_len            : std_logic_vector(15 downto 0);

   -- 6th pipeline stage
   signal reg6_crc_err              : std_logic;
   signal reg6_frame_len            : std_logic_vector(15 downto 0);
   signal reg6_frame_len_in         : std_logic_vector(15 downto 0);

begin

   -- -------------------------------------------------------------------------
   --                            Remove CRC
   -- -------------------------------------------------------------------------

   -- Generate this part only if INBANDFCS = false

   crc_rem: if (INBANDFCS = false) generate
   begin

      -- registers without RESET
      regs_no_reset : process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
            -- signals for CRC removing
            reg2_data_without_crc  <= reg1_data;
            eop_pos_without_crc    <= mx_delayed_eop_pos;
         end if;
      end process regs_no_reset;

      -- registers with RESET
      regs_reset: process (CLK)
      begin
         if (CLK'event AND CLK ='1') then
            if (RESET = '1') then
               -- signals for CRC removing
               reg1_eop                <= '0';
               reg1_eop_pos            <= (others => '0');
               reg1_err                <= '0';
               reg1_remove_word        <= '0';
               reg2_sop_without_crc    <= '0';
               reg2_eop_without_crc    <= '0';
               reg2_err_without_crc    <= '0';
            else
               -- signals for CRC removing
               reg1_eop                <= EOP_RX;
               reg1_eop_pos            <= new_eop_pos_in;
               reg1_err                <= ERR_RX;
               reg1_remove_word        <= remove_word;
               reg2_sop_without_crc    <= reg1_sop;
               reg2_eop_without_crc    <= mx_erasing_eop;
               reg2_err_without_crc    <= (reg1_err and not SOP_RX) or
                                          (ERR_RX and not reg1_eop);
            end if;
         end if;
      end process regs_reset;

      -- unit that recalculate reg_eop_pos_pipe signal and controls removing of
      -- the last word_
      ctrl_unit: process (EOP_RX, EOP_POS_RX)
      begin
         if (EOP_RX = '1') then
            if (EOP_POS_RX < "100") then  -- last word will be removed
               remove_word       <= '1';
               new_eop_pos_in    <= '1' & EOP_POS_RX(1 downto 0);
            else
               remove_word       <= '0';
               new_eop_pos_in    <= '0' & EOP_POS_RX(1 downto 0);
            end if;
         else
            remove_word    <= '0';
            new_eop_pos_in <= (others => 'X');
         end if;
       end process ctrl_unit;

      -- multiplexors mx_delayed (chose delayed or nondelayed signal)
      mx_delayed: process(remove_word, reg1_eop, reg1_eop_pos,
                          EOP_RX, new_eop_pos_in, ERR_RX)
      begin
         case remove_word is
            when '0' => mx_delayed_eop          <= reg1_eop;
                        mx_delayed_eop_pos      <= reg1_eop_pos;
            when '1' => mx_delayed_eop          <= EOP_RX;
                        mx_delayed_eop_pos      <= new_eop_pos_in;
            when others => mx_delayed_eop       <= '0';
                           mx_delayed_eop_pos   <= (others => 'X');
         end case;
      end process mx_delayed;

      -- multiplexors mx_erasing (zeros instead of removed signals)
      mx_erasing: process(reg1_remove_word, mx_delayed_eop)
      begin
         case reg1_remove_word is
            when '0' => mx_erasing_eop          <= mx_delayed_eop;
            when '1' => mx_erasing_eop          <= '0';
            when others => mx_erasing_eop       <= 'X';
         end case;
      end process mx_erasing;

      shreg_remove_word: entity work.sh_reg
         generic map(
            NUM_BITS       => CONST_PIPELINE_LEN - 1
         )
         port map(
            CLK            => CLK,
            DIN            => mx_delayed_eop,
            CE             => '1',
            DOUT           => reg7_earlier_eop
         );

   end generate crc_rem;

   -- -------------------------------------------------------------------------
   --                          Input signals
   -- -------------------------------------------------------------------------

   -- input signals for all parts except CRC checking part
   data_in     <= DATA_RX;
   sop_in      <= SOP_RX;
   eop_in      <= EOP_RX;
   eop_pos_in  <= EOP_POS_RX;
   err_in      <= ERR_RX;

   -- input signals for CRC checking part
   data_in_crc       <= DATA_RX;
   eop_in_crc        <= EOP_RX;
   eop_pos_in_crc    <= EOP_POS_RX;

   -- -------------------------------------------------------------------------
   --                          Inputs from MI
   -- -------------------------------------------------------------------------

   -- Signals from mi_int
   mintu_len   <= MI2CHECK.MIN_FRAME_LEN;
   mtu_len     <= MI2CHECK.MAX_FRAME_LEN;
   check_mode  <= MI2CHECK.MAC_CHECK_MODE;


   -- -------------------------------------------------------------------------
   --                           Shift register
   -- -------------------------------------------------------------------------

   -- Content depends on the INBANDFCS generic

   crc_shreg_gen: if INBANDFCS = true generate
      shreg_ctrldatai: entity work.sh_reg_bus
         generic map(
            NUM_BITS       => CONST_PIPELINE_LEN,
            DATA_WIDTH     => CONST_CTRL_DATA_WIDTH
         )
         port map(
            CLK            => CLK,
            DIN            => shreg_ctrldata_in,
            CE             => '1',
            DOUT           => shreg_ctrldata_out
         );

      -- Input signals
      shreg_ctrldata_in(CONST_POS_SOP) <= sop_in;
      shreg_ctrldata_in(CONST_POS_EOP) <= eop_in;
      shreg_ctrldata_in(CONST_MSB_EOP_POS downto CONST_LSB_EOP_POS) <= eop_pos_in;
      shreg_ctrldata_in(CONST_POS_ERR) <= err_in;
      shreg_ctrldata_in(CONST_MSB_DATA downto CONST_LSB_DATA) <= data_in;

   end generate crc_shreg_gen;


   nocrc_shreg_gen: if INBANDFCS = false generate
      shreg_ctrldatai: entity work.sh_reg_bus
         generic map(
            NUM_BITS       => CONST_PIPELINE_LEN - 1,
            DATA_WIDTH     => CONST_CTRL_DATA_WIDTH
         )
         port map(
            CLK            => CLK,
            DIN            => shreg_ctrldata_in,
            CE             => '1',
            DOUT           => shreg_ctrldata_out
         );

      -- Input signals
      shreg_ctrldata_in(CONST_POS_SOP) <= reg2_sop_without_crc;
      shreg_ctrldata_in(CONST_POS_EOP) <= reg2_eop_without_crc;
      shreg_ctrldata_in(CONST_MSB_EOP_POS downto CONST_LSB_EOP_POS) <= eop_pos_without_crc;
      shreg_ctrldata_in(CONST_POS_ERR) <= reg2_err_without_crc;
      shreg_ctrldata_in(CONST_MSB_DATA downto CONST_LSB_DATA) <= reg2_data_without_crc;

   end generate nocrc_shreg_gen;

   -- Output signals from the shift register
   sop_out <= shreg_ctrldata_out(CONST_POS_SOP);
   eop_out <= shreg_ctrldata_out(CONST_POS_EOP);
   eop_pos_out <= shreg_ctrldata_out(CONST_MSB_EOP_POS downto CONST_LSB_EOP_POS);
   err_pos_out <= shreg_ctrldata_out(CONST_POS_ERR);
   data_out <= shreg_ctrldata_out(CONST_MSB_DATA downto CONST_LSB_DATA);

   -- -------------------------------------------------------------------------
   --                         1st pipeline stage
   -- -------------------------------------------------------------------------
   
   -- multiplexor mx_add
   mx_add_sel <= eop_in;
   mx_add_in_0 <= X"8";
   mx_add_in_1 <= ("0" & eop_pos_in) + 1;
   mx_addp: process(mx_add_sel, mx_add_in_0, mx_add_in_1)
   begin
      case mx_add_sel is
         when '0' => mx_add <= mx_add_in_0;
         when '1' => mx_add <= mx_add_in_1;
         when others => mx_add <= (others => 'X');
      end case;
   end process;


   -- 1st pipeline stage registers
   pipe1p: process(CLK, RESET)
   begin
      if (RESET = '1') then
         reg1_sop <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg1_add <= mx_add;
         reg1_sop <= sop_in;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                         2nd pipeline stage
   -- -------------------------------------------------------------------------

   -- CAM connection
   CAM_DI            <= X"0001" & data_in(47 downto 0);
   CAM_MATCH_EN      <= reg1_sop;
   CAM_MATCH_RST     <= '0';


   -- cnt2_len counter
   cnt2_len_ld <= reg1_sop;
   cnt2_lenp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (cnt2_len_ld = '1') then
            cnt2_len <= (others => '0');
         else
            cnt2_len <= cnt2_len + reg1_add;
         end if;
      end if;
   end process;

   -- register reg2_sop
   reg2_sopp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg2_sop <= reg1_sop;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                         3rd pipeline stage
   -- -------------------------------------------------------------------------

   -- register reg3_broadcast_err input logic
   reg3_broadcast_err_inp: process(reg1_data(47 downto 0))
   begin
      if (reg1_data(47 downto 0) /= X"FFFFFFFFFFFF") then
         reg3_broadcast_err_in <= '1';
      else
         reg3_broadcast_err_in <= '0';
      end if;
   end process;
   
   -- register reg3_broadcast_err
   reg3_broadcast_err_we <= reg2_sop;
   reg3_broadcast_errp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (reg3_broadcast_err_we = '1') then
            reg3_broadcast_err <= reg3_broadcast_err_in;
         end if;
      end if;
   end process;


   -- register reg3_multicast_err input logic
   reg3_multicast_err_in <= not reg1_data(0);
   
   -- register reg3_multicast_err
   reg3_multicast_err_we <= reg2_sop;
   reg3_multicast_errp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (reg3_multicast_err_we = '1') then
            reg3_multicast_err <= reg3_multicast_err_in;
         end if;
      end if;
   end process;

   -- register reg3_mintu_err input logic
   -- Output is '1' when input < mintu_len
   mintu_faultp: process(cnt2_len, mintu_len)
   begin
      if cnt2_len < mintu_len then
         mintu_fault <= '1';
      else
         mintu_fault <= '0';
      end if;
   end process;

   -- register reg3_mtu_err input logic
   -- Output is '1' when input > mtu_len
   mtu_faultp: process(cnt2_len, mtu_len)
   begin
      if cnt2_len > mtu_len then
         mtu_fault <= '1';
      else
         mtu_fault <= '0';
      end if;
   end process;


   -- 3rd stage pipeline registers
   pipe3p: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg3_mintu_err       <= mintu_fault;
         reg3_mtu_err         <= mtu_fault;
      end if;
   end process;

   -- register reg3_framelen
   reg3_frame_lenp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg3_frame_len <= cnt2_len;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                         4th pipeline stage
   -- -------------------------------------------------------------------------

   -- CAM connection
   reg4_match_bus_in <= CAM_MATCH_BUS;
   reg4_match_bus_we <= CAM_MATCH_BUS_VLD;

   -- register reg4_match_bus
   reg4_match_busp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (reg4_match_bus_we = '1') then
            reg4_match_bus <= reg4_match_bus_in;
         end if;
      end if;
   end process;


   -- 4th stage pipeline registers without we signal
   pipe4p: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg4_broadcast_err   <= reg3_broadcast_err;
         reg4_multicast_err   <= reg3_multicast_err;
         reg4_mintu_err       <= reg3_mintu_err;
         reg4_mtu_err         <= reg3_mtu_err;
         reg4_frame_len       <= reg3_frame_len;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                         5th pipeline stage
   -- -------------------------------------------------------------------------

   -- register reg5_mode1_err input logic
   -- Asserts '1' when at least one of the signal is active
   reg5_mode1_err_inp: process(reg4_match_bus)
   begin
      if (reg4_match_bus = 0) then
         reg5_mode1_err_in <= '1';
      else
         reg5_mode1_err_in <= '0';
      end if;
   end process;


   -- 5th pipeline stage registers
   pipe5p: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg5_mode1_err       <= reg5_mode1_err_in;
         reg5_broadcast_err   <= reg4_broadcast_err;
         reg5_multicast_err   <= reg4_multicast_err;
         reg5_mintu_err       <= reg4_mintu_err;
         reg5_mtu_err         <= reg4_mtu_err;
         reg5_frame_len       <= reg4_frame_len;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                         6th pipeline stage
   -- -------------------------------------------------------------------------

   -- mx_mac_error input logic
   mode2_err <= reg5_mode1_err and reg5_broadcast_err;
   mode3_err <= mode2_err and reg5_multicast_err;

   -- multiplexor mx_mac_error
   mx_mac_errorp: process(check_mode, reg5_mode1_err, mode2_err, mode3_err)
   begin
      case check_mode is
         when "00" => mx_mac_error <= '0';
         when "01" => mx_mac_error <= reg5_mode1_err;
         when "10" => mx_mac_error <= mode2_err;
         when "11" => mx_mac_error <= mode3_err;
         when others => mx_mac_error <= 'X';
      end case;
   end process;


   -- 6th pipeline stage registers
   crc_frame_len_gen: if (INBANDFCS = true) generate
      reg6_frame_len_in    <= reg5_frame_len;
   end generate;

   notcrc_frame_len_gen: if (INBANDFCS = false) generate
      reg6_frame_len_in    <= reg5_frame_len - conv_std_logic_vector(4, reg5_frame_len'Length);
   end generate;

   pipe6p: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg6_mac_err      <= mx_mac_error;
         reg6_mintu_err    <= reg5_mintu_err;
         reg6_mtu_err      <= reg5_mtu_err;
         reg6_frame_len    <= reg6_frame_len_in;
      end if;
   end process;

   -- 7th pipeline stage registers
   pipe7p: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg7_mac_err      <= reg6_mac_err;
         reg7_mintu_err    <= reg6_mintu_err;
         reg7_mtu_err      <= reg6_mtu_err;
         reg7_crc_err      <= reg6_crc_err;
         reg7_frame_len    <= reg6_frame_len;
      end if;
   end process;



   -- -------------------------------------------------------------------------
   --                           Sampling part
   -- -------------------------------------------------------------------------

   SAU_REQ <= reg1_sop;

   sau_err_fifo_in(0) <= not SAU_ACCEPT;

   sh_fifo_sampi: entity work.sh_fifo
      generic map(
         FIFO_WIDTH        => 1,
         FIFO_DEPTH        => CONST_FIFO_LEN,
         USE_INREG         => true,
         USE_OUTREG        => false
      )
      port map(
         CLK               => CLK,
         RESET             => RESET,
         DIN               => sau_err_fifo_in,
         WE                => SAU_DV,
         FULL              => open,
         DOUT              => sau_err,
         RE                => reg_sau_next_item,
         EMPTY             => sau_fifo_empty
      );

   sau_err_vld <= not sau_fifo_empty;

   
   -- register reg_sau_next_item (important because of timing constrains)
   reg_sau_next_itemp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_sau_next_item <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_sau_next_item <= eop_out;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                           CRC check part
   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   --                        CRC pipeline stage 1
   -- -------------------------------------------------------------------------

   -- multiplexor mx_crc_frame signals
   mx_crc_frame_sel  <= eop_pos_in_crc;
   mx_crc_frame_in_0 <= data_in_crc(7 downto 0) & reg1_data(63 downto 40);
   mx_crc_frame_in_1 <= data_in_crc(15 downto 0) & reg1_data(63 downto 48);
   mx_crc_frame_in_2 <= data_in_crc(23 downto 0) & reg1_data(63 downto 56);
   mx_crc_frame_in_3 <= data_in_crc(31 downto 0);
   mx_crc_frame_in_4 <= data_in_crc(39 downto 8);
   mx_crc_frame_in_5 <= data_in_crc(47 downto 16);
   mx_crc_frame_in_6 <= data_in_crc(55 downto 24);
   mx_crc_frame_in_7 <= data_in_crc(63 downto 32);

   -- multiplexor mx_crc_frame
   mx_crc_framep:process(mx_crc_frame_sel, mx_crc_frame_in_0, mx_crc_frame_in_1,
                        mx_crc_frame_in_2, mx_crc_frame_in_3, mx_crc_frame_in_4,
                        mx_crc_frame_in_5, mx_crc_frame_in_6, mx_crc_frame_in_7)
   begin
      case mx_crc_frame_sel is
         when "000" => mx_crc_frame <= mx_crc_frame_in_0;
         when "001" => mx_crc_frame <= mx_crc_frame_in_1;
         when "010" => mx_crc_frame <= mx_crc_frame_in_2;
         when "011" => mx_crc_frame <= mx_crc_frame_in_3;
         when "100" => mx_crc_frame <= mx_crc_frame_in_4;
         when "101" => mx_crc_frame <= mx_crc_frame_in_5;
         when "110" => mx_crc_frame <= mx_crc_frame_in_6;
         when "111" => mx_crc_frame <= mx_crc_frame_in_7;
         when others => mx_crc_frame <= (others => 'X');
      end case;
   end process;

   -- register reg1_crc_frame
   reg1_crc_frame_we <= eop_in_crc;
   reg1_crc_framep: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (reg1_crc_frame_we = '1') then
            reg1_crc_frame <= mx_crc_frame;
         end if;
      end if;
   end process;

   -- register reg1_data
   reg1_datap: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg1_data <= DATA_RX;
      end if;
   end process;

   -- register reg1_eop
   reg1_crc_eop_we <= not eop_shift;
   reg1_eopp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg1_crc_eop <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (reg1_crc_eop_we = '1') then
            reg1_crc_eop <= eop_in_crc;
         end if;
      end if;
   end process;

   -- register reg1_mask
   reg1_maskp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg1_mask <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         reg1_mask <= eop_pos_crc;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                        CRC pipeline stage 2
   -- -------------------------------------------------------------------------

   -- register reg2_crc_frame
   reg2_crc_framep: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg2_crc_frame <= reg1_crc_frame;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                        CRC pipeline stage 3
   -- -------------------------------------------------------------------------

   -- register reg3_crc_frame
   reg3_crc_framep: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg3_crc_frame <= reg2_crc_frame;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                          CRC computation
   -- -------------------------------------------------------------------------

   -- Multiplexers selector generator
   eop_shiftp: process(eop_pos_in_crc, eop_in_crc)
   begin
      if (eop_pos_in_crc < 4 and eop_in_crc = '1') then
         eop_shift <= '1';
      else
         eop_shift <= '0';
      end if;
   end process;
   eop_pos_crc <= eop_pos_in_crc - 4;

   -- multiplexor mx_eop_shift
   mx_eop_shift_sel <= eop_shift;
   mx_eop_shiftp: process(mx_eop_shift_sel, eop_in_crc, reg1_crc_eop)
   begin
      case mx_eop_shift_sel is
         when '0' => mx_eop_shift <= reg1_crc_eop;
         when '1' => mx_eop_shift <= eop_in_crc;
         when others => mx_eop_shift <= 'X';
      end case;
   end process;

   -- multiplexor mx_mask_shift
   mx_mask_shift_sel <= eop_shift;
   mx_mask_shiftp: process(mx_mask_shift_sel, eop_pos_crc, reg1_mask)
   begin
      case mx_mask_shift_sel is
         when '0' => mx_mask_shift <= reg1_mask;
         when '1' => mx_mask_shift <= eop_pos_crc;
         when others => mx_mask_shift <= (others => 'X');
      end case;
   end process;


   -- FSM
   check_crc_fsmi: entity work.check_crc_fsm
      port map(
         CLK               => CLK,
         RESET             => RESET,

         SOP               => reg1_sop,
         EOP               => mx_eop_shift,

         CRC_DI_DV         => crc_di_dv
      );

   -- Mask generation (multiplexer)
   crc_maskp: process(mx_eop_shift, mx_mask_shift)
   begin
      if mx_eop_shift = '0' then
         crc_mask <= (others => '1');
      else
         crc_mask <= mx_mask_shift;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event and CLK='1') then
         crc_reset <= reg1_sop;
      end if;
   end process;

   -- Change endianity to correct one for the CRC module
   crc_data(63 downto 56) <= reg1_data( 7 downto  0);
   crc_data(55 downto 48) <= reg1_data(15 downto  8);
   crc_data(47 downto 40) <= reg1_data(23 downto 16);
   crc_data(39 downto 32) <= reg1_data(31 downto 24);
   crc_data(31 downto 24) <= reg1_data(39 downto 32);
   crc_data(23 downto 16) <= reg1_data(47 downto 40);
   crc_data(15 downto  8) <= reg1_data(55 downto 48);
   crc_data( 7 downto  0) <= reg1_data(63 downto 56);

   -- CRC module
   crc32_64bi: entity work.v5_crc
      generic map(
         INPUT_PIPE        => false,
         -- output register pipe
         OUTPUT_PIPE       => false,
         -- input CRC32 data width, only 32 or 64
         INPUT_WIDTH       => 64,
         -- CRC module init value
         CRC_INIT          => X"FFFFFFFF"
      )
      port map(
         CLK                => CLK,

         CRCRESET           => crc_reset,
         DATA_IN            => crc_data,
         DATA_VLD           => crc_di_dv,
         DATA_WIDTH         => crc_mask,

         CRC_OUT            => crc_do
      );

   reg_mx_eop_shiftp: process(CLK, RESET)
   begin
      if (RESET = '1') then
         reg_mx_eop_shift <= '0';
      elsif (CLK'event and CLK = '1') then
         reg_mx_eop_shift <= mx_eop_shift;
      end if;
   end process;

   crc_do_dvp: process(CLK, RESET)
   begin
      if (RESET = '1') then
         crc_do_dv <= '0';
      elsif (CLK'event and CLK = '1') then
         crc_do_dv <= reg_mx_eop_shift;
      end if;
   end process;

   -- CRC is little endian
   reg4_crc_in(31 downto 24) <= crc_do( 7 downto  0);
   reg4_crc_in(23 downto 16) <= crc_do(15 downto  8);
   reg4_crc_in(15 downto  8) <= crc_do(23 downto 16);
   reg4_crc_in( 7 downto  0) <= crc_do(31 downto 24);

   -- -------------------------------------------------------------------------
   --                        CRC pipeline stage 4
   -- -------------------------------------------------------------------------

   -- register reg4_crc
   reg4_crcp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg4_crc <= (others => '1');
      elsif (CLK'event AND CLK = '1') then
         reg4_crc <= reg4_crc_in;
      end if;
   end process;

   -- register reg4_crc_do_dv
   reg4_crc_do_dvp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg4_crc_do_dv <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg4_crc_do_dv <= crc_do_dv;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                        CRC pipeline stage 5
   -- -------------------------------------------------------------------------

   -- Compares computed and extracted CRC
   reg5_crc_err_inp: process(reg4_crc, reg3_crc_frame)
   begin
      if reg4_crc /= reg3_crc_frame then
         reg5_crc_err_in <= '1';
      else
         reg5_crc_err_in <= '0';
      end if;
   end process;

   -- register reg5_crc_err
   reg5_crc_err_we <= reg4_crc_do_dv;
   reg5_crc_errp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg5_crc_err <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (reg5_crc_err_we = '1') then
            reg5_crc_err <= reg5_crc_err_in;
         end if;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                        CRC pipeline stage 6
   -- -------------------------------------------------------------------------

   -- register reg6_crc_err
   reg6_crc_errp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg6_crc_err <= reg5_crc_err;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                            Unit outputs
   -- -------------------------------------------------------------------------
   DATA_TX              <= data_out;
   SOP_TX               <= sop_out;
   EOP_TX               <= eop_out;
   EOP_POS_TX           <= eop_pos_out;
   ERR_TX               <= err_pos_out;

   -- Statistics
   STATS.SAU_ERR        <= sau_err(0);
   STATS.SAU_ERR_VLD    <= sau_err_vld;

   crc_stats_gen: if (INBANDFCS = true) generate
      STATS.MAC_ERR        <= reg6_mac_err;
      STATS.MINTU_ERR      <= reg6_mintu_err;
      STATS.MTU_ERR        <= reg6_mtu_err;
      STATS.CRC_ERR        <= reg5_crc_err;
      STATS.FRAME_LEN      <= reg6_frame_len;
   end generate;

   notcrc_stats_gen: if (INBANDFCS = false) generate
      mx_outp: process(reg7_earlier_eop, reg6_mac_err, reg6_mintu_err,
                       reg6_mtu_err, reg6_crc_err,
                       reg6_frame_len, reg7_mac_err, reg7_mintu_err,
                       reg7_mtu_err,
                       reg7_crc_err, reg7_frame_len)
      begin
         if reg7_earlier_eop = '1' then
            STATS.MAC_ERR        <= reg6_mac_err;
            STATS.MINTU_ERR      <= reg6_mintu_err;
            STATS.MTU_ERR        <= reg6_mtu_err;
            STATS.FRAME_LEN      <= reg6_frame_len;
         else
            STATS.MAC_ERR        <= reg7_mac_err;
            STATS.MINTU_ERR      <= reg7_mintu_err;
            STATS.MTU_ERR        <= reg7_mtu_err;
            STATS.FRAME_LEN      <= reg7_frame_len;
         end if;
      end process;

      STATS.CRC_ERR        <= reg6_crc_err;
   end generate;

end architecture CHECK_ARCH;
