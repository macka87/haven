-- mi_int.vhd: Architecture of component providing MI32 interface to IBUF 
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
use work.lb_pkg.all;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture MI_INT_ARCH of MI_INT is

   ---------- Constants definition ----------
   -- Register addresses
   constant REG_TRFC_L_ADDR         : std_logic_vector(5 downto 2) := "0000";
   constant REG_CFC_L_ADDR          : std_logic_vector(5 downto 2) := "0001";
   constant REG_DFC_L_ADDR          : std_logic_vector(5 downto 2) := "0010";
   constant REG_BODFC_L_ADDR        : std_logic_vector(5 downto 2) := "0011";
   constant REG_TRFC_H_ADDR         : std_logic_vector(5 downto 2) := "0100";
   constant REG_CFC_H_ADDR          : std_logic_vector(5 downto 2) := "0101";
   constant REG_DFC_H_ADDR          : std_logic_vector(5 downto 2) := "0110";
   constant REG_BODFC_H_ADDR        : std_logic_vector(5 downto 2) := "0111";
   constant REG_IBUF_EN_ADDR        : std_logic_vector(5 downto 2) := "1000";
   constant REG_ERROR_MASK_ADDR     : std_logic_vector(5 downto 2) := "1001";
   constant REG_STATUS_ADDR         : std_logic_vector(5 downto 2) := "1010";
   constant REG_CMD_ADDR            : std_logic_vector(5 downto 2) := "1011";
   constant REG_MIN_FRAME_LEN_ADDR  : std_logic_vector(5 downto 2) := "1100";
   constant REG_MAX_FRAME_LEN_ADDR  : std_logic_vector(5 downto 2) := "1101";
   constant REG_MAC_CHECK_MODE_ADDR : std_logic_vector(5 downto 2) := "1110";

   -- Length of the status
   constant C_STATUS_LEN            : integer := BUF2MI.STATUS'length + DEBUG_INFO'length + 2;
   -- Number of the MSB in status register
   -- Note that FSM state is not stored in the register
   constant C_REG_STATUS_M          : integer := 3;


   ---------- Signals declaration ----------
   -- internal mi32 interface
   signal mi_int_dwr			: std_logic_vector(31 downto 0);   -- Input Data
   signal mi_int_addr    	: std_logic_vector(31 downto 0);   -- Address
   signal mi_int_rd      	: std_logic;                       -- Read Request
   signal mi_int_wr      	: std_logic;                       -- Write Request
   signal mi_int_be      	: std_logic_vector(3  downto 0);   -- Byte Enable
   signal mi_int_drd     	: std_logic_vector(31 downto 0);   -- Output Data
   signal mi_int_ardy    	: std_logic;                       -- Address Ready
   signal mi_int_drdy    	: std_logic;                       -- Data Ready

   -- Registers
   signal cnt_reg_we             : std_logic;
   signal reg_trfc               : std_logic_vector(63 downto 0);
   signal reg_cfc                : std_logic_vector(63 downto 0);
   signal reg_dfc                : std_logic_vector(63 downto 0);
   signal reg_bodfc              : std_logic_vector(63 downto 0);
   signal reg_ibuf_en            : std_logic;
   signal reg_ibuf_en_we         : std_logic;
   signal reg_error_mask         : std_logic_vector(4 downto 0);
   signal reg_error_mask_we      : std_logic;
   signal reg_status             : std_logic_vector(C_REG_STATUS_M downto 0);
   signal reg_status_we          : std_logic;
   signal reg_cmd_we             : std_logic;
   signal reg_min_frame_len      : std_logic_vector(15 downto 0);
   signal reg_min_frame_len_we   : std_logic;
   signal reg_max_frame_len      : std_logic_vector(15 downto 0);
   signal reg_max_frame_len_we   : std_logic;
   signal reg_mac_check_mode     : std_logic_vector(1 downto 0);
   signal reg_mac_check_mode_we  : std_logic;

   -- Command part
   signal reset_counters         : std_logic;

   -- CAM part
   signal cami_addr              : std_logic_vector(log2(MAC_COUNT)-1 downto 0);
   signal cami_data_in           : std_logic_vector(63 downto 0);
   signal cami_write_en          : std_logic;
   signal cami_match_en          : std_logic;
   signal cami_busy              : std_logic;
   signal cami_read_en           : std_logic;
   signal cami_data_out          : std_logic_vector(63 downto 0);
   signal cami_data_out_vld      : std_logic;
   signal cam_ins_addr_eq        : std_logic;
   signal reg_cam_ins_data       : std_logic_vector(63 downto 0);
   signal reg_cam_ins_data_low   : std_logic_vector(31 downto 0);
   signal reg_cam_ins_data_high  : std_logic_vector(16 downto 0);
   signal reg_cam_ins_data_low_we   : std_logic;
   signal reg_cam_ins_data_high_we  : std_logic;
   signal reg_cam_ins_in         : std_logic;
   signal reg_cam_ins            : std_logic;
   signal reg_cam_addr           : std_logic_vector(log2(MAC_COUNT)-1 downto 0);
   signal mx_cam_addr_1          : std_logic_vector(log2(MAC_COUNT)-1 downto 0);
   signal mx_cam_addr            : std_logic_vector(log2(MAC_COUNT)-1 downto 0);
   signal mx_cam_addr_sel        : std_logic;
   signal reg_read_part          : std_logic;
   signal reg_read_part_we       : std_logic;
   signal cam_read               : std_logic;
   signal reg_cam_read           : std_logic;

   -- Decoder part
   signal reg_part_cs               : std_logic;
   signal reg_part_we               : std_logic;
   signal cam_part_cs               : std_logic;
   signal reg_ibuf_en_cs            : std_logic;
   signal reg_error_mask_cs         : std_logic;
   signal reg_status_cs             : std_logic;
   signal reg_cmd_cs                : std_logic;
   signal reg_min_frame_len_cs      : std_logic;
   signal reg_max_frame_len_cs      : std_logic;
   signal reg_mac_check_mode_cs     : std_logic;
   signal reg_cam_ins_data_low_cs   : std_logic;
   signal reg_cam_ins_data_high_cs  : std_logic;

   signal mx_mi_drdy                : std_logic;
   signal mx_mi_drdy_sel            : std_logic;

   -- MI32 Output multiplexers
   signal mx_decoder_data_out    : std_logic_vector(31 downto 0);
   signal mx_cam_do              : std_logic_vector(31 downto 0);
   signal mx_cam_do_sel          : std_logic;
   signal mx_decoder_mi_rd       : std_logic_vector(31 downto 0);
   signal mx_decoder_mi_rd_sel   : std_logic;
   -- 32-bit version of registers
   signal reg_ibuf_en32          : std_logic_vector(31 downto 0);
   signal reg_error_mask32       : std_logic_vector(31 downto 0);
   signal reg_status32           : std_logic_vector(31 downto 0);
   signal reg_min_frame_len32    : std_logic_vector(31 downto 0);
   signal reg_max_frame_len32    : std_logic_vector(31 downto 0);
   signal reg_mac_check_mode32   : std_logic_vector(31 downto 0);
   signal cami_data_out32l       : std_logic_vector(31 downto 0);
   signal cami_data_out32h       : std_logic_vector(31 downto 0);

begin

   -- ----------------------------------------------------------------------------
   --                              MI32 Part
   -- ----------------------------------------------------------------------------

   -- Asynchronous MI32 interface
   mi32_asynci: entity work.mi32_async_norec
      port map(
         RESET             => RESET,
         
         CLK_M             => MI_CLK,
         MI_M_DWR      	   => MI_DWR,
	      MI_M_ADDR     	   => MI_ADDR,
	      MI_M_RD       	   => MI_RD,
	      MI_M_WR       	   => MI_WR,
	      MI_M_BE       	   => MI_BE,
	      MI_M_DRD      	   => MI_DRD,
	      MI_M_ARDY     	   => MI_ARDY,
	      MI_M_DRDY     	   => MI_DRDY,
      
         CLK_S             => IBUF_CLK,
         MI_S_DWR      	   => mi_int_dwr,
      	MI_S_ADDR     	   => mi_int_addr,
      	MI_S_RD       	   => mi_int_rd,
      	MI_S_WR       	   => mi_int_wr,
      	MI_S_BE       	   => mi_int_be,
      	MI_S_DRD      	   => mi_int_drd,
      	MI_S_ARDY     	   => mi_int_ardy,
      	MI_S_DRDY     	   => mi_int_drdy
      );


   -- ----------------------------------------------------------------------------
   --                           Registers Part
   -- ----------------------------------------------------------------------------

   -- register reg_trfc
   reg_trfcp: process(IBUF_CLK)
   begin
      if (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (cnt_reg_we = '1') then
            reg_trfc <= BUF2MI.TRFC;
         end if;
      end if;
   end process;

   -- register reg_cfc
   reg_cfcp: process(IBUF_CLK)
   begin
      if (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (cnt_reg_we = '1') then
            reg_cfc <= BUF2MI.CFC;
         end if;
      end if;
   end process;

   -- register reg_dfc
   reg_dfcp: process(IBUF_CLK)
   begin
      if (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (cnt_reg_we = '1') then
            reg_dfc <= BUF2MI.DFC;
         end if;
      end if;
   end process;

   -- register reg_bodfc
   reg_bodfcp: process(IBUF_CLK)
   begin
      if (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (cnt_reg_we = '1') then
            reg_bodfc <= BUF2MI.BODFC;
         end if;
      end if;
   end process;

   -- register reg_ibuf_en
   reg_ibuf_enp: process(RESET, IBUF_CLK)
   begin
      if (RESET = '1') then
         reg_ibuf_en <= '0';
      elsif (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (reg_ibuf_en_we = '1') then
            reg_ibuf_en <= mi_int_dwr(0);
         end if;
      end if;
   end process;

   -- register reg_error_mask
   reg_error_maskp: process(RESET, IBUF_CLK)
   begin
      if (RESET = '1') then
         reg_error_mask <= (others => '1');
      elsif (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (reg_error_mask_we = '1') then
            reg_error_mask <= mi_int_dwr(4 downto 0);
         end if;
      end if;
   end process;

   -- register reg_status
   reg_statusp: process(RESET, IBUF_CLK)
   begin
      if (RESET = '1') then
         reg_status <= (others => '0');
      elsif (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (reg_status_we = '1') then
            reg_status <= mi_int_dwr(C_REG_STATUS_M downto 0);
         else
            reg_status(C_REG_STATUS_M downto 0) <= reg_status(C_REG_STATUS_M
               downto 0) or BUF2MI.STATUS(C_REG_STATUS_M downto 0);
         end if;
      end if;
   end process;

   -- register reg_cmd
   reg_cmdp: process(IBUF_CLK)
   begin
      if (IBUF_CLK'event AND IBUF_CLK = '1') then
         cnt_reg_we     <= '0';
         reset_counters <= '0';

         if (reg_cmd_we = '1') then
            if (mi_int_dwr(1 downto 0) = "01") then
               cnt_reg_we <= '1';
            else
               reset_counters <= '1';
            end if;
         end if;
      end if;
   end process;


   -- register reg_min_frame_len
   reg_min_frame_lenp: process(RESET, IBUF_CLK)
   begin
      if (RESET = '1') then
         reg_min_frame_len <= X"0040"; -- 64
      elsif (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (reg_min_frame_len_we = '1') then
            reg_min_frame_len <= mi_int_dwr(15 downto 0);
         end if;
      end if;
   end process;

   -- register reg_max_frame_len
   reg_max_frame_lenp: process(RESET, IBUF_CLK)
   begin
      if (RESET = '1') then
         reg_max_frame_len <= X"05F6"; -- 1526
      elsif (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (reg_max_frame_len_we = '1') then
            reg_max_frame_len <= mi_int_dwr(15 downto 0);
         end if;
      end if;
   end process;

   -- register reg_mac_check_mode
   reg_mac_check_modep: process(RESET, IBUF_CLK)
   begin
      if (RESET = '1') then
         reg_mac_check_mode <= (others => '0');
      elsif (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (reg_mac_check_mode_we = '1') then
            reg_mac_check_mode <= mi_int_dwr(1 downto 0);
         end if;
      end if;
   end process;


   -- ----------------------------------------------------------------------------
   --                              CAM Part
   -- ----------------------------------------------------------------------------

   -- CAM unit
   cami: entity work.ibuf_cam
      generic map (
         CAM_ROW_WIDTH     => 64,
         CAM_ROW_COUNT     => MAC_COUNT
      )
      port map (
         CLK               => IBUF_CLK,
         RESET             => RESET,
         ADDR              => cami_addr,
         CAM_BUSY          => cami_busy,
         DATA_IN           => cami_data_in,
         WRITE_EN          => cami_write_en,
         READ_EN           => cami_read_en,
         DATA_OUT          => cami_data_out,
         DATA_OUT_VLD      => cami_data_out_vld,
         MATCH_EN          => cami_match_en,
         MATCH_RST         => CAM_MATCH_RST,
         MATCH_BUS         => CAM_MATCH_BUS,
         MATCH_BUS_VLD     => CAM_MATCH_BUS_VLD
      );


   -- Registers for DATA_IN of CAM
   -- register reg_cam_ins_data_low
   reg_cam_ins_data_lowp: process(IBUF_CLK)
   begin
      if (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (reg_cam_ins_data_low_we = '1') then
            reg_cam_ins_data_low <= mi_int_dwr(31 downto 0);
         end if;
      end if;
   end process;

   -- register reg_cam_ins_data_high
   reg_cam_ins_data_highp: process(IBUF_CLK)
   begin
      if (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (reg_cam_ins_data_high_we = '1') then
            reg_cam_ins_data_high <= mi_int_dwr(16 downto 0);
         end if;
      end if;
   end process;

   -- register reg_cam_ins_data (it is divided into 2 registers)
   -- note that SW access is little endian, but matching has to be big endian
   -- http://en.wikipedia.org/wiki/MAC_address
   reg_cam_ins_data(63 downto 49) <= (others => '0'); -- not used
   reg_cam_ins_data(48)           <= reg_cam_ins_data_high(16); -- validity bit
   reg_cam_ins_data(47 downto 40) <= reg_cam_ins_data_low(7 downto 0); -- LSB
   reg_cam_ins_data(39 downto 32) <= reg_cam_ins_data_low(15 downto 8);
   reg_cam_ins_data(31 downto 24) <= reg_cam_ins_data_low(23 downto 16);
   reg_cam_ins_data(23 downto 16) <= reg_cam_ins_data_low(31 downto 24);
   reg_cam_ins_data(15 downto 8)  <= reg_cam_ins_data_high(7 downto 0);
   reg_cam_ins_data(7 downto 0)   <= reg_cam_ins_data_high(15 downto 8); -- MSB


   -- reg_cam_ins input logic
   -- address of the higher part of MAC address has to be the same as the lower
   cam_ins_addr_eqp: process(reg_cam_addr,
                             mi_int_addr(log2(MAC_COUNT)+2 downto 3))
   begin
      if (reg_cam_addr = mi_int_addr(log2(MAC_COUNT)+2 downto 3)) then
         cam_ins_addr_eq <= '1';
      else
         cam_ins_addr_eq <= '0';
      end if;
   end process;

   reg_cam_ins_in <= cam_ins_addr_eq and reg_cam_ins_data_high_we;

   -- register reg_cam_ins
   reg_cam_insp: process(IBUF_CLK)
   begin
      if (IBUF_CLK'event AND IBUF_CLK = '1') then
         reg_cam_ins <= reg_cam_ins_in;
      end if;
   end process;


   -- multiplexor mx_cam_data_in
   mx_cam_data_inp: process(reg_ibuf_en, reg_cam_ins_data, CAM_DI)
   begin
      case reg_ibuf_en is
         when '0' => cami_data_in <= reg_cam_ins_data;
         when '1' => cami_data_in <= CAM_DI;
         when others => cami_data_in <= (others => 'X');
      end case;
   end process;


   -- CAM write_en & match_en input logic
   cami_write_en <= reg_cam_ins and not reg_ibuf_en;
   cami_match_en <= CAM_MATCH_EN and reg_ibuf_en;


   -- register reg_cam_addr
   reg_cam_addrp: process(IBUF_CLK)
   begin
      if (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (reg_cam_ins_data_low_we = '1') then
            reg_cam_addr <= mi_int_addr(log2(MAC_COUNT)+2 downto 3);
         end if;
      end if;
   end process;

   -- CAM address logic
   -- multiplexor mx_cam_addr
   mx_cam_addr_sel <= cam_read;
   mx_cam_addr_1   <= mi_int_addr(log2(MAC_COUNT)+2 downto 3);
   mx_cam_addrp: process(mx_cam_addr_sel, mx_cam_addr_1, reg_cam_addr)
   begin
      case mx_cam_addr_sel is
         when '0' => mx_cam_addr <= reg_cam_addr;
         when '1' => mx_cam_addr <= mx_cam_addr_1;
         when others => mx_cam_addr <= (others => 'X');
      end case;
   end process;

   cami_addr <= mx_cam_addr;

   -- register reg_read_part
   reg_read_part_we <= cam_read;
   reg_read_partp: process(RESET, IBUF_CLK)
   begin
      if (RESET = '1') then
         reg_read_part <= '0';
      elsif (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (reg_read_part_we = '1') then
            reg_read_part <= mi_int_addr(2);
         end if;
      end if;
   end process;

   -- register reg_cam_read
   reg_cami_read_enp: process(IBUF_CLK)
   begin
      if (IBUF_CLK'event AND IBUF_CLK = '1') then
         reg_cam_read <= cam_read;
      end if;
   end process;

   cami_read_en <= cam_read and not reg_cam_read;



   -- ----------------------------------------------------------------------------
   --                            Decoder Part
   -- ----------------------------------------------------------------------------

   -- multiplexor mx_mi_drdy
   mx_mi_drdy_sel <= cam_read;
   mx_mi_drdyp: process(mx_mi_drdy_sel, mi_int_rd, cami_data_out_vld)
   begin
      case mx_mi_drdy_sel is
         when '0' => mx_mi_drdy <= mi_int_rd;
         when '1' => mx_mi_drdy <= cami_data_out_vld;
         when others => mx_mi_drdy <= 'X';
      end case;
   end process;

   mi_int_drdy       <= mx_mi_drdy;
   mi_int_ardy       <= not cami_busy;
   mi_int_drd        <= mx_decoder_mi_rd;

   -- reg_part_cs is active if mi_int_addr is pointing to the register part
   reg_part_csp: process(mi_int_addr(7 downto 6))
   begin
      if (mi_int_addr(7 downto 6) = "00") then
         reg_part_cs <= '1';
      else
         reg_part_cs <= '0';
      end if;
   end process;

   -- cam_part_cs is active if mi_int_addr is pointing to the CAM part
   cam_part_cs <= mi_int_addr(7);


   -- Writing part ------------------------------------------------------------

   -- Register part --
   -- reg_part_we is active if reg_part_cs and mi_int_wr are active
   reg_part_we             <= reg_part_cs and mi_int_wr;

   reg_ibuf_en_we          <= reg_ibuf_en_cs and reg_part_we;
   reg_error_mask_we       <= reg_error_mask_cs and reg_part_we;
   reg_status_we           <= reg_status_cs and reg_part_we;
   reg_cmd_we              <= reg_cmd_cs and reg_part_we;
   reg_min_frame_len_we    <= reg_min_frame_len_cs and reg_part_we;
   reg_max_frame_len_we    <= reg_max_frame_len_cs and reg_part_we;
   reg_mac_check_mode_we   <= reg_mac_check_mode_cs and reg_part_we;

   -- Contols CS signals of the registers according to mi_int_addr
   chip_selectp: process(mi_int_addr(5 downto 2))
   begin
      reg_ibuf_en_cs             <= '0';
      reg_error_mask_cs          <= '0';
      reg_status_cs              <= '0';
      reg_cmd_cs                 <= '0';
      reg_min_frame_len_cs       <= '0';
      reg_max_frame_len_cs       <= '0';
      reg_mac_check_mode_cs      <= '0';

      case (mi_int_addr(5 downto 2)) is
         when REG_IBUF_EN_ADDR         => reg_ibuf_en_cs             <= '1';
         when REG_ERROR_MASK_ADDR      => reg_error_mask_cs          <= '1';
         when REG_STATUS_ADDR          => reg_status_cs              <= '1';
         when REG_CMD_ADDR             => reg_cmd_cs                 <= '1';
         when REG_MIN_FRAME_LEN_ADDR   => reg_min_frame_len_cs       <= '1';
         when REG_MAX_FRAME_LEN_ADDR   => reg_max_frame_len_cs       <= '1';
         when REG_MAC_CHECK_MODE_ADDR  => reg_mac_check_mode_cs      <= '1';
         when others =>
      end case;
   end process;

   -- CAM part --
   reg_cam_ins_data_low_cs    <= cam_part_cs and (not mi_int_addr(2));
   reg_cam_ins_data_high_cs   <= cam_part_cs and mi_int_addr(2);

   reg_cam_ins_data_low_we <= reg_cam_ins_data_low_cs and mi_int_wr;
   reg_cam_ins_data_high_we<=reg_cam_ins_data_high_cs and mi_int_wr;


   -- Reading part -------------------------------------------------------------
   -- Create 32-bit signals for each readable register with lower width
   reg_ibuf_en32           <= (31 downto 1 => '0') & reg_ibuf_en;
   reg_error_mask32        <= (31 downto 5 => '0') & reg_error_mask;
   reg_status32            <= (31 downto C_STATUS_LEN => '0') &
                              DEBUG_INFO &
                              BUF2MI.STATUS(BUF2MI.STATUS'length-1 downto
                              C_FSM_STATUS_DEBUG_L) &
                              "11" & -- Usefull for SW tools
                              reg_status;
   reg_min_frame_len32     <= (31 downto 16 => '0') & reg_min_frame_len;
   reg_max_frame_len32     <= (31 downto 16 => '0') & reg_max_frame_len;
   reg_mac_check_mode32    <= (31 downto 2 => '0') & reg_mac_check_mode;

   -- Create 32-bit signals dor CAM output
   -- note that SW access is little endian, but matching has to be big endian
   -- http://en.wikipedia.org/wiki/MAC_address
   cami_data_out32h(31 downto 17) <= (others => '0'); -- not used
   cami_data_out32h(16)           <= cami_data_out(48); -- validity bit
   cami_data_out32h(15 downto 8)  <= cami_data_out(7 downto 0); -- MSB
   cami_data_out32h(7 downto 0)   <= cami_data_out(15 downto 8);
   cami_data_out32l(31 downto 24) <= cami_data_out(23 downto 16);
   cami_data_out32l(23 downto 16) <= cami_data_out(31 downto 24);
   cami_data_out32l(15 downto 8)  <= cami_data_out(39 downto 32);
   cami_data_out32l(7 downto 0)   <= cami_data_out(47 downto 40); -- LSB

   -- CAM part --
   cam_read <= cam_part_cs and mi_int_rd;


   -- Output register multiplexer
   mx_decoder_data_outp: process(mi_int_addr(5 downto 2), reg_trfc, reg_cfc,
      reg_dfc, reg_bodfc, reg_ibuf_en32, reg_error_mask32, reg_status32, 
      reg_min_frame_len32, reg_max_frame_len32, reg_mac_check_mode32)
   begin
      case (mi_int_addr(5 downto 2)) is
         when REG_TRFC_L_ADDR =>
            mx_decoder_data_out <= reg_trfc(31 downto 0);
         when REG_CFC_L_ADDR =>
            mx_decoder_data_out <= reg_cfc(31 downto 0);
         when REG_DFC_L_ADDR =>
            mx_decoder_data_out <= reg_dfc(31 downto 0);
         when REG_BODFC_L_ADDR =>
            mx_decoder_data_out <= reg_bodfc(31 downto 0);
         when REG_TRFC_H_ADDR =>
            mx_decoder_data_out <= reg_trfc(63 downto 32);
         when REG_CFC_H_ADDR =>
            mx_decoder_data_out <= reg_cfc(63 downto 32);
         when REG_DFC_H_ADDR =>
            mx_decoder_data_out <= reg_dfc(63 downto 32);
         when REG_BODFC_H_ADDR =>
            mx_decoder_data_out <= reg_bodfc(63 downto 32);
         when REG_IBUF_EN_ADDR =>
            mx_decoder_data_out <= reg_ibuf_en32;
         when REG_ERROR_MASK_ADDR =>
            mx_decoder_data_out <= reg_error_mask32;
         when REG_STATUS_ADDR =>
            mx_decoder_data_out <= reg_status32;
         when REG_MIN_FRAME_LEN_ADDR =>
            mx_decoder_data_out <= reg_min_frame_len32;
         when REG_MAX_FRAME_LEN_ADDR =>
            mx_decoder_data_out <= reg_max_frame_len32;
         when REG_MAC_CHECK_MODE_ADDR =>
            mx_decoder_data_out <= reg_mac_check_mode32;
         when others =>
            mx_decoder_data_out <= (others => '0');
      end case;
   end process;

   -- multiplexor mx_cam_do
   mx_cam_do_sel <= reg_read_part;
   mx_cam_dop: process(mx_cam_do_sel, cami_data_out32h, cami_data_out32l)
   begin
      case mx_cam_do_sel is
         when '0' => mx_cam_do <= cami_data_out32l;
         when '1' => mx_cam_do <= cami_data_out32h;
         when others => mx_cam_do <= (others => 'X');
      end case;
   end process;

   -- multiplexor mx_decoder_mi_rd
   mx_decoder_mi_rd_sel <= cam_part_cs;
   mx_decoder_mi_rdp: process(mx_decoder_mi_rd_sel, mx_decoder_data_out, mx_cam_do)
   begin
      case mx_decoder_mi_rd_sel is
         when '0' => mx_decoder_mi_rd <= mx_decoder_data_out;
         when '1' => mx_decoder_mi_rd <= mx_cam_do;
         when others => mx_decoder_mi_rd <= (others => 'X');
      end case;
   end process;



   -- ----------------------------------------------------------------------------
   --                   Data provided to other components
   -- ----------------------------------------------------------------------------

   MI2BUF.IBUF_EN    <= reg_ibuf_en;
   MI2BUF.ERROR_MASK <= reg_error_mask;
   MI2BUF.CNT_RESET  <= reset_counters;

   MI2CHECK.MIN_FRAME_LEN  <= reg_min_frame_len;
   MI2CHECK.MAX_FRAME_LEN  <= reg_max_frame_len;
   MI2CHECK.MAC_CHECK_MODE <= reg_mac_check_mode;

end architecture MI_INT_ARCH;
