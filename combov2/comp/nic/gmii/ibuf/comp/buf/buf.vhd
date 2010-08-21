--
-- ibuf_gmii_buf.vhd: Input buffer for GMII - buffer part
-- Copyright (C) 2005 CESNET
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
--            Martin Mikusek <martin.mikusek@liberouter.org>
--            Libor Polcak <polcak_l@liberouter.org>
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
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;
use work.cnt_types.all;
use work.ibuf_pkg.all;
use work.ibuf_common_pkg.all;
use work.ibuf_general_pkg.all;
use work.fifo_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity ibuf_gmii_buf is
   generic(
      -- Greater or equal than 2
      DATA_PATHS  : integer := 2;
      -- Number of items in Data FIFO (FL_WIDTH_TX + control signals wide).
      -- !!!!!!!!!!! Must be (2^n), n>=2 !!!!!!!!!!!!!!!!!!!!!!
      DFIFO_SIZE  : integer := 1024;
      -- Number of items in Header and Footer FIFO
      HFIFO_SIZE  : integer := 256
   );
   port(
      RESET   : in  std_logic;

      -- ibuf_gmii_rx interface
      WRCLK       : in  std_logic;
      DI          : in  std_logic_vector(7 downto 0);
      DI_DV       : in  std_logic;
      RX_STAT     : in  t_ibuf_rx_stat;
      SOP         : in  std_logic;
      EOP         : in  std_logic;
      SPEED       : out std_logic_vector(1 downto 0);

      -- Debug interface
      FSM_RX_STATE : in std_logic_vector(2 downto 0);

      -- PACODAG interface
      CTRL_DI        : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      CTRL_REM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      CTRL_SRC_RDY_N : in std_logic;
      CTRL_SOP_N     : in std_logic;
      CTRL_EOP_N     : in std_logic;
      CTRL_DST_RDY_N : out std_logic;
      CTRL_SOP       : out std_logic;
      CTRL_RDY       : in std_logic;
      CTRL_STAT      : out t_ibuf_general_stat;
      CTRL_STAT_DV   : out std_logic;

      -- MAC check interface
      EN       : out std_logic;   -- IBUF enable bit. MAC Memory cannot be accessed by PCI when asserted.
      MAC_IN   : out std_logic_vector(47 downto 0);
      CHECK    : out std_logic;
      CHECK_FIN   : in std_logic;
      MAC_MATCH   : in std_logic;
      MULTICAST   : in std_logic;
      BROADCAST   : in std_logic;

      -- sampling unit interface
      SAU_ACCEPT : in std_logic;
      SAU_DV     : in std_logic;

      -- FL interface
      RDCLK       : in  std_logic;

      -- Payload
      -- Data
      TX_DATA        : out std_logic_vector(DATA_PATHS*8-1 downto 0);
      -- Position of the end of the part, valid only if TX_EOP_N is set to '0'.
      TX_REM         : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      -- Start of the part, active in '0'
      TX_SOP_N       : out std_logic;
      -- End of the packet, active in '0'.
      TX_EOP_N       : out std_logic;
      -- Source is ready, active in '0'
      TX_SRC_RDY_N   : out std_logic;
      -- Destination is ready, active in '0'
      TX_DST_RDY_N   : in std_logic;

      -- Packet headres/footers
      -- Part data
      TX_HDATA       : out std_logic_vector(DATA_PATHS*8-1 downto 0);
      -- Position of the end of the part, valid only if TX_HEOP_N is set to '0'.
      TX_HREM        : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      -- Start of the part, active in '0'
      TX_HSOP_N      : out std_logic;
      -- End of the packet, active in '0'.
      TX_HEOP_N      : out std_logic;
      -- Source is ready, active in '0'
      TX_HSRC_RDY_N  : out std_logic;
      -- Destination is ready, active in '0'
      TX_HDST_RDY_N  : in std_logic;

      -- Address decoder interface
      ADC_CLK     : out std_logic;
      ADC_RD      : in  std_logic; -- Read Request
      ADC_WR      : in  std_logic; -- Write Request
      ADC_ADDR    : in  std_logic_vector(3 downto 0);  -- Address
      ADC_DI      : in  std_logic_vector(31 downto 0); -- Input Data
      ADC_DO      : out std_logic_vector(31 downto 0);  -- Output Data
      ADC_DRDY    : out std_logic
   );
end entity ibuf_gmii_buf;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ibuf_gmii_buf is

   signal ADC_DO_i      :  std_logic_vector(31 downto 0);

   -- IBUF Counters
   signal cnt_packets      : std_logic_vector(63 downto 0);
   signal cnt_recv         : std_logic_vector(63 downto 0);
   signal cnt_recverr      : std_logic_vector(63 downto 0);
   signal cnt_bufovferr    : std_logic_vector(63 downto 0);

   -- Command comparators
   signal strobe_counters_c : std_logic;
   signal reset_counters_c  : std_logic;
   signal set_speed10_c     : std_logic;
   signal set_speed100_c    : std_logic;
   signal set_speed1000_c   : std_logic;

   -- ADC signals
   signal reg_cnt_packets  : std_logic_vector(63 downto 0);
   signal reg_cnt_recv     : std_logic_vector(63 downto 0);
   signal reg_cnt_recverr  : std_logic_vector(63 downto 0);
   signal reg_cnt_bufovferr: std_logic_vector(63 downto 0);
   signal reg_cnts_ce      : std_logic;
   signal reg_errmask      : std_logic_vector(7 downto 0);
   signal reg_enable       : std_logic;

   signal cs_cnt_packets_l    : std_logic;
   signal cs_cnt_recv_l       : std_logic;
   signal cs_cnt_recverr_l    : std_logic;
   signal cs_cnt_bufovferr_l  : std_logic;
   signal cs_cnt_packets_h    : std_logic;
   signal cs_cnt_recv_h       : std_logic;
   signal cs_cnt_recverr_h    : std_logic;
   signal cs_cnt_bufovferr_h  : std_logic;

   signal cs_reg_enable    : std_logic;
   signal cs_reg_errmask   : std_logic;
   signal cs_reg_ibuf_status  : std_logic;
   signal cs_reg_ibuf_ctrl : std_logic;
   signal cs_reg_min_len   : std_logic;
   signal cs_reg_mtu       : std_logic;
   signal cs_reg_mac_check : std_logic;

   -- Control signals
   signal reg_sau_acc      : std_logic;
   signal reg_ibuf_status  : std_logic_vector(31 downto 0);

   -- Payload counter
   signal cnt_pld_len : std_logic_vector(15 downto 0);
   signal cnt_pld_len_load : std_logic;
   signal cnt_pld_len_ce : std_logic;

   -- Minimum frame length register
   signal reg_min_len : std_logic_vector(15 downto 0);
   signal reg_min_len_we : std_logic;
   signal len_below_min : std_logic;
   -- MTU register
   signal reg_mtu : std_logic_vector(15 downto 0);
   signal reg_mtu_we : std_logic;
   signal len_over_mtu : std_logic;
   -- MAC check
   signal mac_check_failed : std_logic;
   signal reg_mac_check : std_logic_vector(1 downto 0);
   signal reg_mac : std_logic_vector(47 downto 0);
   signal reg_mac_vld   : std_logic_vector(5 downto 0);
   signal reg_mac_valid : std_logic;
--   signal reg_mac_we : std_logic_vector(5 downto 0);
   signal reg_check  : std_logic;

   -- speed register
   signal reg_speed : std_logic_vector(1 downto 0);

   -- Buf core signals
   signal buf2mi        : t_buf2mi;
   signal mi2buf        : t_mi2buf;
   signal core_stat_in  : t_stats;

begin

   -- -------------------------------------------------------------
   -- ADRESS DECODER
   -- -------------------------------------------------------------
   ADC_CLK <= WRCLK;
   
   cs_cnt_packets_l   <= '1' when (ADC_ADDR="0000") else '0'; -- 00
   cs_cnt_recv_l      <= '1' when (ADC_ADDR="0001") else '0'; -- 04
   cs_cnt_recverr_l   <= '1' when (ADC_ADDR="0010") else '0'; -- 08
   cs_cnt_bufovferr_l <= '1' when (ADC_ADDR="0011") else '0'; -- 0C
   cs_cnt_packets_h   <= '1' when (ADC_ADDR="0100") else '0'; -- 10
   cs_cnt_recv_h      <= '1' when (ADC_ADDR="0101") else '0'; -- 14
   cs_cnt_recverr_h   <= '1' when (ADC_ADDR="0110") else '0'; -- 18
   cs_cnt_bufovferr_h <= '1' when (ADC_ADDR="0111") else '0'; -- 1C
   
   cs_reg_enable  <= '1' when (ADC_ADDR="1000") else '0'; -- 20
   cs_reg_errmask <= '1' when (ADC_ADDR="1001") else '0'; -- 24
   cs_reg_ibuf_status <= '1' when (ADC_ADDR="1010") else '0'; -- 28
   cs_reg_ibuf_ctrl   <= '1' when (ADC_ADDR="1011") else '0'; -- 2C
   cs_reg_min_len <= '1' when (ADC_ADDR="1100") else '0'; -- 30
   cs_reg_mtu     <= '1' when (ADC_ADDR="1101") else '0'; -- 34
   cs_reg_mac_check  <= '1' when (ADC_ADDR="1110") else '0'; -- 38
   
   reg_adc_do_p: process (WRCLK, RESET)
   begin
      if (RESET='1') then
         ADC_DO <= (others=>'0');
      elsif (WRCLK'event and WRCLK='1') then
         ADC_DO <= ADC_DO_i;
      end if;
   end process;

   ADC_DO_i <= X"0000000" & "000" & reg_enable when (cs_reg_enable='1')  else --enable
               X"000000" & reg_errmask         when (cs_reg_errmask='1') else --errmask
               reg_ibuf_status                 when (cs_reg_ibuf_status='1') else -- ibuf_status
               X"0000"   & reg_min_len         when (cs_reg_min_len='1') else -- reg_min_len
               X"0000"   & reg_mtu             when (cs_reg_mtu='1') else -- reg_mtu
               X"0000000" & "00" & reg_mac_check   when (cs_reg_mac_check='1') else -- reg_mac_check
               reg_cnt_packets(31 downto 0)    when (cs_cnt_packets_l='1') else --cnt_packets
               reg_cnt_recv(31 downto 0)       when (cs_cnt_recv_l='1')    else --cnt_recv
               reg_cnt_recverr(31 downto 0)    when (cs_cnt_recverr_l='1') else --cnt_recverr
               reg_cnt_bufovferr(31 downto 0)  when (cs_cnt_bufovferr_l='1') else --cnt_bufovferr
               reg_cnt_packets(63 downto 32)    when (cs_cnt_packets_h='1') else --cnt_packets
               reg_cnt_recv(63 downto 32)       when (cs_cnt_recv_h='1')    else --cnt_recv
               reg_cnt_recverr(63 downto 32)    when (cs_cnt_recverr_h='1') else --cnt_recverr
               reg_cnt_bufovferr(63 downto 32)  when (cs_cnt_bufovferr_h='1') else --cnt_bufovferr
	            (others=>'0');
   
   reg_adc_p: process (WRCLK, RESET)
   begin
      if (RESET='1') then
         ADC_DRDY   <= '0';
      elsif (WRCLK'event and WRCLK='1') then
         ADC_DRDY   <= ADC_RD; -- drdy is delayed adc_rd         
      end if;
   end process;

   -- -------------------------------------------------------------
   -- Enable register
   -- -------------------------------------------------------------
   reg_enable_p: process (RESET, WRCLK)
   begin
      if (RESET='1') then
         reg_enable <= '0';
      elsif (WRCLK'event and WRCLK='1') then
         if (ADC_WR='1' and cs_reg_enable='1') then
            reg_enable <= ADC_DI(0);
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------
   -- Error mask register
   -- -------------------------------------------------------------
   -- error masking comparator
   -- 4: Bad MAC address
   -- 3: Frame Length over MTU
   -- 2: Frame Length below min
   -- 1: Bad CRC
   -- 0: GMII error
   reg_errmask_p: process (RESET, WRCLK)
   begin
      if (RESET='1') then
         reg_errmask <= (others=>'1');
      elsif (WRCLK'event and WRCLK='1') then
         if (ADC_WR='1' and cs_reg_errmask='1') then
            reg_errmask <= ADC_DI(7 downto 0);
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------
   -- Minimum Length register
   -- -------------------------------------------------------------
   reg_min_len_we <= ADC_WR and cs_reg_min_len;
   process(RESET, WRCLK)
   begin
      if (RESET = '1') then
         reg_min_len <= x"0040"; -- 64 bytes
      elsif (WRCLK'event AND WRCLK = '1') then
         if (reg_min_len_we = '1') then
            reg_min_len <= ADC_DI(15 downto 0);
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------
   -- MTU register
   -- -------------------------------------------------------------
   reg_mtu_WE <= ADC_WR and cs_reg_mtu;
   process(RESET, WRCLK)
   begin
      if (RESET = '1') then
         reg_mtu <= x"05f6";   -- 1526 bytes
      elsif (WRCLK'event AND WRCLK = '1') then
         if (reg_mtu_we = '1') then
            reg_mtu <= ADC_DI(15 downto 0);
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------
   -- IBUF status register
   -- -------------------------------------------------------------
   process (RESET, WRCLK)
   begin
      if (RESET='1') then
         reg_ibuf_status <= (others=>'0');
      elsif (WRCLK'event and WRCLK='1') then
         if (ADC_WR='1' and cs_reg_ibuf_status='1') then
            reg_ibuf_status <= (others => '0');    -- clear the register
         else
            if (buf2mi.STATUS(C_PACODAG_OVF_POS) = '1') then
               reg_ibuf_status(0) <= '1';
            end if;
            if buf2mi.STATUS(C_DFIFO_OVF_POS) = '1' then
               reg_ibuf_status(1) <= '1';
            end if;
            if (buf2mi.STATUS(C_FR_DISCARDED_POS) = '1') then
               reg_ibuf_status(2) <= '1';
            end if;
            if (buf2mi.STATUS(C_BUFFER_OVF_POS) = '1') then
               reg_ibuf_status(3) <= '1';
            end if;
--            reg_ibuf_status(1) <= SGMII;
--            reg_ibuf_status(4) <= LINK_STATUS;
--            reg_ibuf_status(5) <= DUPLEX_MODE;
--            reg_ibuf_status(7 downto 6) <= SPEED;
            reg_ibuf_status(5 downto 4) <= reg_speed;

            -- IBUF FSMs STATE
            reg_ibuf_status(10 downto 8) <= FSM_RX_STATE;
            reg_ibuf_status(11) <= buf2mi.STATUS(C_FSM_STATUS_DEBUG_L);
            reg_ibuf_status(12) <= buf2mi.STATUS(C_FSM_STATUS_DEBUG_H);
            reg_ibuf_status(13) <= buf2mi.STATUS(C_DFIFO_EMPTY_POS);
            reg_ibuf_status(14) <= buf2mi.STATUS(C_DFIFO_FULL_POS);
            reg_ibuf_status(15) <= buf2mi.STATUS(C_HFIFO_EMPTY_POS);
            reg_ibuf_status(16) <= buf2mi.STATUS(C_HFIFO_FULL_POS);
            -- reg_ibuf_status(14 downto 12) <= FSM_FL_STATE;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------
   -- IBUF control register
   -- -------------------------------------------------------------
   strobe_counters_c <= '1' when (ADC_DI(7 downto 0) = IBUFCMD_STROBE_COUNTERS) and
                        (cs_reg_ibuf_ctrl = '1') and (ADC_WR = '1') else
                        '0';
   reset_counters_c  <= '1' when (ADC_DI(7 downto 0) = IBUFCMD_RESET_COUNTERS) and
                        (cs_reg_ibuf_ctrl = '1') and (ADC_WR = '1')  else
                        '0';
   set_speed10_c     <= '1' when (ADC_DI(7 downto 0) = IBUFCMD_SET_SPEED10) and
                        (cs_reg_ibuf_ctrl = '1') and (ADC_WR = '1')  else
                        '0';
   set_speed100_c    <= '1' when (ADC_DI(7 downto 0) = IBUFCMD_SET_SPEED100) and
                        (cs_reg_ibuf_ctrl = '1') and (ADC_WR = '1')  else
                        '0';
   set_speed1000_c   <= '1' when (ADC_DI(7 downto 0) = IBUFCMD_SET_SPEED1000) and
                        (cs_reg_ibuf_ctrl = '1') and (ADC_WR = '1')  else
                        '0';

   -- -------------------------------------------------------------
   -- Speed settings
   -- -------------------------------------------------------------
   process(RESET, WRCLK)
   begin
      if (RESET = '1') then
         reg_speed <= "10";  -- 1000Mb as a default
      elsif (WRCLK'event AND WRCLK = '1') then
         if (set_speed10_c = '1' or set_speed100_c = '1' or set_speed1000_c = '1') then
            reg_speed <= ADC_DI(1 downto 0);
         end if;
      end if;
   end process;
   SPEED <= reg_speed;
   
   -- -------------------------------------------------------------
   -- Packet Counters
   -- -------------------------------------------------------------
   cnt_packets <= buf2mi.TRFC;
   cnt_recv <= buf2mi.CFC;
   cnt_recverr <= buf2mi.DFC;
   cnt_bufovferr <= buf2mi.BODFC;

   -- strobe counters registers
   process (WRCLK)
   begin
      if (WRCLK'event and WRCLK='1') then
         if (strobe_counters_c='1') then
            reg_cnts_ce <= '1';
         else
            reg_cnts_ce <= '0';
         end if;
      end if;
   end process;

   process (WRCLK)
   begin
      if (WRCLK'event and WRCLK='1') then
         if (reg_cnts_ce = '1') then
            reg_cnt_packets <= cnt_packets;
            reg_cnt_recv <= cnt_recv;
            reg_cnt_recverr <= cnt_recverr;
            reg_cnt_bufovferr <= cnt_bufovferr;
         end if;
      end if;
   end process;

   ----------------------------------------------------------------------------
   --                           MI2BUF
   ----------------------------------------------------------------------------
   mi2buf.IBUF_EN <= reg_enable;
   mi2buf.ERROR_MASK <= reg_errmask(4 downto 0);
   mi2buf.CNT_RESET <= reset_counters_c;


   -- -------------------------------------------------------------
   -- MAC CHECK unit
   -- -------------------------------------------------------------
   EN <= reg_enable;
   MAC_IN <= reg_mac;

   ----------------------------
   -- 0 - promiscuous mode
   -- 1 - pass only matching addresses
   -- 2 - 1+ broadcast
   -- 3 - 2+ all multicast frames
   process(RESET, WRCLK)
   begin
      if (RESET = '1') then
         reg_mac_check <= (others => '0');
      elsif (WRCLK'event AND WRCLK = '1') then
         if (ADC_WR='1' and cs_reg_mac_check='1') then
            reg_mac_check <= ADC_DI(1 downto 0);
         end if;
      end if;
   end process;

   p_mac_check: process(RESET, WRCLK)
   begin
      if (WRCLK'event AND WRCLK = '1') then
         if (SOP = '1' and DI_DV = '1') then
            mac_check_failed <= '0';
         elsif ((CHECK_FIN = '1') and (reg_errmask(4) = '1')) then
            if (reg_mac_check = "01") then
               mac_check_failed <= not MAC_MATCH;
            elsif (reg_mac_check = "10") then
               mac_check_failed <= (not MAC_MATCH) and (not BROADCAST);
            elsif (reg_mac_check = "11") then
               mac_check_failed <= (not MAC_MATCH) and (not BROADCAST) and (not MULTICAST);
            end if;
         end if;
      end if;
   end process;

   -- Control the moment when MAC valid signal should be active
   process(RESET, WRCLK)
   begin
      if (RESET = '1') then
         reg_mac_vld(0) <= '0';
      elsif (WRCLK'event and WRCLK='1') then
         if (DI_DV = '1') then
            reg_mac_vld(0) <= SOP and DI_DV;
         end if;
      end if;
   end process;

   reg_mac_vld_gen: for i in 1 to 5 generate
      process(RESET, WRCLK)
      begin
         if (RESET = '1') then
            reg_mac_vld(i) <= '0';
         elsif (WRCLK'event AND WRCLK = '1') then
            if (EOP = '1' and DI_DV = '1') then
               reg_mac_vld(i) <= '0';
            elsif (DI_DV = '1') then
               reg_mac_vld(i) <= reg_mac_vld(i-1);
            end if;
         end if;
      end process;
   end generate;
   reg_mac_valid <= reg_mac_vld(5);


   -- Store MAC address to be sent when it is received completely
   process(RESET, WRCLK)
   begin
      if (WRCLK'event AND WRCLK = '1') then
         if (reg_mac_valid = '1' and DI_DV = '1') then
            reg_mac(7 downto 0) <= DI;
         end if;
      end if;
   end process;

   reg_mac_gen: for i in 0 to 5 generate
      process(RESET, WRCLK)
      begin
         if (WRCLK'event AND WRCLK = '1') then
            if (reg_mac_vld(5-i) = '1' and DI_DV = '1') then
               reg_mac(((i+1)*8)-1 downto (i*8)) <= DI;
            end if;
         end if;
      end process;
   end generate;

   -- Control the moment when the MAC address is ready
   process(RESET, WRCLK)
   begin
      if (RESET = '1') then
         reg_check <= '0';
      elsif (WRCLK'event AND WRCLK = '1') then
         if (DI_DV = '1') then
            reg_check <= reg_mac_valid;
         end if;
      end if;
   end process;
   CHECK <= reg_check and DI_DV;


   -- -------------------------------------------------------------
   -- STATUS port logic
   -- -------------------------------------------------------------

   cnt_pld_len_load <= SOP and DI_DV;
   cnt_pld_len_ce <= DI_DV and not EOP;
   process(RESET, WRCLK)
   begin
      if (WRCLK'event AND WRCLK = '1') then
         if (cnt_pld_len_load = '1') then
            -- It has to be 2 because of SOP and EOP (value of the counter
            -- has to be valid when EOP arrives)
            cnt_pld_len <= conv_std_logic_vector(2, cnt_pld_len'length);
         elsif (cnt_pld_len_ce='1') then
            cnt_pld_len <= cnt_pld_len + 1;
         end if;
      end if;
   end process;

   len_below_min <= '1' when RX_STAT.FRAME_LEN < reg_min_len else
                    '0';
   len_over_mtu  <= '1' when RX_STAT.FRAME_LEN > reg_mtu else
                    '0';

   process(RESET,WRCLK)
   begin
      if (RESET='1') then
         reg_sau_acc <= '0';
      elsif (WRCLK'event and WRCLK='1') then
         if (SAU_DV='1') then
            reg_sau_acc <= SAU_ACCEPT;
         end if;
      end if;
   end process;


   ----------------------------------------------------------------------------
   --                          Statistic
   ----------------------------------------------------------------------------

   core_stat_in.MAC_ERR <= mac_check_failed;
   core_stat_in.MINTU_ERR <= len_below_min;
   core_stat_in.MTU_ERR <= len_over_mtu;
   core_stat_in.SAU_ERR <= not reg_sau_acc;
   core_stat_in.SAU_ERR_VLD <= EOP;
   core_stat_in.CRC_ERR <= RX_STAT.CRC_CHECK_FAILED;
   core_stat_in.FRAME_LEN <= cnt_pld_len;

   ----------------------------------------------------------------------------
   --                            CORE
   ----------------------------------------------------------------------------
   buf_corei: entity work.common_ibuf_buf
      generic map (
         -- Number of items in Data FIFO (FL_WIDTH_TX + control signals wide).
         -- !!!!!!!!!!! Must be (2^n)-1, n>=2 !!!!!!!!!!!!!!!!!!!!!!
         DFIFO_SIZE     => DFIFO_SIZE,
         -- Number of items in Header and Footer FIFO
         -- (FL_WIDTH_TX + control signals wide)
         HFIFO_SIZE     => HFIFO_SIZE,
         -- Type of the memory used in HFIFO
         HFIFO_MEMTYPE  => BRAM,
         -- FrameLink output width (at least 64)
         FL_WIDTH_TX    => DATA_PATHS * 8,
         -- RX data width
         RX_WIDTH       => 8
      )
      port map (
         -- Common IBUF signals
         -- Clock sigal
         CLK            => WRCLK,
         -- Asynchronous reset, active in '1'
         RESET          => RESET,

         -- Input
         -- Packet data
         RX_DATA        => DI,
         -- RX data is valid
         RX_DV          => DI_DV,
         -- Start of the packet, active in '1'
         RX_SOP         => SOP,
         -- End of the packet, active in '1'.
         RX_EOP         => EOP,
         -- Position of the end of the packet, valid only if RX_EOP is set to '1'.
         RX_EOP_POS     => "0",
         -- Error inside the packet was detected, active in '1'.
         RX_ERR         => RX_STAT.GMII_ERROR,

         -- Input statistic data
         RX_STAT        => core_stat_in,
         -- Statistics valid signal
 	 RX_STAT_DV	=> EOP,

         -- Output
         -- Output clock
         FL_CLK         => RDCLK,

         -- Payload
         -- Data
         TX_DATA        => TX_DATA,
         -- Position of the end of the part, valid only if TX_EOP_N is set to '0'.
         TX_REM         => TX_REM,
         -- Start of the part, active in '0'
         TX_SOP_N       => TX_SOP_N,
         -- End of the packet, active in '0'.
         TX_EOP_N       => TX_EOP_N,
         -- Source is ready, active in '0'
         TX_SRC_RDY_N   => TX_SRC_RDY_N,
         -- Destination is ready, active in '0'
         TX_DST_RDY_N   => TX_DST_RDY_N,

         -- Packet headres/footers
         -- Part data
         TX_HDATA       => TX_HDATA,
         -- Position of the end of the part, valid only if TX_HEOP_N is set to '0'.
         TX_HREM        => TX_HREM,
         -- Start of the part, active in '0'
         TX_HSOP_N      => TX_HSOP_N,
         -- End of the packet, active in '0'.
         TX_HEOP_N      => TX_HEOP_N,
         -- Source is ready, active in '0'
         TX_HSRC_RDY_N  => TX_HSRC_RDY_N,
         -- Destination is ready, active in '0'
         TX_HDST_RDY_N  => TX_HDST_RDY_N,

         -- MI_INT Interface
         MI2BUF         => mi2buf,
         BUF2MI         => buf2mi,

         -- Control data generator interface
         -- Control data
         CTRL_DATA         => CTRL_DI,
         -- Specifies the number of valid bytes in the last CTRL_DATA beat;
         -- valid only when CTRL_EOP is asserted
         CTRL_REM          => CTRL_REM,
         -- Asserted when the input signals from control data generator are valid
         CTRL_SRC_RDY_N    => CTRL_SRC_RDY_N,
         -- Signals the start of the incoming control data
         CTRL_SOP_N        => CTRL_SOP_N,
         -- Signals the end of the incoming control data
         CTRL_EOP_N        => CTRL_EOP_N,
         -- Asserted when data from control data generator will be accepted
         CTRL_DST_RDY_N    => CTRL_DST_RDY_N,
         -- New frame is being received; prepare to generate new control data
         CTRL_SOP          => CTRL_SOP,
         -- Control data generator is ready to receive new request
         CTRL_RDY          => CTRL_RDY,
         -- Output statistic data
         CTRL_STAT         => CTRL_STAT,
         -- Output statistic data is valid
         CTRL_STAT_DV      => CTRL_STAT_DV
     );

end architecture full;

