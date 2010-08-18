-- sum_arch.vhd: status update manager architecture
-- Copyright (C) 2009 CESNET
-- Author(s): Petr Kastovsky <kastovsky@liberouter.org>
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
-- KEYWORDS : TODO, DEBUG
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;
use work.pac_dma_pkg.all;
-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture sum_behav of sum is

   constant BM_REQ_DISTMEM_TYPE : integer := 16;

   -- round up number to the multiple of 8
   function ROUND_UP8 ( number : integer) return integer is
   variable ret : integer;
   begin
      ret := (number / 8)*8;
      if ( (number mod 8) /= 0) then
         ret := ret + 8;
      end if;
      return ret;
   end ROUND_UP8;

   type TCNT_VARRAY is array (0 to IFCS-1) of std_logic_vector(31 downto 0);
   type T_VARRAY is array (0 to 2*IFCS-1) of std_logic_vector(31 downto 0);

   constant gndvec         : std_logic_vector(63 downto 0) := (others => '0');
   constant RXUP_NFIFO_BLOCK_SIZE : integer := BLOCK_SIZE*4;
   constant RXUP_STATUS_WIDTH     : integer := log2(RXUP_NFIFO_BLOCK_SIZE+1);

   constant LENGTH_WIDTH      : integer := log2(BLOCK_SIZE+1);
   constant LENGTH_DW         : integer := ROUND_UP8(LENGTH_WIDTH);
   constant GADDR_WIDTH       : integer := 64;
   constant TX_BM_LENGTH      : integer := ROUND_UP8(IFCS*4);
   constant NFIFO_OUTPUT_REG  : boolean := false;
   constant TRANS_TYPE        : std_logic_vector := "01";

   signal tx_cnt_array     : TCNT_VARRAY;
   signal tx_cnt_ce        : std_logic_vector(IFCS-1 downto 0);
   signal tx_cnt_ld        : std_logic_vector(IFCS-1 downto 0);

   signal rx_update_len    : std_logic_vector(LENGTH_DW-1 downto 0);
   signal ra_length_sclr   : std_logic;
   signal ra_length_wea    : std_logic;
   signal ra_length_bea    : std_logic_vector((LENGTH_DW/8)-1 downto 0);
   signal ra_length_addra  : std_logic_vector(log2(IFCS)-1 downto 0);
   signal ra_length_dia    : std_logic_vector(LENGTH_DW-1 downto 0);
   signal ra_length_doa    : std_logic_vector(LENGTH_DW-1 downto 0);

   signal ra_gaddr_sclr    : std_logic;
   signal ra_gaddr_wea     : std_logic;
   signal ra_gaddr_bea     : std_logic_vector((GADDR_WIDTH/8)-1 downto 0);
   signal ra_gaddr_addra   : std_logic_vector(log2(IFCS)-1 downto 0);
   signal ra_gaddr_dia     : std_logic_vector(GADDR_WIDTH-1 downto 0);
   signal ra_gaddr_doa     : std_logic_vector(GADDR_WIDTH-1 downto 0);

   signal ra_swcnt_sclr   : std_logic;
   signal ra_swcnt_wea    : std_logic;
   signal ra_swcnt_bea    : std_logic_vector(3 downto 0);
   signal ra_swcnt_addra  : std_logic_vector(log2(IFCS)-1 downto 0);
   signal ra_swcnt_dia    : std_logic_vector(31 downto 0);
   signal ra_swcnt_doa    : std_logic_vector(31 downto 0);
   signal ra_swcnt_addrb  : std_logic_vector(log2(IFCS)-1 downto 0);
   signal ra_swcnt_dob    : std_logic_vector(31 downto 0);

   signal ra_hwcnt_sclr   : std_logic;
   signal ra_hwcnt_wea    : std_logic;
   signal ra_hwcnt_bea    : std_logic_vector(3 downto 0);
   signal ra_hwcnt_addra  : std_logic_vector(log2(IFCS)-1 downto 0);
   signal ra_hwcnt_dia    : std_logic_vector(31 downto 0);
   signal ra_hwcnt_doa    : std_logic_vector(31 downto 0);
   signal ra_hwcnt_addrb  : std_logic_vector(log2(IFCS)-1 downto 0);
   signal ra_hwcnt_dob    : std_logic_vector(31 downto 0);
   signal reg_hwcnt_dia   : std_logic_vector(31 downto 0);

   signal mux_gaddr_dia    : std_logic_vector(GADDR_WIDTH-1 downto 0);
   signal mux_gaddr_dia_sel : std_logic;

   signal cnt_chid         : std_logic_vector(log2(IFCS+1)-1 downto 0);
   signal cnt_chid_ce      : std_logic;
   signal cnt_chid_ld      : std_logic;

   signal enable_rx        : std_logic;
   signal enable_tx        : std_logic;

   signal rxup_enable            : std_logic;
   signal rxup_flag_get          : std_logic;
   signal rxup_length_nz         : std_logic;
   signal rxup_status_nz         : std_logic;
   signal rxup_length_lte_status : std_logic;
   signal rxup_flush             : std_logic;
   signal rxup_req_fifo_empty    : std_logic;
   signal rxup_req_fifo_dv       : std_logic;
   signal rxup_timeout           : std_logic;
   signal rxup_bm_ack            : std_logic;
   signal rxup_swhw_diff         : std_logic;

   signal rxup_next_chid   : std_logic;
   signal rxup_bm_req      : std_logic;
   signal rxup_length_we   : std_logic;
   signal rxup_reqw1       : std_logic;
   signal rxup_reqw2       : std_logic;
   signal rxup_flag_set    : std_logic;
   signal rxup_req_fifo_rd : std_logic;
   signal rxup_update      : std_logic;
   signal rxup_update_we   : std_logic;
   signal rxup_tint        : std_logic;

   signal rxup_nfifo_init     : std_logic_vector(IFCS-1 downto 0);
   signal rxup_nfifo_dout     : std_logic_vector(NUM_FLAGS+16-1 downto 0);
   signal rxup_nfifo_dout_vld : std_logic;
   signal rxup_nfifo_raddr    : std_logic_vector(abs(log2(IFCS)-1) downto 0);
   signal rxup_nfifo_rd       : std_logic;
   signal rxup_nfifo_pipe_en  : std_logic;
   signal rxup_nfifo_empty    : std_logic_vector(IFCS-1 downto 0);
   signal rxup_nfifo_status   : std_logic_vector(RXUP_STATUS_WIDTH*IFCS-1 downto 0);

   signal rx_actlen           : std_logic_vector(LENGTH_DW-1 downto 0);
   signal reg_rx_actlen       : std_logic_vector(LENGTH_DW-1 downto 0);
   signal reg_rx_actlen_we    : std_logic;
   signal mux_rx_actlen_sel   : std_logic;
 
   signal mux_rx_rf_empty    : std_logic_vector(0 downto 0);
   signal mux_length_dia     : std_logic_vector(LENGTH_DW-1 downto 0);
   signal mux_length_dia_sel : std_logic;
   signal mux_rxup_nfifo_status : std_logic_vector(RXUP_STATUS_WIDTH-1 downto 0);

   signal ib_word_index       : std_logic_vector(8 downto 0);
   signal ib_channel_index    : std_logic_vector(log2(IFCS*2)-1 downto 0);
   signal ib_rx_cs            : std_logic;
   signal ib_tx_cs            : std_logic;
   signal rx_ib_rd_first_word : std_logic;

   signal mux_rd_data         : std_logic_vector(63 downto 0);
   signal mux_rd_data_sel     : std_logic;
   signal mux_rx_rd_data      : std_logic_vector(63 downto 0);
   signal mux_rx_rd_data_sel  : std_logic;
   signal mux_tx_rd_data      : std_logic_vector(63 downto 0);

   signal reg_tx_status       : std_logic_vector(IFCS-1 downto 0);
   signal reg_tx_status_set   : std_logic_vector(IFCS-1 downto 0);
   signal reg_tx_status_clr   : std_logic_vector(IFCS-1 downto 0);
   signal dec_tx_su_addr      : std_logic_vector(IFCS-1 downto 0);
   signal tx_status           : std_logic;

   signal dec_rx_chid         : std_logic_vector(IFCS-1 downto 0);
   signal dec_rx_su_addr      : std_logic_vector(IFCS-1 downto 0);
   signal su_addr_clr         : std_logic_vector(2*IFCS-1 downto 0);

   signal txup_enable      : std_logic;
   signal txup_flag_get    : std_logic;
   signal txup_timeout     : std_logic;
   signal txup_syncint     : std_logic;
   signal txup_flush       : std_logic;
   signal txup_tx_status   : std_logic;
   signal txup_bm_ack      : std_logic;
   signal txup_next_chid   : std_logic;
   signal txup_bm_req      : std_logic;
   signal txup_reqw1       : std_logic;
   signal txup_reqw2       : std_logic;
   signal txup_flag_set    : std_logic;
   signal txup_update      : std_logic;

   signal flags_get        : std_logic;
   signal flags_get_addr   : std_logic_vector(log2(IFCS+1)-1 downto 0);
   signal flags_set        : std_logic;
   signal flags_set_addr   : std_logic_vector(log2(IFCS+1)-1 downto 0);
   signal flags_clr        : std_logic;
   signal flags_clr_addr   : std_logic_vector(log2(IFCS+1)-1 downto 0);

   signal tx_syncint         : std_logic;
   signal reg_tx_syncint     : std_logic_vector(IFCS-1 downto 0);
   signal reg_tx_syncint_clr : std_logic_vector(IFCS-1 downto 0);
   signal reg_tx_syncint_set : std_logic_vector(IFCS-1 downto 0);

   signal tx_syncint_set     : std_logic_vector(IFCS-1 downto 0);
   signal rx_syncint_set     : std_logic_vector(IFCS-1 downto 0);
   signal tx_timeout_set     : std_logic_vector(IFCS-1 downto 0);
   signal rx_timeout_set     : std_logic_vector(IFCS-1 downto 0);

   signal dec_rx_ibrd_enable : std_logic;
   signal dec_rx_ibrd        : std_logic_vector(IFCS-1 downto 0);

   signal cs_sum           : std_logic;
   signal cs_reg_timeout   : std_logic;
   signal cs_reg_swcnt     : std_logic;
   signal cs_reg_tx_gaddrl : std_logic;
   signal cs_reg_tx_gaddrh : std_logic;
   signal mx_do_regs       : std_logic_vector(31 downto 0);
   signal reg_mx_do_regs   : std_logic_vector(31 downto 0);
   signal reg_mi_sw_rd     : std_logic;

   signal reg_tx_gaddrl    : std_logic_vector(31 downto 0);
   signal reg_tx_gaddrl_we : std_logic;
   signal reg_tx_gaddrh    : std_logic_vector(31 downto 0);
   signal reg_tx_gaddrh_we : std_logic;

   signal rx_timeout_occured : std_logic_vector(IFCS-1 downto 0);
   signal tx_timeout_occured : std_logic_vector(IFCS-1 downto 0);

   signal ra_timeout_do    : std_logic_vector(31 downto 0);
   signal ra_timeout       : T_VARRAY; -- register array
   signal ra_timeout_we    : std_logic_vector(2*IFCS-1 downto 0);
   signal ra_timeout_wea   : std_logic;
   signal ca_control       : std_logic_vector(2*IFCS-1 downto 0);
   signal ca_control_set   : std_logic_vector(2*IFCS-1 downto 0);
   signal ca_control_clr   : std_logic_vector(2*IFCS-1 downto 0);
   signal ca_timeout       : T_VARRAY; -- counter array
   signal ca_timeout_ce    : std_logic_vector(2*IFCS-1 downto 0);
   signal ca_timeout_ld    : std_logic_vector(2*IFCS-1 downto 0);
   signal dec_mi_addr      : std_logic_vector(2*IFCS-1 downto 0);
   signal cmp_timeout      : std_logic_vector(2*IFCS-1 downto 0);

   signal ra_timeout_occured     : std_logic_vector(2*IFCS-1 downto 0);
   signal ra_timeout_occured_set : std_logic_vector(2*IFCS-1 downto 0);
   signal ra_timeout_occured_clr : std_logic_vector(2*IFCS-1 downto 0);
   signal ra_timeout_interrupt   : std_logic_vector(2*IFCS-1 downto 0);
   signal ra_timeout_interrupt_set : std_logic_vector(2*IFCS-1 downto 0);
   signal ra_timeout_interrupt_clr : std_logic_vector(2*IFCS-1 downto 0);

   signal dec_rx_timeout_set_enable : std_logic;
   signal mux_tx_timeout_set_sel : std_logic;
   signal mux_rx_timeout_occured : std_logic_vector(0 downto 0);
   signal mux_interrupt_clr_sel  : std_logic;

   signal mux_bm_gaddr_sel    : std_logic;
   signal mux_bm_laddr_sel    : std_logic;
   signal mux_bm_len_sel      : std_logic;
   signal mux_bm_tag_sel      : std_logic;
   signal mux_flags_clr_addr_sel : std_logic;
   signal mux_req_di_sel      : std_logic;

   signal reg_interrupt_set : std_logic_vector(2*IFCS-1 downto 0);
   signal pipe_interrupt    : std_logic_vector(2*IFCS-1 downto 0);

   signal bm_req_di        : std_logic_vector(63 downto 0);
   signal bm_req_we        : std_logic;
   signal bm_req_addra     : std_logic_vector(0 downto 0);
   signal bm_req_addrb     : std_logic_vector(0 downto 0);
   signal bm_req_dob       : std_logic_vector(63 downto 0);

   -- BM interface
   signal bm_gaddr    : std_logic_vector(63 downto 0); -- Global Address 
   signal bm_laddr    : std_logic_vector(31 downto 0); -- Local Address
   signal bm_length   : std_logic_vector(11 downto 0); -- Length
   signal bm_tag      : std_logic_vector(15 downto 0); -- Operation TAG
   signal bm_ttype    : std_logic_vector(1  downto 0); -- Type of transaction

   signal reg_ib_rd_src_rdy   : std_logic;
   signal reg_ib_rd_addr      : std_logic_vector(31 downto 0);
   signal reg_ib_rd_req       : std_logic;

   signal rx_flush      : std_logic_vector(IFCS-1 downto 0);
   signal tx_flush      : std_logic_vector(IFCS-1 downto 0);
   signal tx_flush_di   : std_logic_vector(IFCS-1 downto 0);
   signal mux_rx_flush  : std_logic_vector(0 downto 0);

   signal cmp_rx_swhw_diff    : std_logic;
begin

gen_flush: for i in 0 to IFCS- 1 generate
   rx_flush(i) <= FLUSH(2*i);
   tx_flush(i) <= FLUSH(2*i+1);
end generate;


-- output multiplexor for DMA DOUT
-- multiplex 64bits of bm request to generic DMA_DATA_WIDTH
mux_dma_dout_i: entity work.gen_mux
   generic map (
      DATA_WIDTH => DMA_DATA_WIDTH,
      MUX_WIDTH  => 64/DMA_DATA_WIDTH
   )
   port map (
      DATA_IN  => bm_req_dob,
      SEL      => DMA_ADDR(DMA_ADDR'length-2 downto 0),
      DATA_OUT => DMA_DOUT
   );


-- read first/second word of bm request
bm_req_addrb(0) <= DMA_ADDR(DMA_ADDR'length-1);

-- 2*64bit memory, store dma request as two parts
bm_req_mem_i: entity work.DP_DISTMEM
   generic map (
      -- one DMA  request == 2*64b
      DATA_WIDTH  => 64, 
      ITEMS       => 2,
      DISTMEM_TYPE=> BM_REQ_DISTMEM_TYPE,
      DEBUG       => false
   )
   port map (
      RESET    => RESET,

      DI       => bm_req_di,
      WE       => bm_req_we,
      WCLK     => CLK,
      ADDRA    => bm_req_addra,
      DOA      => open,

      ADDRB    => bm_req_addrb,
      DOB      => bm_req_dob
   );

-- write one part of dma request to memory
bm_req_we      <= rxup_reqw1 or rxup_reqw2 or txup_reqw1 or txup_reqw2;
-- if we are writting second word, set address to 1
bm_req_addra(0)<= rxup_reqw2 or txup_reqw2;
mux_req_di_sel <= rxup_reqw2 or txup_reqw2;
-- multiplexor mux_req_di ------------------------------------------------------
mux_req_dip: process(mux_req_di_sel, bm_laddr, bm_tag, bm_length, bm_ttype, 
                                     bm_gaddr)
begin
   case mux_req_di_sel is
      when '0' => bm_req_di <= bm_laddr & bm_tag &
                               bm_length & "00" & bm_ttype;
      when '1' => bm_req_di <= bm_gaddr;
      when others => bm_req_di <= (others => 'X');
   end case;
end process;

-- internal bus busmater signals
DMA_REQ  <= rxup_bm_req or txup_bm_req;
bm_ttype <= TRANS_TYPE;

---------------------------------------------------------------------------
-- select between rx and tx bm data
---------------------------------------------------------------------------
mux_bm_gaddr_sel <= enable_tx;
-- multiplexor mux_bm_gaddr ------------------------------------------------------
mux_bm_gaddrp: process(mux_bm_gaddr_sel, ra_gaddr_doa, reg_tx_gaddrh,
                                                             reg_tx_gaddrl)
begin
   case mux_bm_gaddr_sel is
      when '0' => bm_gaddr <= ra_gaddr_doa;
      when '1' => bm_gaddr <= reg_tx_gaddrh & reg_tx_gaddrl;
      when others => bm_gaddr <= (others => 'X');
   end case;
end process;

mux_bm_laddr_sel <= enable_tx;
-- multiplexor mux_bm_laddr ------------------------------------------------------
mux_bm_laddrp: process(mux_bm_laddr_sel, cnt_chid)
begin
   case mux_bm_laddr_sel is
      when '0' => bm_laddr <= BASE_ADDR +
                  ( gndvec(31 downto log2(2*IFCS)+12) & 
                    cnt_chid(log2(IFCS)-1 downto 0) & gndvec(12 downto 0)
                  );
      when '1' => bm_laddr <= BASE_ADDR +
                  ( gndvec(31 downto 13) & '1' & gndvec(11 downto 0) );

      when others => bm_laddr <= (others => 'X');
   end case;
end process;

mux_bm_len_sel <= enable_tx;
-- multiplexor mux_bm_laddr ------------------------------------------------------
mux_bm_lenp: process(mux_bm_len_sel, reg_rx_actlen)
begin
   case mux_bm_len_sel is
      when '0' => bm_length <= reg_rx_actlen & "0000";
      when '1' => bm_length <= conv_std_logic_vector(TX_BM_LENGTH, 12);
      when others => bm_length <= (others => 'X');
   end case;
end process;

mux_bm_tag_sel <= enable_tx;
-- multiplexor mux_bm_tag ------------------------------------------------------
mux_bm_tagp: process(mux_bm_tag_sel, cnt_chid)
begin
   case mux_bm_tag_sel is
      -- for rx send channel index
      when '0' => bm_tag <= gndvec(15 downto 2+log2(2*IFCS)) &
                               cnt_chid(log2(IFCS)-1 downto 0) &
                               '0' & DMA_ID;
      -- for tx send number of interfaces -> index into sync flags
      when '1' => bm_tag <= gndvec(15 downto 2+log2(2*IFCS)) &
                               cnt_chid(log2(IFCS)-1 downto 0) &
                               '1' & DMA_ID;
      when others => bm_tag <= (others => 'X');
   end case;
end process;

enable_rx <= '1' when (cnt_chid /= conv_std_logic_vector(IFCS,cnt_chid'length))
             else '0';
enable_tx <= not enable_rx;

---------------------------------------------------------------------------
-- channel index counter
---------------------------------------------------------------------------
cnt_chid_ce <= rxup_next_chid or txup_next_chid;

cnt_chid_ld <= '1' when (cnt_chid = conv_std_logic_vector(IFCS,cnt_chid'length))
               else '0';

-- cnt_chid counter
cnt_chidp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         cnt_chid <= (others => '0');
      elsif (cnt_chid_ce = '1') then
         if (cnt_chid_ld = '1') then
            cnt_chid <= (others => '0');
         else
            cnt_chid <= cnt_chid + 1;
         end if;
      end if;
   end if;
end process;

---------------------------------------------------------------------------
-- length register array - to store length of rx desc request
---------------------------------------------------------------------------
reg_array_length_i: entity work.reg_array_sp_be
   generic map (
      DATA_WIDTH  => LENGTH_DW,
      ITEMS       => IFCS,
      INIT_DATA   => gndvec(LENGTH_DW-1 downto 0)
   )
   port map (
      CLK   => CLK,
      SCLR  => ra_length_sclr,
      -- read/write PORT
      WEA   => ra_length_wea,
      BEA   => ra_length_bea,
      ADDRA => ra_length_addra,
      DIA   => ra_length_dia,
      DOA   => ra_length_doa
   );

ra_length_sclr  <= INIT(2*conv_integer(cnt_chid(log2(IFCS)-1 downto 0)));
ra_length_wea   <= rxup_update_we;
ra_length_bea   <= not gndvec(ra_length_bea'length-1 downto 0);
ra_length_addra <= cnt_chid(log2(IFCS)-1 downto 0);
ra_length_dia   <= mux_length_dia;

rx_update_len  <= ra_length_doa - reg_rx_actlen;

mux_length_dia_sel <= rxup_update;
-- multiplexor mux_length_dia ------------------------------------------------------
mux_length_diap: process(mux_length_dia_sel, RX_RF_DOUT, rx_update_len)
begin
   case mux_length_dia_sel is
      when '0' => mux_length_dia <= 
                  gndvec(mux_length_dia'length-1 downto LENGTH_WIDTH) &
                  RX_RF_DOUT(RX_RF_DOUT'length-1 downto GADDR_WIDTH);

      when '1' => mux_length_dia <= rx_update_len;
      when others => mux_length_dia <= (others => 'X');
   end case;
end process;

mux_rx_actlen_sel <= rxup_length_lte_status;
-- multiplexor mux_rx_actlen ------------------------------------------------------
mux_rx_actlenp: process(mux_rx_actlen_sel, ra_length_doa, mux_rxup_nfifo_status)
begin
   case mux_rx_actlen_sel is
      when '0' => rx_actlen <= gndvec(LENGTH_DW-RXUP_STATUS_WIDTH-1 downto 0) & 
                              mux_rxup_nfifo_status;
      when '1' => rx_actlen <= ra_length_doa;
      when others => rx_actlen <= (others => 'X');
   end case;
end process;


reg_rx_actlen_we <= rxup_length_we;
-- register reg_rx_actlen ------------------------------------------------------
reg_rx_actlenp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         reg_rx_actlen <= (others => '0');
      elsif (reg_rx_actlen_we = '1') then
         reg_rx_actlen <= rx_actlen;
      end if;
   end if;
end process;

---------------------------------------------------------------------------
-- gaddr register array - to store gaddr of rx desc request
---------------------------------------------------------------------------
reg_array_gaddr_i: entity work.reg_array_sp_be
   generic map (
      DATA_WIDTH  => GADDR_WIDTH,
      ITEMS       => IFCS,
      INIT_DATA   => gndvec(GADDR_WIDTH-1 downto 0)
   )
   port map (
      CLK   => CLK,
      SCLR  => ra_gaddr_sclr,
      -- read/write PORT
      WEA   => ra_gaddr_wea,
      BEA   => ra_gaddr_bea,
      ADDRA => ra_gaddr_addra,
      DIA   => ra_gaddr_dia,
      DOA   => ra_gaddr_doa
   );

ra_gaddr_sclr  <= INIT(2*conv_integer(cnt_chid(log2(IFCS)-1 downto 0)));
ra_gaddr_wea   <= rxup_update_we;
ra_gaddr_bea   <= not gndvec(ra_gaddr_bea'length-1 downto 0);
ra_gaddr_addra <= cnt_chid(log2(IFCS)-1 downto 0);
ra_gaddr_dia   <= mux_gaddr_dia;

RX_RF_RADDR       <= cnt_chid(log2(IFCS)-1 downto 0);
RX_RF_READ        <= rxup_req_fifo_rd;
rxup_req_fifo_dv  <= RX_RF_DVLD;

mux_gaddr_dia_sel <= rxup_update;
-- multiplexor mux_gaddr_dia ------------------------------------------------------
mux_gaddr_diap: process(mux_gaddr_dia_sel, RX_RF_DOUT, ra_gaddr_doa, reg_rx_actlen)
begin
   case mux_gaddr_dia_sel is
      when '0' => mux_gaddr_dia <= RX_RF_DOUT(GADDR_WIDTH-1 downto 0);
-- gaddr increment optimized: based on fact, that we never cross the page
-- boundary
      when '1' => mux_gaddr_dia <= 
           ra_gaddr_doa(ra_gaddr_doa'length - 1 downto 12) &
          (ra_gaddr_doa(11 downto 0) + 
          ( gndvec(11 downto reg_rx_actlen'length + 4) & reg_rx_actlen & "0000"));
         when others => mux_gaddr_dia <= (others => 'X');
   end case;
end process;

---------------------------------------------------------------------------
-- rx update fsm - control rx status update DMA request
---------------------------------------------------------------------------
rxup_fsm_i: entity work.RXUP_FSM
   port map (
      -- global signals 
      CLK            => CLK,
      RESET          => RESET,

      -- input signals
      ENABLE            => rxup_enable,
      FLAG_GET          => rxup_flag_get,
      LENGTH_NZ         => rxup_length_nz,
      STATUS_NZ         => rxup_status_nz,
      LENGTH_LTE_STATUS => rxup_length_lte_status,
      FLUSH             => rxup_flush,
      REQ_FIFO_EMPTY    => rxup_req_fifo_empty,
      REQ_FIFO_DV       => rxup_req_fifo_dv,
      TIMEOUT           => rxup_timeout,
      BM_ACK            => rxup_bm_ack,
      SWHW_CNT_DIFF     => rxup_swhw_diff,
      
      -- output signals
      NEXT_CHID      => rxup_next_chid,
      BM_REQ         => rxup_bm_req,
      LENGTH_WE      => rxup_length_we,
      REQ_W1         => rxup_reqw1,
      REQ_W2         => rxup_reqw2,
      FLAG_SET       => rxup_flag_set,
      REQ_FIFO_RD    => rxup_req_fifo_rd,
      UPDATE         => rxup_update,
      UPDATE_WE      => rxup_update_we,
      TINT           => rxup_tint
   );

rxup_bm_ack    <= DMA_ACK;
rxup_enable    <= enable_rx;
rxup_flag_get  <= flags_get;
rxup_length_nz <= '1' when (ra_length_doa /= 
                            gndvec(ra_length_doa'length-1 downto 0))
                  else '0';

rxup_length_lte_status <= '1' when 
              (ra_length_doa(LENGTH_WIDTH-1 downto 0) <= mux_rxup_nfifo_status)
                          else '0';

rxup_status_nz  <= '1' when (mux_rxup_nfifo_status /= 
                            gndvec(mux_rxup_nfifo_status'length-1 downto 0))
                  else '0';

rxup_req_fifo_empty <= mux_rx_rf_empty(0);

rxup_swhw_diff <= cmp_rx_swhw_diff;

---------------------------------------------------------------------------
-- mux rx req fifo empty - select empty signal of current channel
---------------------------------------------------------------------------
mux_rx_rf_empty_i: entity work.gen_mux
   generic map (
      DATA_WIDTH => 1,
      MUX_WIDTH  => IFCS
   )
   port map (
      DATA_IN  => RX_RF_EMPTY,
      SEL      => cnt_chid(log2(IFCS)-1 downto 0),
      DATA_OUT => mux_rx_rf_empty
   );

rxup_timeout <= mux_rx_timeout_occured(0);
---------------------------------------------------------------------------
-- mux rx timeout occured - select timeout indication signal
---------------------------------------------------------------------------
mux_rx_timeout_occured_i: entity work.gen_mux
   generic map (
      DATA_WIDTH => 1,
      MUX_WIDTH  => IFCS
   )
   port map (
      DATA_IN  => rx_timeout_occured,
      SEL      => cnt_chid(log2(IFCS)-1 downto 0),
      DATA_OUT => mux_rx_timeout_occured
   );

rxup_flush <= mux_rx_flush(0);
---------------------------------------------------------------------------
-- mux rx flush - select flush signal
---------------------------------------------------------------------------
mux_rx_flush_i: entity work.gen_mux
   generic map (
      DATA_WIDTH => 1,
      MUX_WIDTH  => IFCS
   )
   port map (
      DATA_IN  => rx_flush,
      SEL      => cnt_chid(log2(IFCS)-1 downto 0),
      DATA_OUT => mux_rx_flush
   );


---------------------------------------------------------------------------
-- rx up nfifo - nfifo with actual lengths and flags
---------------------------------------------------------------------------
rxup_nfifo_i: entity work.nfifo
  generic map (
    DATA_WIDTH => NUM_FLAGS+16,
    FLOWS      => IFCS,
    BLOCK_SIZE => RXUP_NFIFO_BLOCK_SIZE,
    LUT_MEMORY => NFIFO_LUT_MEMORY,
    OUTPUT_REG => NFIFO_OUTPUT_REG
  )
  port map (
    CLK         => CLK,
    RESET       => RESET,
    INIT        => rxup_nfifo_init,

    -- Write interface
    DATA_IN     => RX_SU_DATA,
    WR_BLK_ADDR => RX_SU_ADDR,
    WRITE       => RX_SU_DVLD,
    FULL        => open,

    -- Read interface
    DATA_OUT    => rxup_nfifo_dout,
    DATA_VLD    => rxup_nfifo_dout_vld,
    RD_BLK_ADDR => rxup_nfifo_raddr,
    READ        => rxup_nfifo_rd,
    PIPE_EN     => rxup_nfifo_pipe_en,
    EMPTY       => rxup_nfifo_empty,

    STATUS      => rxup_nfifo_status
  );

gen_idle_i: for i in 0 to IFCS-1 generate
--  rx is idle when there are no descs to update in nfifo
   IDLE(2*i)   <= rxup_nfifo_empty(i);
--  tx is idle when there is not status set
   IDLE(2*i+1) <= not reg_tx_status(i);
end generate;


--  indicate that the rxup fifo is half-full (or half empty :) )
gen_rx_su_hfull: for i in 0 to IFCS- 1 generate
   RX_SU_HFULL(i) <= rxup_nfifo_status((i+1)*RXUP_STATUS_WIDTH-1);
end generate;

-- tx su will never be full as there are only counters
TX_SU_HFULL <= (others => '0');

rxup_nfifo_init      <= (others => '0');
rxup_nfifo_raddr     <= ib_channel_index(ib_channel_index'length-1 downto 1);
rxup_nfifo_rd        <= IB_RD_REQ and ib_rx_cs and rx_ib_rd_first_word; 
rxup_nfifo_pipe_en   <= rxup_nfifo_rd;

rx_ib_rd_first_word <= '1' when IB_RD_ADDR(3 downto 0) = "0000"
                       else '0'; 
---------------------------------------------------------------------------
-- rx up nfifo status - select status signal of current channel
---------------------------------------------------------------------------
mux_rxup_nfifo_status_i: entity work.gen_mux
   generic map (
      DATA_WIDTH => RXUP_STATUS_WIDTH,
      MUX_WIDTH  => IFCS
   )
   port map (
      DATA_IN  => rxup_nfifo_status,
      SEL      => cnt_chid(log2(IFCS)-1 downto 0),
      DATA_OUT => mux_rxup_nfifo_status
   );

---------------------------------------------------------------------------
-- hw cnt register array - to store number of descs processed by hw
-- register array + one accumulator
---------------------------------------------------------------------------
reg_array_hwcnt_i: entity work.reg_array_be
   generic map (
      DATA_WIDTH  => 32,
      ITEMS       => IFCS,
      INIT_DATA   => gndvec(31 downto 0)
   )
   port map (
      CLK   => CLK,
      SCLR  => ra_hwcnt_sclr,
      -- read/write PORT
      WEA   => ra_hwcnt_wea,
      BEA   => ra_hwcnt_bea,
      ADDRA => ra_hwcnt_addra,
      DIA   => ra_hwcnt_dia,
      DOA   => ra_hwcnt_doa,
      -- readonly PORT
      ADDRB => ra_hwcnt_addrb,
      DOB   => ra_hwcnt_dob
   );

ra_hwcnt_sclr  <= INIT(2*conv_integer(
                      ib_channel_index(ib_channel_index'length-1 downto 1)));
ra_hwcnt_wea   <= rxup_nfifo_rd;
ra_hwcnt_bea   <= (others => '1');
ra_hwcnt_addra <= ib_channel_index(ib_channel_index'length-1 downto 1);
ra_hwcnt_dia   <= reg_hwcnt_dia;

ra_hwcnt_addrb <= cnt_chid(log2(IFCS)-1 downto 0);


-- register reg_hwcnt_dia ------------------------------------------------------
reg_hwcnt_diap: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      reg_hwcnt_dia <= ra_hwcnt_doa + 1;
   end if;
end process;

---------------------------------------------------------------------------
-- sw cnt register array - to store number of descs processed by sw
---------------------------------------------------------------------------
reg_array_swcnt_i: entity work.reg_array_be
   generic map (
      DATA_WIDTH  => 32,
      ITEMS       => IFCS,
      INIT_DATA   => gndvec(31 downto 0)
   )
   port map (
      CLK   => CLK,
      SCLR  => ra_swcnt_sclr,
      -- read/write PORT
      WEA   => ra_swcnt_wea,
      BEA   => ra_swcnt_bea,
      ADDRA => ra_swcnt_addra,
      DIA   => ra_swcnt_dia,
      DOA   => ra_swcnt_doa,
      -- readonly PORT
      ADDRB => ra_swcnt_addrb,
      DOB   => ra_swcnt_dob
   );

-- initialization is done by sw
ra_swcnt_sclr  <= '0';
ra_swcnt_bea   <= (others => '1');
ra_swcnt_addra <= MI_SW_ADDR(log2(PAC_MI32_ADDR_MAX)+log2(2*IFCS)-1
                             downto log2(PAC_MI32_ADDR_MAX)+1);
ra_swcnt_dia   <= MI_SW_DWR;

ra_swcnt_addrb <= cnt_chid(log2(IFCS)-1 downto 0);

---------------------------------------------------------------------------
-- sw and hw cnt comparator
-- signal is set, if there is a difference between sw and hw cnts
---------------------------------------------------------------------------
cmp_rx_swhw_diff <= '0' when (ra_hwcnt_dob = ra_swcnt_dob) else '1';

---------------------------------------------------------------------------
-- internal bus read logic
---------------------------------------------------------------------------
ib_channel_index <= IB_RD_ADDR(12+log2(IFCS*2)-1 downto 12);
ib_rx_cs   <= not ib_channel_index(0); -- even index
ib_tx_cs   <= ib_channel_index(0); -- odd index - all tx's on same place


IB_RD_ARDY       <= IB_RD_REQ;
IB_RD_SRC_RDY    <= reg_ib_rd_req;
IB_RD_DATA       <= mux_rd_data;


-- register reg_ib_rd_req ------------------------------------------------------
reg_ib_rd_reqp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      reg_ib_rd_req <= IB_RD_REQ;
   end if;
end process;

-- register reg_ib_rd_addr ------------------------------------------------------
reg_ib_rd_addrp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      reg_ib_rd_addr <= IB_RD_ADDR;
   end if;
end process;


mux_rd_data_sel  <= ib_tx_cs;
-- multiplexor mux_rd_data ------------------------------------------------------
mux_rd_datap: process(mux_rd_data_sel, mux_rx_rd_data, mux_tx_rd_data)
begin
   case mux_rd_data_sel is
      when '0' => mux_rd_data <= mux_rx_rd_data;
      when '1' => mux_rd_data <= mux_tx_rd_data;
      when others => mux_rd_data <= (others => 'X');
   end case;
end process;

dec1fn_rx_ibrd_ce_i: entity work.dec1fn_enable
   generic map (
      ITEMS    => IFCS
   )
   port map (
      ADDR     => ib_channel_index(ib_channel_index'length-1 downto 1),
      ENABLE   => dec_rx_ibrd_enable,
      DO       => dec_rx_ibrd
   );

-- if read request, first word of descriptor and interrupt flag is set
dec_rx_ibrd_enable <= reg_ib_rd_req and (not mux_rx_rd_data_sel) and 
                      mux_rx_rd_data(32 + PAC_DMA_INTF);
-- set appropriate interrupt register bit
rx_syncint_set     <= dec_rx_ibrd;

mux_rx_rd_data_sel <= reg_ib_rd_addr(3);  -- rx_rd data - first 8B len+flags
                                          --            - next  8B all zeroes
-- prepare rx output data for internal bus
-- multiplexor mux_rx_rd_data ------------------------------------------------------
mux_rx_rd_datap: process(mux_rx_rd_data_sel, rxup_nfifo_dout)
begin
   case mux_rx_rd_data_sel is
      when '0' => mux_rx_rd_data <= gndvec(31 downto NUM_FLAGS) &   -- first 8B
                rxup_nfifo_dout(rxup_nfifo_dout'length-1 downto 16) & -- flags
                gndvec(31 downto 16) & rxup_nfifo_dout(15 downto 0); -- length

      when '1' => mux_rx_rd_data <= gndvec(GADDR_WIDTH-1 downto 0); -- second 8B
      when others => mux_rx_rd_data <= (others => 'X');
   end case;
end process;

ib_word_index <= reg_ib_rd_addr(11 downto 3);
-- little tricky signal construction
-- glue selected counters from cnt_array into ouput signal
mux_tx_rd_datap: process(ib_word_index, tx_cnt_array)
begin
   mux_tx_rd_data <= (others => '0');
   for i in 0 to IFCS-1 loop
      if (conv_integer(ib_word_index) = i / 2) then
         mux_tx_rd_data(32*(i rem 2)+31 downto 32*(i rem 2)) <= tx_cnt_array(i);
      end if;
   end loop;
end process;

---------------------------------------------------------------------------
-- decoders to set/clr tx status register and tx syncint register
---------------------------------------------------------------------------
reg_tx_status_clrp: process(ib_word_index, reg_ib_rd_req)
begin
   reg_tx_status_clr <= (others => '0');
   for i in 0 to IFCS-1 loop
      if (conv_integer(ib_word_index) = i / 2) then
         if (reg_ib_rd_req = '1' and ib_tx_cs = '1') then
            reg_tx_status_clr(i) <= '1';
         end if;
      end if;
   end loop;
end process;


tx_syncintp: process(ib_word_index, reg_tx_syncint, reg_ib_rd_req)
begin
   reg_tx_syncint_clr <= (others => '0');
   tx_syncint_set     <= (others => '0');
   for i in 0 to IFCS-1 loop
      if (conv_integer(ib_word_index) = i / 2) then
         if (reg_tx_syncint(i) = '1' and reg_ib_rd_req = '1' and 
                                         ib_tx_cs = '1') then
            reg_tx_syncint_clr(i) <= '1';
            tx_syncint_set(i) <= '1';
         end if;
      end if;
   end loop;
end process;

---------------------------------------------------------------------------
-- Tx status counters and status register to indicate change since last
-- upload of status counters
---------------------------------------------------------------------------
dec1fn_tx_su_addr_ce_i: entity work.dec1fn_enable
   generic map (
      ITEMS    => IFCS
   )
   port map (
      ADDR     => TX_SU_ADDR,
      ENABLE   => TX_SU_DVLD,
      DO       => dec_tx_su_addr
   );

gen_tx_cnt_ld: for i in 0 to IFCS- 1 generate
   tx_cnt_ld(i) <= INIT(2*i+1);
end generate;
tx_cnt_ce  <= dec_tx_su_addr;

reg_tx_status_set  <= dec_tx_su_addr;

-- for each tx channel one counter of sent packets
gen_tx_cnts: for i in 0 to IFCS-1 generate
   -- tx_cnt counters array
   tx_cntp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            tx_cnt_array(i) <= (others => '0');
         elsif (tx_cnt_ld(i) = '1') then
               tx_cnt_array(i) <= (others => '0');
         elsif (tx_cnt_ce(i) = '1') then
               tx_cnt_array(i) <= tx_cnt_array(i) + 1;
         end if;
      end if;
   end process;

-- when there is a change in one of the counters - status register is set
-- status register is cleared when the upload of data is being done, i.e. IB RD
   -- register reg_tx_status -------------------------------------------------
   reg_tx_statusp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_tx_status(i) <= '0';
         elsif (reg_tx_status_set(i) = '1') then
            reg_tx_status(i) <= '1';
         elsif (reg_tx_status_clr(i) = '1') then
            reg_tx_status(i) <= '0';
         end if;
      end if;
   end process;

end generate;

generic_or_tx_status_i: entity work.nport_or
   generic map (
      PORTS => IFCS
   )
   port map (
      DI => reg_tx_status,
      DO => tx_status
   );

gen_tx_syncint: for i in 0 to IFCS-1 generate
   -- tx syncint status registers - set when there was a interrupt flag in
   -- descriptor
   -- cleared when tx counters are being read - flag is propagated to
   -- reg_interrupt
   -- register reg_tx_syncint ------------------------------------------------
   reg_tx_syncintp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_tx_syncint(i) <= '0';
         elsif (reg_tx_syncint_set(i) = '1') then
            reg_tx_syncint(i) <= '1';
         elsif (reg_tx_syncint_clr(i) = '1') then
            reg_tx_syncint(i) <= '0';
         end if;
      end if;
   end process;

   reg_tx_syncint_set(i) <= dec_tx_su_addr(i) and TX_SU_DATA(PAC_DMA_INTF);

end generate;
---------------------------------------------------------------------------
-- Tx status update FSM - responsible for upload of packet counters
---------------------------------------------------------------------------
txup_fsm_i: entity work.TXUP_FSM
   port map (
      -- global signals 
      CLK            => CLK,
      RESET          => RESET,

      -- input signals
      ENABLE         => txup_enable,
      FLAG_GET       => txup_flag_get,
      TIMEOUT        => txup_timeout,
      SYNCINT        => txup_syncint,
      FLUSH          => txup_flush,
      TX_STATUS      => txup_tx_status,
      BM_ACK         => txup_bm_ack,
      
      -- output signals
      NEXT_CHID      => txup_next_chid,
      BM_REQ         => txup_bm_req,
      REQ_W1         => txup_reqw1,
      REQ_W2         => txup_reqw2,
      FLAG_SET       => txup_flag_set,
      UPDATE         => txup_update
   );

txup_enable    <= enable_tx;
txup_flag_get  <= flags_get;
txup_tx_status <= tx_status;
txup_syncint   <= tx_syncint;
txup_bm_ack    <= DMA_ACK;

generic_or_tx_timeout_i: entity work.nport_or
   generic map (
      PORTS => IFCS
   )
   port map (
      DI => tx_timeout_occured,
      DO => txup_timeout
   );

-- for given channel flush is set and status set
tx_flush_di <= tx_flush and reg_tx_status;
generic_or_tx_flush: entity work.nport_or
   generic map (
      PORTS => IFCS
   )
   port map (
      DI => tx_flush_di,
      DO => txup_flush
   );

generic_or_tx_syncint: entity work.nport_or
   generic map (
      PORTS => IFCS
   )
   port map (
      DI => reg_tx_syncint,
      DO => tx_syncint
   );



---------------------------------------------------------------------------
-- synchronization flags - when set for appropriate channel DMA already
-- in progress
---------------------------------------------------------------------------
flags_i: entity work.SYNC_FLAGS
   generic map (
      ITEMS       => IFCS+1,
      DATA_WIDTH  => 1
   )
   port map (
      CLK      => CLK,
      RESET    => RESET,

      -- get value
      GET      => flags_get,
      -- get address
      GET_ADDR => flags_get_addr,
      -- set enable
      SET      => flags_set,
      -- set address
      SET_ADDR => flags_set_addr,
      -- clear enable
      CLR      => flags_clr,
      -- clear address
      CLR_ADDR => flags_clr_addr

   );

flags_get_addr <= cnt_chid;
flags_set_addr <= cnt_chid;
flags_set      <= rxup_flag_set or txup_flag_set;

mux_flags_clr_addr_sel <= DMA_TAG(2); -- decide if it is rx or tx
-- multiplexor mux_flags_clr_addr ------------------------------------------------------
mux_flags_clr_addrp: process(mux_flags_clr_addr_sel, DMA_TAG)
begin
   case mux_flags_clr_addr_sel is
      -- rx
      when '0' => flags_clr_addr <= DMA_TAG(3+log2(IFCS+1)-1 downto 3);
      when '1' => flags_clr_addr <= conv_std_logic_vector(IFCS,
                                        flags_clr_addr'length); -- tx
      when others => flags_clr_addr <= (others => 'X');
   end case;
end process;

flags_clr      <= DMA_DONE;
---------------------------------------------------------------------------
-- address decoder for localbus (mi32)
---------------------------------------------------------------------------
adr_dec : process(MI_SW_ADDR)
begin
   cs_reg_timeout    <= '0';
   cs_reg_swcnt      <= '0';
   cs_reg_tx_gaddrl  <= '0';
   cs_reg_tx_gaddrh  <= '0';

   case (MI_SW_ADDR(4 downto 2)) is
      when "100" => cs_reg_timeout    <= '1';
      when "101" => cs_reg_swcnt      <= '1';
      when "110" => cs_reg_tx_gaddrl  <= '1';
      when "111" => cs_reg_tx_gaddrh  <= '1';
      when others => null;
   end case;
end process;

cs_sum <= cs_reg_timeout   or cs_reg_swcnt or 
          cs_reg_tx_gaddrl or cs_reg_tx_gaddrh;

ra_timeout_wea   <= cs_reg_timeout   AND MI_SW_WR;
ra_swcnt_wea     <= cs_reg_swcnt     AND MI_SW_WR;
reg_tx_gaddrl_we <= cs_reg_tx_gaddrl AND MI_SW_WR;
reg_tx_gaddrh_we <= cs_reg_tx_gaddrh AND MI_SW_WR;

-- output multiplexor
with MI_SW_ADDR(4 downto 2) select
mx_do_regs <=  ra_timeout_do     when "100",
               ra_swcnt_doa      when "101",
               reg_tx_gaddrl     when "110",
               reg_tx_gaddrh     when "111",
               (others => '0')   when others;

-- register reg_mx_do_regs ----------------------------------------------------
reg_mx_do_regsp : process(CLK)
begin
   if (CLK'event and CLK = '1') then
      reg_mx_do_regs <= mx_do_regs;
   end if;
end process;

-- register reg_mi_sw_rd ------------------------------------------------------
reg_mi_sw_rdp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      reg_mi_sw_rd <= MI_SW_RD and cs_sum;
   end if;
end process;

-- we have only registers here
MI_SW_ARDY <= (MI_SW_WR OR MI_SW_RD) and cs_sum;
MI_SW_DRDY <= reg_mi_sw_rd;
MI_SW_DRD  <= reg_mx_do_regs;


-------------------------------------------------------------------------------
-- upper and lower part of tx gaddr register
-- stores global address where tx counters are uploaded
-------------------------------------------------------------------------------
-- register reg_tx_gaddrl ---------------------------------------------------
reg_tx_gaddrlp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         reg_tx_gaddrl <= (others => '0');
      elsif (reg_tx_gaddrl_we = '1') then
         reg_tx_gaddrl <= MI_SW_DWR;
      end if;
   end if;
end process;


-- register reg_tx_gaddrh ---------------------------------------------------
reg_tx_gaddrhp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         reg_tx_gaddrh <= (others => '0');
      elsif (reg_tx_gaddrh_we = '1') then
         reg_tx_gaddrh <= MI_SW_DWR;
      end if;
   end if;
end process;

-- readback timeout register
ra_timeout_dop: process(dec_mi_addr, ra_timeout)
begin
   ra_timeout_do <= (others => '0');
   for i in 0 to 2*IFCS-1 loop
      if (dec_mi_addr(i) = '1') then
         ra_timeout_do <= ra_timeout(i);
      end if;
   end loop;
end process;
-------------------------------------------------------------------------------
-- timeout logic - registers, counters and comparators
-------------------------------------------------------------------------------
-- for each channel there is:
--  timeout register - value of timeout set by SW
--  control register - indicates/controls counter activity
--  timeout counter - counts ticks until it reachs timeout register value
--  timeout comparator - compares timeout counter and timeout register
-------------------------------------------------------------------------------
gen_timeout_rcc: for i in 0 to 2*IFCS-1 generate

   ra_timeout_we(i) <= dec_mi_addr(i) and ra_timeout_wea;
   -- array of software controlled registers
   -- register ra_timeout ----------------------------------------------------
   ra_timeoutp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            ra_timeout(i) <= (others => '0');
         elsif (ra_timeout_we(i) = '1') then
            ra_timeout(i) <= MI_SW_DWR;
         end if;
      end if;
   end process;

   ca_control_set(i) <= dec_mi_addr(i) and ra_timeout_wea;
   ca_control_clr(i) <= cmp_timeout(i);
   -- array of registers to control counter activity (start/stop)
   -- when 1 -- counter is active
   -- when 0 -- counter is stopped
   -- register ca_control ------------------------------------------------------
   ca_controlp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            ca_control(i) <= '0';
         elsif (ca_control_set(i) = '1') then
            ca_control(i) <= '1';
         elsif (ca_control_clr(i) = '1') then
            ca_control(i) <= '0';
         end if;
      end if;
   end process;

   ca_timeout_ce(i) <= ca_control(i);
   ca_timeout_ld(i) <= su_addr_clr(i) or                -- packet arrived/sent
                       (dec_mi_addr(i) and ra_timeout_wea) or -- timeout reg set
                       cmp_timeout(i);                  -- timeout expired
   -- array of timeout counters - controled by ca_control
   -- ca_timeout counter
   ca_timeoutp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            ca_timeout(i) <= (others => '0');
         elsif (ca_timeout_ce(i) = '1') then
            if (ca_timeout_ld(i) = '1') then
               ca_timeout(i) <= (others => '0');
            else
               ca_timeout(i) <= ca_timeout(i) + 1;
            end if;
         end if;
      end if;
   end process;

   cmp_timeout(i) <= '1' when ( (ca_timeout(i) = ra_timeout(i)) 
                            and (ca_control(i) = '1') )          else '0';

end generate;

-- MI address decoder - to select which counter should start counting
dec1fn_mi_addr_i: entity work.dec1fn
   generic map (
      ITEMS    => 2*IFCS
   )
   port map (
      ADDR     => MI_SW_ADDR(log2(PAC_MI32_ADDR_MAX)+log2(2*IFCS)-1
                             downto log2(PAC_MI32_ADDR_MAX)),
      DO       => dec_mi_addr
   );

dec1fn_rx_su_addr_i: entity work.dec1fn_enable
   generic map (
      ITEMS    => IFCS
   )
   port map (
      ADDR     => RX_SU_ADDR,
      ENABLE   => RX_SU_DVLD,
      DO       => dec_rx_su_addr
   );

-- concatenate counters ld signal from rx su a tx su
-- clear counter on packet arrival
gen_su_addr_clr: for i in 0 to IFCS- 1 generate
   su_addr_clr(2*i)   <= dec_rx_su_addr(i);
   su_addr_clr(2*i+1) <= dec_tx_su_addr(i);
end generate;

ra_timeout_occured_set <= cmp_timeout;
-------------------------------------------------------------------------------
-- ra_timeout_occured - stores timeout events
-------------------------------------------------------------------------------
gen_timeout_occured: for i in 0 to 2*IFCS- 1 generate

   -- register ra_timeout_occured ---------------------------------------------
   ra_timeout_occuredp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            ra_timeout_occured(i) <= '0';
         elsif (ra_timeout_occured_set(i) = '1') then
            ra_timeout_occured(i) <= '1';
         elsif (ra_timeout_occured_clr(i) = '1') then
            ra_timeout_occured(i) <= '0';
         end if;
      end if;
   end process;

end generate;

-- extract separate rx and tx timeout status signals
gen_rxtx_timeout_occured: for i in 0 to IFCS- 1 generate
   rx_timeout_occured(i) <= ra_timeout_occured(2*i);
   tx_timeout_occured(i) <= ra_timeout_occured(2*i+1);
end generate;

-- clear occured and set interrupt registers on rx DMA ack
dec1fn_rx_chid_i: entity work.dec1fn
   generic map (
      ITEMS    => IFCS
   )
   port map (
      ADDR     => cnt_chid(log2(IFCS)-1 downto 0),
      DO       => dec_rx_chid
   );

gen_rx_timeout_acked: for i in 0 to IFCS- 1 generate
   ra_timeout_occured_clr(2*i)   <= dec_rx_chid(i) and 
                                    (rxup_update_we or rxup_tint);
   ra_timeout_interrupt_set(2*i) <= dec_rx_chid(i) and rxup_update_we
                                    and ra_timeout_occured(2*i);
end generate;

-- clear occured and set interrupt registers on tx DMA ack
gen_tx_timeout_acked: for i in 0 to IFCS- 1 generate
   ra_timeout_occured_clr(2*i+1)   <= txup_update;
   ra_timeout_interrupt_set(2*i+1) <= txup_update and ra_timeout_occured(2*i+1);
end generate;


-------------------------------------------------------------------------------
-- ra_timeout_interrupt - stores acked timeout events
-------------------------------------------------------------------------------
gen_timeout_interrupt: for i in 0 to 2*IFCS- 1 generate

   -- register ra_timeout_interrupt ------------------------------------------------------
   ra_timeout_interruptp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            ra_timeout_interrupt(i) <= '0';
         elsif (ra_timeout_interrupt_set(i) = '1') then
            ra_timeout_interrupt(i) <= '1';
         elsif (ra_timeout_interrupt_clr(i) = '1') then
            ra_timeout_interrupt(i) <= '0';
         end if;
      end if;
   end process;

end generate;

gen_ra_timeout_interrupt_clr: for i in 0 to IFCS- 1 generate
   ra_timeout_interrupt_clr(2*i)   <= rx_timeout_set(i);
   ra_timeout_interrupt_clr(2*i+1) <= tx_timeout_set(i);
end generate;
-- interrupt register is implemented in rxtx_buffers_pac top level
-- and is connected on internal bus to flush all previous data
-- scheduled for transfer -> forced synchronization

INTERRUPT <= pipe_interrupt;
--INTERRUPT <= reg_interrupt_set;
-- register pipe_interrupt ------------------------------------------------------
pipe_interruptp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      pipe_interrupt <= reg_interrupt_set;
   end if;
end process;

-- set appropriate bits of reg_interrupt
gen_reg_interrupt_set: for i in 0 to IFCS- 1 generate
   reg_interrupt_set(2*i)   <= rx_syncint_set(i) or 
                           (rx_timeout_set(i) and ra_timeout_interrupt(2*i)) or
                           (dec_rx_chid(i) and rxup_tint);
   reg_interrupt_set(2*i+1) <= tx_syncint_set(i) or 
                           (tx_timeout_set(i) and ra_timeout_interrupt(2*i+1));
end generate;

-- propagate timeout events on dma done
mux_tx_timeout_set_sel <= DMA_TAG(2) and DMA_DONE;
-- multiplexor mux_tx_timeout_set ------------------------------------------------------
mux_tx_timeout_setp: process(mux_tx_timeout_set_sel)
begin
   case mux_tx_timeout_set_sel is
      when '0' => tx_timeout_set <= (others => '0');
      when '1' => tx_timeout_set <= (others => '1');
      when others => tx_timeout_set <= (others => 'X');
   end case;
end process;

dec_rx_timeout_set_enable <= (not DMA_TAG(2)) and DMA_DONE;
dec1fn_rx_timeout_set_i: entity work.dec1fn_enable
   generic map (
      ITEMS    => IFCS
   )
   port map (
      ADDR     => DMA_TAG(3+log2(IFCS)-1 downto 3),
      ENABLE   => dec_rx_timeout_set_enable,
      DO       => rx_timeout_set
   );

end architecture sum_behav;
