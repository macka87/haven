-- tx_ctrl_arch.vhd: Packet TX DMA controller architecture.
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
--
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- package with log2 function
use work.math_pack.all;
use work.pac_dma_pkg.all;
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture tx_ctrl_behav of tx_ctrl is
   constant gndvec         : std_logic_vector(63 downto 0) := (others => '0');

   -- packet length signal width - from rx buff
   constant LENGTH_WIDTH   : integer := 16;
   -- type of transaction - FPGA2RAM
   constant TRANS_TYPE     : std_logic_vector := "00";
   constant BM_REQ_DISTMEM_TYPE : integer := 16;

   constant NP2RP_FIFO_ITEMS  : integer := BLOCK_SIZE;
   constant NP2RP_FIFO_DT     : integer := 32;
   constant NP2RP_FIFO_DW     : integer := LENGTH_WIDTH+
                                           log2(CHANNELS)+NUM_FLAGS;

   type TCNT_ARRAY is array (0 to CHANNELS-1) of 
                    std_logic_vector(log2(NP2RP_FIFO_ITEMS+1)-1 downto 0);

   type TSTRPTR_ARRAY is array (0 to CHANNELS-1) of 
                               std_logic_vector(LENGTH_WIDTH-1-3 downto 0);

   type TRELLEN_ARRAY is array (0 to CHANNELS-1) of 
                               std_logic_vector(LENGTH_WIDTH-1 downto 0);

   type TACCPTR_ARRAY is array (0 to CHANNELS-1) of 
                               std_logic_vector(LENGTH_WIDTH-1-3 downto 0);
   signal ra_strptr        : TSTRPTR_ARRAY;
   signal buf_rel_len      : TRELLEN_ARRAY;
   signal acc_strptr       : TACCPTR_ARRAY;
   signal strptr           : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal endptr           : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal str_allign       : std_logic_vector(CHANNELS-1 downto 0);
   signal end_allign       : std_logic;
   signal acc_endptr       : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal tmp_acc          : std_logic_vector(LENGTH_WIDTH-1 downto 0);


   type TLADDR_ARRAY is array (0 to CHANNELS-1) of std_logic_vector(31 downto 0);

   function laddr_array_init(empty: in integer) return TLADDR_ARRAY is
   variable ra : TLADDR_ARRAY;
   variable product : std_logic_vector(63 downto 0);
   begin
      for i in 0 to CHANNELS - 1 loop
         product := conv_std_logic_vector(i,32)*BUFFER_GAP;
         ra(i) := product(31 downto 0)+BUFFER_ADDR;
      end loop;
      return ra;
   end;

   signal ra_laddr         : TLADDR_ARRAY := laddr_array_init(0);

   signal ra_endptr_sclr   : std_logic;
   signal ra_endptr_wea    : std_logic;
   signal ra_endptr_bea    : std_logic_vector((LENGTH_WIDTH/8)-1 downto 0);
   signal ra_endptr_addra  : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal ra_endptr_dia    : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal ra_endptr_doa    : std_logic_vector(LENGTH_WIDTH-1 downto 0);

   signal ra_desclen_sclr  : std_logic;
   signal ra_desclen_wea   : std_logic;
   signal ra_desclen_bea   : std_logic_vector((LENGTH_WIDTH/8)-1 downto 0);
   signal ra_desclen_addra : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal ra_desclen_dia   : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal ra_desclen_doa   : std_logic_vector(LENGTH_WIDTH-1 downto 0);

   signal desclen          : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal freespace        : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal ptrdiff          : std_logic_vector(log2(BUFFER_SIZE)-1 downto 0);

   signal ra_flags_sclr    : std_logic;
   signal ra_flags_wea     : std_logic;
   signal ra_flags_bea     : std_logic_vector((NUM_FLAGS/8)-1 downto 0);
   signal ra_flags_addra   : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal ra_flags_dia     : std_logic_vector(NUM_FLAGS-1 downto 0);
   signal ra_flags_doa     : std_logic_vector(NUM_FLAGS-1 downto 0);

   signal ra_rellen_sclr   : std_logic;
   signal ra_rellen_wea    : std_logic;
   signal ra_rellen_bea    : std_logic_vector((LENGTH_WIDTH/8)-1 downto 0);
   signal ra_rellen_addra  : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal ra_rellen_dia    : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal ra_rellen_doa    : std_logic_vector(LENGTH_WIDTH-1 downto 0);


   signal mux_desc_empty   : std_logic_vector(0 downto 0);

   signal cnt_chid         : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal cnt_chid_ce      : std_logic;
   signal cnt_chid_ld      : std_logic;

   signal fsm_run          : std_logic;
   signal fsm_reg_len_dv   : std_logic;
   signal fsm_enough_space : std_logic;
   signal fsm_fifo_full    : std_logic;
   signal fsm_length_we    : std_logic;
   signal fsm_update       : std_logic;
   signal fsm_bm_req       : std_logic;
   signal fsm_bm_reqw1     : std_logic;
   signal fsm_bm_reqw2     : std_logic;

   signal fifo_di          : std_logic_vector(NP2RP_FIFO_DW-1 downto 0);
   signal fifo_wr          : std_logic;
   signal fifo_full        : std_logic;
   signal fifo_lstblk      : std_logic;
   signal fifo_do          : std_logic_vector(NP2RP_FIFO_DW-1 downto 0);
   signal fifo_rd          : std_logic;
   signal fifo_empty       : std_logic;

   signal fifo_rel_chid    : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal fifo_rel_flags   : std_logic_vector(NUM_FLAGS-1 downto 0);
   signal fifo_rel_len     : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal rel_op_done      : std_logic_vector(0 downto 0);
   signal rel_len          : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal release_packet   : std_logic;

   signal demux_rellen_dv_out : std_logic_vector(CHANNELS-1 downto 0);

   signal buff_addr        : std_logic_vector(31 downto 0);
   signal buff_offset      : std_logic_vector(32 + log2(CHANNELS)-1 downto 0);

   signal mux_req_di_sel     : std_logic;
   signal mux_acc_endptr_sel : std_logic;

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

   signal cnt_dma_in_progress      : TCNT_ARRAY;
   signal cnt_dma_in_progress_up   : std_logic_vector(CHANNELS-1 downto 0);
   signal cnt_dma_in_progress_down : std_logic_vector(CHANNELS-1 downto 0);
   signal no_dma_in_progress       : std_logic_vector(CHANNELS-1 downto 0);

   signal dec_idle_enable    : std_logic;

begin

   assert (NP2RP_FIFO_DT >= NP2RP_FIFO_DW)
   report "fifo dist mem type is invalid, sjould be more than data width"
   severity error;

---------------------------------------------------------------------------
-- hw pointers logic
---------------------------------------------------------------------------
GEN_STRPTR: for i in 0 to CHANNELS-1 generate

   -- register array ra_strptr -----------------------------------------------
   ra_strptrp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            ra_strptr(i) <= (others => '0');
         elsif (BUF_RELLEN_DV(i) = '1') then
            ra_strptr(i) <= acc_strptr(i);
         end if;
      end if;
   end process;

   -- tx buffer always release 8B alligned amount of memory
   buf_rel_len(i) <= BUF_RELLEN(LENGTH_WIDTH*(i+1)-1 downto LENGTH_WIDTH*i);
   str_allign(i) <= buf_rel_len(i)(0) or buf_rel_len(i)(1) or buf_rel_len(i)(2);
   acc_strptr(i) <= ra_strptr(i) + str_allign(i) + 
                    buf_rel_len(i)(LENGTH_WIDTH-1 downto 3);
end generate;

strptr <= ra_strptr(conv_integer(cnt_chid)) & "000";
---------------------------------------------------------------------------
-- end pointer - register array
---------------------------------------------------------------------------
reg_array_endptr_i: entity work.reg_array_sp_be
   generic map(
      DATA_WIDTH => LENGTH_WIDTH,
      ITEMS      => CHANNELS,
      INIT_DATA  => gndvec(LENGTH_WIDTH-1 downto 0)
   )
   port map(
      CLK   => CLK,

      SCLR  => ra_endptr_sclr,
      -- read/write PORT
      WEA   => ra_endptr_wea,
      BEA   => ra_endptr_bea,
      ADDRA => ra_endptr_addra,
      DIA   => ra_endptr_dia,
      DOA   => ra_endptr_doa
   );

endptr          <= ra_endptr_doa;
ra_endptr_sclr  <= '0';
ra_endptr_wea   <= fsm_update;
ra_endptr_addra <= cnt_chid;
ra_endptr_bea   <= not gndvec(ra_endptr_bea'length-1 downto 0);
ra_endptr_dia   <= acc_endptr;

-- if there is a lff in descriptor flags - allign endptr to 8B
-- otherwise not
mux_acc_endptr_sel <= ra_flags_doa(PAC_DMA_LFF);
-- multiplexor mux_acc_endptr ------------------------------------------------------
mux_acc_endptrp: process(mux_acc_endptr_sel, tmp_acc, end_allign)
begin
   case mux_acc_endptr_sel is
      when '0' => acc_endptr <= tmp_acc;
      when '1' => acc_endptr <= (tmp_acc(LENGTH_WIDTH-1 downto 3) + end_allign)
                                & "000";
      when others => acc_endptr <= (others => 'X');
   end case;
end process;

tmp_acc <= endptr + ra_desclen_doa;

end_allign <= tmp_acc(0) or tmp_acc(1) or tmp_acc(2);

---------------------------------------------------------------------------
-- new packet fsm - packet transmission - DMA request
---------------------------------------------------------------------------
new_packet_fsm_i: entity work.TX_NEW_PACKET_FSM
   port map(
      -- global signals 
      CLK            => CLK,
      RESET          => RESET,

      -- input signals
      RUN            => fsm_run,
      REG_LEN_DV     => fsm_reg_len_dv,
      ENOUGH_SPACE   => fsm_enough_space,
      DESC_DV        => DESC_DO_VLD,
      DESC_EMPTY     => mux_desc_empty(0), 
      FIFO_FULL      => fsm_fifo_full,
      BM_ACK         => DMA_ACK,
      
      -- output signals
      GET_DESC       => DESC_READ,
      NEXT_CHID      => cnt_chid_ce,
      BM_REQ         => fsm_bm_req,
      BM_REQW1       => fsm_bm_reqw1,
      BM_REQW2       => fsm_bm_reqw2,
      LENGTH_WE      => fsm_length_we,
      UPDATE         => fsm_update
   );

fsm_run        <= RUN(conv_integer(cnt_chid));
fsm_fifo_full  <= fifo_full or SU_HFULL(conv_integer(cnt_chid));

-- desc empty multiplexor
mux_desc_empty_dv_i: entity work.gen_mux
   generic map (
      DATA_WIDTH  => 1,
      MUX_WIDTH   => CHANNELS
   )
   port map (
      DATA_IN  => DESC_EMPTY, 
      SEL      => cnt_chid,
      DATA_OUT => mux_desc_empty
   );

DESC_ADDR <= cnt_chid;

-- channel index counter
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

cnt_chid_ld <= '1' when 
            (cnt_chid = conv_std_logic_vector(CHANNELS-1, cnt_chid'length))
                   else '0';

reg_array_desclen_i: entity work.reg_array_sp_be
   generic map(
      DATA_WIDTH => LENGTH_WIDTH,
      ITEMS      => CHANNELS,
      INIT_DATA  => gndvec(LENGTH_WIDTH-1 downto 0)
   )
   port map(
      CLK   => CLK,

      SCLR  => ra_desclen_sclr,
      -- read/write PORT
      WEA   => ra_desclen_wea,
      BEA   => ra_desclen_bea,
      ADDRA => ra_desclen_addra,
      DIA   => ra_desclen_dia,
      DOA   => ra_desclen_doa
   );

ra_desclen_addra <= cnt_chid;
ra_desclen_bea   <= not gndvec(ra_desclen_bea'length-1 downto 0);
ra_desclen_wea   <= fsm_length_we;
ra_desclen_sclr  <= fsm_update;
ra_desclen_dia   <= DESC_DO(LENGTH_WIDTH-1 downto 0); 

-- data in register array are valid if they differ from 0
fsm_reg_len_dv <= '1' when ra_desclen_doa /= gndvec(LENGTH_WIDTH-1 downto 0)
                      else '0';
-- length of data
desclen <= ra_desclen_doa when fsm_length_we = '0' else ra_desclen_dia;
-- occupied space
ptrdiff <=strptr(log2(BUFFER_SIZE)-1 downto 0)-
          endptr(log2(BUFFER_SIZE)-1 downto 0);

freespace <= gndvec(LENGTH_WIDTH - 1 downto log2(BUFFER_SIZE)) & ptrdiff;

-- there is enough space in tx buffer for packet 
-- there should not be a packet larger than hw tx buffer
fsm_enough_space <= '1' when freespace >= desclen  or strptr = endptr else '0';

reg_array_flags_i: entity work.reg_array_sp_be
   generic map(
      DATA_WIDTH => NUM_FLAGS,
      ITEMS      => CHANNELS,
      INIT_DATA  => gndvec(NUM_FLAGS-1 downto 0)
   )
   port map(
      CLK   => CLK,

      SCLR  => ra_flags_sclr,
      -- read/write PORT
      WEA   => ra_flags_wea,
      BEA   => ra_flags_bea,
      ADDRA => ra_flags_addra,
      DIA   => ra_flags_dia,
      DOA   => ra_flags_doa
   );

-- flags are stored in upper part of word with length
ra_flags_wea   <= fsm_length_we;
ra_flags_bea   <= not gndvec(ra_flags_bea'length-1 downto 0);
ra_flags_addra <= cnt_chid;
ra_flags_dia   <= DESC_DO(32+NUM_FLAGS-1 downto 32);

---------------------------------------------------------------------------
-- DMA request memory
---------------------------------------------------------------------------
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
bm_req_we      <= fsm_bm_reqw1 or fsm_bm_reqw2;
-- if we are writting second word, set address to 1
bm_req_addra(0)<= fsm_bm_reqw2;

mux_req_di_sel <= fsm_bm_reqw2;
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
DMA_REQ  <= fsm_bm_req;
bm_ttype <= TRANS_TYPE;

bm_gaddr    <= DESC_DO;
bm_laddr    <= buff_addr(buff_addr'length-1 downto log2(BUFFER_SIZE)) & 
               endptr(log2(BUFFER_SIZE)-1 downto 0);
bm_length   <= ra_desclen_doa(11 downto 0);
bm_tag      <= gndvec(15 downto DMA_ID'length) & DMA_ID;
bm_ttype    <= TRANS_TYPE;

buff_addr <= ra_laddr(conv_integer(cnt_chid)); 

-- read first/second word of bm request
bm_req_addrb(0) <= DMA_ADDR(DMA_ADDR'length-1);

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

---------------------------------------------------------------------------
-- cnt dma in progress for status indication
-- we have to know if there are any transfers in progress
---------------------------------------------------------------------------
-- increment counter when we put request in fifo
dec1fn_dma_up_i: entity work.dec1fn_enable
   generic map (
      ITEMS    => CHANNELS
   )
   port map (
      ADDR     => cnt_chid,
      ENABLE   => fsm_update,
      DO       => cnt_dma_in_progress_up
   );

-- decrement counter when we inform tx buffer
cnt_dma_in_progress_down <= demux_rellen_dv_out;

gen_cnt_dma: for i in 0 to CHANNELS-1 generate

   -- cnt_dma_in_progress counter
   cnt_dma_in_progressp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_dma_in_progress(i) <= (others => '0');
         elsif (cnt_dma_in_progress_up(i) = '1' and 
                cnt_dma_in_progress_down(i) = '0') then
               cnt_dma_in_progress(i) <= cnt_dma_in_progress(i) + 1;
         elsif (cnt_dma_in_progress_down(i) = '1' and
                cnt_dma_in_progress_up(i) = '0') then
               cnt_dma_in_progress(i) <= cnt_dma_in_progress(i) - 1;
         end if;
      end if;
   end process;

   no_dma_in_progress(i) <= '1' when (cnt_dma_in_progress(i) =
                        conv_std_logic_vector(0, cnt_dma_in_progress(i)'length))
                           else '0';
end generate;

dec1fn_idle_i: entity work.dec1fn_enable
   generic map (
      ITEMS    => CHANNELS
   )
   port map (
      ADDR     => cnt_chid,
      ENABLE   => dec_idle_enable,
      DO       => IDLE
   );

-- no dma in progress and we are moving to next channel and new dma request
-- hasn`t been sent
dec_idle_enable <= no_dma_in_progress(conv_integer(cnt_chid)) and 
                   cnt_chid_ce and 
                   not cnt_dma_in_progress_up(conv_integer(cnt_chid));

---------------------------------------------------------------------------
-- fifo from new packet part to release packet
---------------------------------------------------------------------------
fifo_np2rp_i: entity work.fifo
   generic map (
      DATA_WIDTH     => NP2RP_FIFO_DW,
      DISTMEM_TYPE   => NP2RP_FIFO_DT,
      ITEMS          => NP2RP_FIFO_ITEMS,
      BLOCK_SIZE     => 0
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,

      --Write interface
      DATA_IN     => fifo_di,
      WRITE_REQ   => fifo_wr,
      FULL        => fifo_full,
      LSTBLK      => fifo_lstblk,

      -- Read interface
      DATA_OUT    => fifo_do,
      READ_REQ    => fifo_rd,
      EMPTY       => fifo_empty
   );

fifo_di <= cnt_chid & ra_flags_doa & ra_desclen_doa;
fifo_wr <= fsm_update;

---------------------------------------------------------------------------
-- packet release logic
---------------------------------------------------------------------------
fifo_rd     <= DMA_DONE;

fifo_rel_chid  <= fifo_do(NP2RP_FIFO_DW-1 downto NUM_FLAGS+LENGTH_WIDTH);
fifo_rel_len   <= fifo_do(LENGTH_WIDTH-1 downto 0);
fifo_rel_flags <= fifo_do(NUM_FLAGS+LENGTH_WIDTH-1 downto LENGTH_WIDTH);
-- release only packets with lff, otherwise accumulate length
release_packet <= fifo_rel_flags(PAC_DMA_LFF) and DMA_DONE;

reg_array_rellen_i: entity work.reg_array_sp_be
   generic map(
      DATA_WIDTH => LENGTH_WIDTH,
      ITEMS      => CHANNELS,
      INIT_DATA  => gndvec(LENGTH_WIDTH-1 downto 0)
   )
   port map(
      CLK   => CLK,

      SCLR  => ra_rellen_sclr,
      -- read/write PORT
      WEA   => ra_rellen_wea,
      BEA   => ra_rellen_bea,
      ADDRA => ra_rellen_addra,
      DIA   => ra_rellen_dia,
      DOA   => ra_rellen_doa
   );

-- cleat accumulated value
ra_rellen_sclr  <= release_packet;
-- store for later release
ra_rellen_wea   <= DMA_DONE and not fifo_rel_flags(PAC_DMA_LFF);
ra_rellen_addra <= fifo_rel_chid;
ra_rellen_bea   <= not gndvec(ra_rellen_bea'length-1 downto 0);
ra_rellen_dia   <= rel_len;

rel_len <= ra_rellen_doa + fifo_rel_len;

SU_ADDR     <= fifo_rel_chid;
SU_DATA     <= fifo_rel_flags;
SU_DATA_VLD <= release_packet;

demux_rellen_i: entity work.gen_demux
   generic map (
      DATA_WIDTH  => 16,
      DEMUX_WIDTH => CHANNELS,
      DEF_VALUE   => '0'
   )
   port map (
      DATA_IN  => rel_len,
      SEL      => fifo_rel_chid,
      DATA_OUT => BUF_NEWLEN
   );

rel_op_done(0)  <= release_packet;
demux_rellen_dv_i: entity work.gen_demux
   generic map (
      DATA_WIDTH  => 1,
      DEMUX_WIDTH => CHANNELS,
      DEF_VALUE   => '0'
   )
   port map (
      DATA_IN  => rel_op_done,
      SEL      => fifo_rel_chid,
      DATA_OUT => demux_rellen_dv_out
   );

BUF_NEWLEN_DV <= demux_rellen_dv_out;

end architecture tx_ctrl_behav;
