-- rx_ctrl_arch.vhd: Packet RX DMA controller architecture.
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
architecture rx_ctrl_behav of rx_ctrl is
   constant gndvec         : std_logic_vector(63 downto 0) := (others => '0');

   -- packet length signal width - from rx buff
   constant LENGTH_WIDTH   : integer := 16;
   -- type of transaction - FPGA2RAM
   constant TRANS_TYPE     : std_logic_vector := "01";
   constant BM_REQ_DISTMEM_TYPE : integer := 16;


   constant NP2RP_FIFO_ITEMS  : integer := BLOCK_SIZE;
   constant NP2RP_FIFO_DT     : integer := 32;
   constant NP2RP_FIFO_DW     : integer := LENGTH_WIDTH + 
                                           log2(CHANNELS) + NUM_FLAGS;

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

   type TCNT_ARRAY is array (0 to CHANNELS-1) of 
                    std_logic_vector(log2(NP2RP_FIFO_ITEMS+1)-1 downto 0);

   signal buff_addr        : std_logic_vector(31 downto 0);
   signal buff_offset      : std_logic_vector(32 + log2(CHANNELS)-1 downto 0);
   signal sig_desc_do      : std_logic_vector(63 downto 0);
   signal cnt_chid         : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal cnt_chid_ce      : std_logic;
   signal cnt_chid_ld      : std_logic;

   signal fsm_run          : std_logic;
   signal fsm_new_desc_ne  : std_logic;
   signal fsm_new_desc_dv  : std_logic;
   signal fsm_new_len      : std_logic;
   signal fsm_fifo_full    : std_logic;
   signal fsm_get_desc     : std_logic;
   signal fsm_lenflags_we  : std_logic;
   signal fsm_bm_req       : std_logic;
   signal fsm_bm_reqw1     : std_logic;
   signal fsm_bm_reqw2     : std_logic;
   signal fsm_update_regs  : std_logic;

   signal reg_act_len      : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal reg_act_len_we   : std_logic;
   signal reg_desc_flags   : std_logic_vector(NUM_FLAGS-1 downto 0);
   signal reg_desc_flags_we : std_logic;

   signal mux_newlen       : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal mux_newlen_dv    : std_logic_vector(0 downto 0);
   signal mux_desc_empty   : std_logic_vector(0 downto 0);
   signal demux_newlen_rdy : std_logic_vector(0 downto 0);
   signal demux_newlen_rdy_out : std_logic_vector(CHANNELS-1 downto 0);
   signal demux_rellen_dv_out  : std_logic_vector(CHANNELS-1 downto 0);
   signal desc_len         : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal act_len          : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal newlen           : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal newlen_rem_frag  : std_logic;
   signal pipe_newlen      : std_logic_vector(LENGTH_WIDTH-1 downto 0);

   signal reg_newlen_dia   : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal ra_newlen_wea    : std_logic;
   signal ra_newlen_bea    : std_logic_vector((LENGTH_WIDTH/8)-1 downto 0);
   signal ra_newlen_addra  : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal ra_newlen_dia    : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal ra_newlen_doa    : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal ra_newlen_sclr   : std_logic;
   signal release_packet   : std_logic;
   signal pipe_release_packet : std_logic;

   signal ra_hwptr_wea     : std_logic;
   signal ra_hwptr_bea     : std_logic_vector((LENGTH_WIDTH/8)-1 downto 0);
   signal ra_hwptr_addra   : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal ra_hwptr_dia     : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal ra_hwptr_doa     : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal ra_hwptr_sclr    : std_logic;

   signal ra_rellen_wea    : std_logic;
   signal ra_rellen_bea    : std_logic_vector((LENGTH_WIDTH/8)-1 downto 0);
   signal ra_rellen_addra  : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal ra_rellen_dia    : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal ra_rellen_doa    : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal ra_rellen_sclr   : std_logic;

   signal fifo_di          : std_logic_vector(NP2RP_FIFO_DW-1 downto 0);
   signal fifo_wr          : std_logic;
   signal fifo_full        : std_logic;
   signal fifo_lstblk      : std_logic;
   signal fifo_do          : std_logic_vector(NP2RP_FIFO_DW-1 downto 0);
   signal fifo_rd          : std_logic;
   signal fifo_empty       : std_logic;

   signal pipe_fifo_rel_chid : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal fifo_rel_chid    : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal fifo_rel_flags   : std_logic_vector(NUM_FLAGS-1 downto 0);
   signal fifo_rel_len     : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal op_done          : std_logic_vector(0 downto 0);
   signal rel_len          : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal pipe_rel_len     : std_logic_vector(LENGTH_WIDTH-1 downto 0);

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

   signal mux_req_di_sel      : std_logic;
   signal acc_hwptr           : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal mux_acc_hwptr_sel   : std_logic;
   signal reg_lff             : std_logic;
   signal reg_lff_set         : std_logic;
   signal reg_lff_clr         : std_logic;
   signal hwptr_allign        : std_logic;
   signal cnt_dma_in_progress      : TCNT_ARRAY;
   signal cnt_dma_in_progress_up   : std_logic_vector(CHANNELS-1 downto 0);
   signal cnt_dma_in_progress_down : std_logic_vector(CHANNELS-1 downto 0);
   signal no_dma_in_progress       : std_logic_vector(CHANNELS-1 downto 0);

   signal dec_idle_enable     : std_logic;

begin

   assert (NP2RP_FIFO_DT >= NP2RP_FIFO_DW)
   report "fifo dist mem type is invalid, should be more than data width"
   severity error;

-- new descriptor interface from desc. download manager
DESC_READ       <= fsm_get_desc;
DESC_ADDR       <= cnt_chid;
sig_desc_do     <= DESC_DO ;
fsm_new_desc_dv <= DESC_DO_VLD;
fsm_new_desc_ne <= not mux_desc_empty(0);

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
               ra_hwptr_doa(log2(BUFFER_SIZE)-1 downto 0);
bm_length   <= reg_act_len(11 downto 0);
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

-- new packet fsm - handles newly arrived packets
new_packet_fsm_i: entity work.RX_NEW_PACKET_FSM
   port map (
      -- global signals 
      CLK            => CLK,
      RESET          => RESET,

      -- input signals
      RUN            => fsm_run,
      NEW_DESC_NE    => fsm_new_desc_ne,
      NEW_DESC_DV    => fsm_new_desc_dv,
      NEW_LEN        => fsm_new_len,
      BM_ACK         => DMA_ACK,
      FIFO_FULL      => fsm_fifo_full,
      
      -- output signals
      GET_DESC       => fsm_get_desc,
      NEXT_CHID      => cnt_chid_ce,
      BM_REQ         => fsm_bm_req,
      BM_REQW1       => fsm_bm_reqw1,
      BM_REQW2       => fsm_bm_reqw2,
      LENFLAGS_WE    => fsm_lenflags_we,
      UPDATE_REGS    => fsm_update_regs
   );

fsm_run        <= RUN(conv_integer(cnt_chid)) or newlen_rem_frag;
fsm_fifo_full  <= fifo_full or SU_HFULL(conv_integer(cnt_chid));

reg_act_len_we <= fsm_lenflags_we;
-- register reg_act_len ------------------------------------------------------
reg_act_lenp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         reg_act_len <= (others => '0');
      elsif (reg_act_len_we = '1') then
         reg_act_len <= act_len;
      end if;
   end if;
end process;

reg_desc_flags_we <= fsm_lenflags_we;
-- register reg_desc_flags ------------------------------------------------------
reg_desc_flagsp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         reg_desc_flags <= (others => '0');
      elsif (reg_desc_flags_we = '1') then
         reg_desc_flags <= sig_desc_do(32+NUM_FLAGS-1 downto 32);
      end if;
   end if;
end process;

---------------------------------------------------------------------------
-- new len register array - to store length of rx packets fragments
-- when there is a packet longer than space given by descriptor
---------------------------------------------------------------------------
reg_array_newlen_i: entity work.reg_array_sp_be
   generic map (
      DATA_WIDTH  => LENGTH_WIDTH,
      ITEMS       => CHANNELS,
      INIT_DATA   => gndvec(LENGTH_WIDTH-1 downto 0)
   )
   port map (
      CLK   => CLK,
      SCLR  => ra_newlen_sclr,
      -- read/write PORT
      WEA   => ra_newlen_wea,
      BEA   => ra_newlen_bea,
      ADDRA => ra_newlen_addra,
      DIA   => ra_newlen_dia,
      DOA   => ra_newlen_doa
   );

ra_newlen_wea     <= fsm_update_regs;
ra_newlen_bea     <= not gndvec(ra_newlen_bea'length-1 downto 0);
ra_newlen_addra   <= cnt_chid;
ra_newlen_dia     <= reg_newlen_dia;

-- are there any rests of previous packet?
newlen_rem_frag <= '0' when 
                           ra_newlen_doa = gndvec(LENGTH_WIDTH-1 downto 0)
                                 else '1';

-- when there is a remaining fragment of previous packet
-- use it as new length
newlen  <= mux_newlen when newlen_rem_frag = '0'
                       else ra_newlen_doa;


-- register pipe_newlen ------------------------------------------------------
pipe_newlenp: process(RESET, CLK)
begin
   if (CLK'event AND CLK = '1') then
      pipe_newlen <= newlen;
   end if;
end process;

-- new len data valid signal for new packet fsm
-- when there is a rest of previous packet then 1
-- else it depends on mux_newlen_dv
fsm_new_len <= mux_newlen_dv(0) when newlen_rem_frag = '0'
                       else '1';

-- length stored in descriptor
desc_len <= sig_desc_do(LENGTH_WIDTH-1 downto 0);

-- compute actual length, if packet is too long use only desc. length
-- else newlen
act_len <= desc_len when (desc_len < pipe_newlen) else pipe_newlen;

reg_lff_set <= '0' when (desc_len < pipe_newlen) else '1'; 
reg_lff_clr <= not reg_lff_set;
-- last fragment flag register - indicates last fragment of packet
-- register reg_lff ------------------------------------------------------
reg_lffp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         reg_lff <= '0';
      elsif (reg_lff_set = '1' and fsm_lenflags_we = '1') then
         reg_lff <= '1';
      elsif (reg_lff_clr = '1' and fsm_lenflags_we = '1') then
         reg_lff <= '0';
      end if;
   end if;
end process;


-- register reg_newlen_dia ------------------------------------------------------
reg_newlen_diap: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
         reg_newlen_dia <= (newlen - reg_act_len);
   end if;
end process;

---------------------------------------------------------------------------
-- multiplexors for buffers connecting signals
---------------------------------------------------------------------------
-- new packet length multiplexor
mux_newlen_i: entity work.gen_mux
   generic map (
      DATA_WIDTH  => LENGTH_WIDTH,
      MUX_WIDTH   => CHANNELS
   )
   port map (
      DATA_IN  => BUF_NEWLEN, 
      SEL      => cnt_chid,
      DATA_OUT => mux_newlen
   );

mux_newlen_dv_i: entity work.gen_mux
   generic map (
      DATA_WIDTH  => 1,
      MUX_WIDTH   => CHANNELS
   )
   port map (
      DATA_IN  => BUF_NEWLEN_DV, 
      SEL      => cnt_chid,
      DATA_OUT => mux_newlen_dv
   );

demux_newlen_rdy_i: entity work.gen_demux
   generic map (
      DATA_WIDTH  => 1,
      DEMUX_WIDTH => CHANNELS,
      DEF_VALUE   => '0'
   )
   port map (
      DATA_IN  => demux_newlen_rdy,
      SEL      => cnt_chid,
      DATA_OUT => demux_newlen_rdy_out
   );

BUF_NEWLEN_RDY <= demux_newlen_rdy_out;
-- accept newlen from buffer when registers are being updated
-- i.e. bm ack strobe and it is first part of packet
demux_newlen_rdy(0) <= fsm_update_regs and (not newlen_rem_frag);
---------------------------------------------------------------------------
-- register array of hardware pointers - pointer to actual data in rx buf
---------------------------------------------------------------------------
reg_array_hwptr_i: entity work.reg_array_sp_be
   generic map (
      DATA_WIDTH  => LENGTH_WIDTH,
      ITEMS       => CHANNELS,
      INIT_DATA   => gndvec(LENGTH_WIDTH-1 downto 0)
   )
   port map (
      CLK   => CLK,
      SCLR  => ra_hwptr_sclr,
      -- read/write PORT
      WEA   => ra_hwptr_wea,
      BEA   => ra_hwptr_bea,
      ADDRA => ra_hwptr_addra,
      DIA   => ra_hwptr_dia,
      DOA   => ra_hwptr_doa
   );

ra_hwptr_wea   <= fsm_update_regs;
ra_hwptr_bea   <= not gndvec(ra_hwptr_bea'length-1 downto 0);
ra_hwptr_addra <= cnt_chid;
ra_hwptr_dia   <= acc_hwptr;

mux_acc_hwptr_sel <= reg_lff;
-- multiplexor mux_acc_hwptr ------------------------------------------------------
mux_acc_hwptrp: process(mux_acc_hwptr_sel, ra_hwptr_doa, reg_act_len,
                        hwptr_allign)
begin
   case mux_acc_hwptr_sel is
      when '0' => acc_hwptr <= ra_hwptr_doa + reg_act_len;
      when '1' => acc_hwptr <= (ra_hwptr_doa(LENGTH_WIDTH-1 downto 3) +
                               reg_act_len(LENGTH_WIDTH-1 downto 3) +
                               hwptr_allign) & "000";
      when others => acc_hwptr <= (others => 'X');
   end case;
end process;

hwptr_allign <= '0' when (ra_hwptr_doa(2 downto 0) + reg_act_len(2 downto 0))=0
                    else '1';
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

fifo_di <= cnt_chid & reg_desc_flags(NUM_FLAGS-1 downto PAC_DMA_LFF+1) &
            reg_lff & reg_desc_flags(0) & reg_act_len;

fifo_wr <= fsm_update_regs;
---------------------------------------------------------------------------
-- cnt dma in progress for status indication
-- we have to know if there are any transfers in progress
---------------------------------------------------------------------------
-- increment counter when we read length from rx buff
cnt_dma_in_progress_up <= demux_newlen_rdy_out;
-- decrement counter when we release packet from rx buff
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
-- packet release logic
---------------------------------------------------------------------------

fifo_rd <= DMA_DONE; 

fifo_rel_chid  <= fifo_do(NP2RP_FIFO_DW-1 downto NP2RP_FIFO_DW-log2(CHANNELS));
fifo_rel_flags <= fifo_do(NP2RP_FIFO_DW-log2(CHANNELS)-1 downto
                       NP2RP_FIFO_DW-log2(CHANNELS)-NUM_FLAGS);
fifo_rel_len   <= fifo_do(LENGTH_WIDTH-1 downto 0);

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
SU_DATA     <= fifo_rel_flags & rel_len;
SU_DATA_VLD <= release_packet;


demux_rellen_i: entity work.gen_demux
   generic map (
      DATA_WIDTH  => 16,
      DEMUX_WIDTH => CHANNELS,
      DEF_VALUE   => '0'
   )
   port map (
      DATA_IN  => pipe_rel_len,
      SEL      => pipe_fifo_rel_chid,
      DATA_OUT => BUF_RELLEN
   );

op_done(0)  <= pipe_release_packet;
demux_rellen_dv_i: entity work.gen_demux
   generic map (
      DATA_WIDTH  => 1,
      DEMUX_WIDTH => CHANNELS,
      DEF_VALUE   => '0'
   )
   port map (
      DATA_IN  => op_done,
      SEL      => pipe_fifo_rel_chid,
      DATA_OUT => demux_rellen_dv_out
   );

BUF_RELLEN_DV <= demux_rellen_dv_out;


-- register pipe_rel_len ------------------------------------------------------
pipe_rel_lenp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      pipe_rel_len <= rel_len;
   end if;
end process;


-- register pipe_fifo_rel_chid ------------------------------------------------------
pipe_fifo_rel_chidp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      pipe_fifo_rel_chid <= fifo_rel_chid;
   end if;
end process;

-- register pipe_release_packet ------------------------------------------------------
pipe_release_packetp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      pipe_release_packet <= release_packet;
   end if;
end process;

end architecture rx_ctrl_behav;
