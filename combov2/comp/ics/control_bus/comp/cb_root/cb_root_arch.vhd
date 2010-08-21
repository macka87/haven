-- cb_root_arch.vhd : Control Bus root component architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
use ieee.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.cb_pkg.all; -- Control Bus package

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cb_root_arch of cb_root is

constant CNT_W : integer := QADDR_WIDTH-3;   -- Width of most counters
constant one   : std_logic_vector(7 downto 0) := "00000001";
constant zeros : std_logic_vector(7 downto 0) := "00000000";

signal txq_wea       : std_logic;
signal txq_doa_dv    : std_logic;
signal txq_doa       : std_logic_vector(63 downto 0);
signal rxq_doa_dv    : std_logic;
signal rxq_doa       : std_logic_vector(63 downto 0);

signal txq_reb       : std_logic;
signal txq_addrb     : std_logic_vector(QADDR_WIDTH downto 0);
signal txq_dob_dv    : std_logic;
signal txq_dob       : std_logic_vector(15 downto 0);

signal cnt_qfull     : std_logic_vector(15 downto 0);

signal rxq_web       : std_logic;
signal rxq_addrb     : std_logic_vector(QADDR_WIDTH downto 0);
signal rxq_dib       : std_logic_vector(15 downto 0);

signal rxsp_di       : std_logic_vector(CNT_W downto 0);
signal rxsp_we       : std_logic;
signal rxsp_doa      : std_logic_vector(CNT_W downto 0);
signal rxsp_addrb    : std_logic_vector(3 downto 0);
signal rxsp_dob      : std_logic_vector(CNT_W downto 0);

signal rxep_di       : std_logic_vector(CNT_W downto 0);
signal rxep_we       : std_logic;
signal rxep_doa      : std_logic_vector(CNT_W downto 0);
signal rxep_dob      : std_logic_vector(CNT_W downto 0);

signal txsp_di       : std_logic_vector(CNT_W downto 0);
signal txsp_we       : std_logic;
signal txsp_doa      : std_logic_vector(CNT_W downto 0);
signal txsp_dob      : std_logic_vector(CNT_W downto 0);

signal txep_di       : std_logic_vector(CNT_W downto 0);
signal txep_we       : std_logic;
signal txep_doa      : std_logic_vector(CNT_W downto 0);
signal txep_addrb    : std_logic_vector(3 downto 0);
signal txep_dob      : std_logic_vector(CNT_W downto 0);

signal rxcnt_vrd     : std_logic_vector(CNT_W-1 downto 0);
signal rxcnt_vldsub  : std_logic;
signal rxcnt_outsub  : std_logic_vector(CNT_W-1 downto 0);
signal src_id        : std_logic_vector(3 downto 0);
signal rxcnt_vldadd  : std_logic;
signal rxcnt_fulladd : std_logic;
signal rxcnt_mask    : std_logic_vector(15 downto 0);
      
signal edbuf_vrd     : std_logic_vector(7 downto 0);
signal dst_id        : std_logic_vector(3 downto 0);
signal tx_msg_len    : std_logic_vector(CNT_W-1 downto 0);
signal edbuf_valsub  : std_logic_vector(7 downto 0);
signal edbuf_vldsub  : std_logic;
signal edbuf_outsub  : std_logic_vector(7 downto 0);
signal endpoint_freed: std_logic_vector(7 downto 0);
signal edbuf_addradd : std_logic_vector(3 downto 0);
signal edbuf_vldadd  : std_logic;
signal edbuf_fulladd : std_logic;
signal edbuf_mask    : std_logic_vector(15 downto 0);

signal cb_in_dst_rdy_n:std_logic;
signal cb_out_src_rdy_n:std_logic;
signal cb_out_sop_n  : std_logic;
signal cb_out_eop_n  : std_logic;
signal cb_out_data   : std_logic_vector(15 downto 0);

signal reg_rx_even   : std_logic;
signal reg_tx_even   : std_logic;

signal qdrd_mux_in   : std_logic_vector(127 downto 0);
signal reg_qaddr     : std_logic_vector(0 downto 0);
signal qdrd_mux_out  : std_logic_vector(63 downto 0);
signal reg_qdrd      : std_logic_vector(63 downto 0);
signal reg_qdrdy     : std_logic;

signal txcnt_vrd     : std_logic_vector(CNT_W-1 downto 0);
signal txcnt_vldsub  : std_logic;
signal txcnt_fullsub : std_logic;
signal txcnt_valsub  : std_logic_vector(CNT_W-1 downto 0);
signal txcnt_vldadd  : std_logic;
signal txcnt_outadd  : std_logic_vector(CNT_W-1 downto 0);
signal txcnt_mask    : std_logic_vector(15 downto 0);
signal txcnt_pend    : std_logic_vector(15 downto 0);
      

signal rdbuf_addr_rd : std_logic_vector(3 downto 0);
signal rdbuf_vrd     : std_logic_vector(CNT_W-1 downto 0);
signal rdbuf_addr_sub: std_logic_vector(3 downto 0);
signal rdbuf_value_sub:std_logic_vector(CNT_W-1 downto 0);
signal rdbuf_vld_sub : std_logic;
signal rdbuf_fullsub : std_logic;
signal rdbuf_out_sub : std_logic_vector(CNT_W-1 downto 0);
signal rdbuf_vld_add : std_logic;
signal rdbuf_mask    : std_logic_vector(15 downto 0);
signal rdbuf_pend    : std_logic_vector(15 downto 0);
signal reg_clr_rdbuf : std_logic;

signal reg_cdrd      : std_logic_vector(7 downto 0);
signal reg_cdrdy     : std_logic;
signal cmux1_in      : std_logic_vector(63 downto 0);
signal cmux1_out     : std_logic_Vector(7 downto 0);
signal reg_caddr_msb : std_logic_vector(0 downto 0);
signal cmux2_in      : std_logic_vector(2*16 - 1 downto 0);
signal cmux2_out     : std_logic_vector(15 downto 0);
signal cmuxm_out     : std_logic_vector(15 downto 0);
signal reg_cmuxm_out : std_logic_vector(15 downto 0);

signal arbiter_vector: std_logic_vector(15 downto 0);
signal arbiter_step  : std_logic;
signal arbiter_addr  : std_logic_vector(3 downto 0);
signal arbiter_vld   : std_logic;

signal f_arbiter_vector:std_logic_vector(15 downto 0);
signal f_arbiter_step: std_logic;
signal f_arbiter_addr: std_logic_vector(3 downto 0);
signal f_arbiter_vld : std_logic;

type t_tx_fsm is (sel_queue,      -- Wait for any job
                  get_msg_len,    -- Read meesage length from TX queue
                  compare_msg_len,-- Message length is at the output of TX q
                  check_msg_len,  -- Message length has been compared
                  send_header,    -- Send message header
                  send_body,      -- Send message body
                  send_init,      -- Send empty message to all endpoints
                  send_empty);    -- Send one empty message

signal tx_fsm        : t_tx_fsm;
signal tx_fsm_next   : t_tx_fsm;
signal tx_fsm_1      : t_tx_fsm;

signal cnt_send_init : std_logic_vector(3 downto 0);
signal cnt_send_empty: std_logic_vector(2 downto 0);

signal reg_msg_len   : std_logic_vector(7 downto 0);
signal cnt_msg_len   : std_logic_vector(7 downto 0);
signal reg_len_ok    : std_logic;

signal reg_tx_addr   : std_logic_vector(3 downto 0);

signal cbmux_in      : std_logic_vector(63 downto 0);
signal cbmux_out     : std_logic_vector(15 downto 0);
signal reg_cbout     : std_logic_vector(15 downto 0);
signal reg_rdy       : std_logic;
signal cbmux_sel     : std_logic_vector(1 downto 0);

begin

   -- This is a place where data intended to transfer are stored.
   -- It is organized to 16 queues of the same size.
   -- PPC may read and write.
   TX_QUEUES : entity work.QUEUE_BRAM
   generic map(
      ITEMS_B  => 2**(QADDR_WIDTH+1)
   )
   port map(
      RESET    => CB_RESET,
      
      -- PPC interface - 64 bit
      CLKA     => CB_CLK,
      REA      => QRD,
      WEA      => txq_wea,
      ADDRA    => QADDR(QADDR_WIDTH-2 downto 0),
      DIA      => QDWR,
      DMA      => QBE,
      DOA_DV   => txq_doa_dv,
      DOA      => txq_doa,

      -- Control Bus interface - 16 bit, aligned to 32 bits internally
      CLKB     => CB_CLK,
      REB      => txq_reb,
      WEB      => '0',
      ADDRB    => txq_addrb,
      DIB      => X"0000",
      DOB_DV   => txq_dob_dv,
      DOB      => txq_dob
   );
   txq_wea <= QWR and QADDR(QADDR_WIDTH-1);
   txq_addrb <= reg_tx_addr & txsp_doa(CNT_W-1 downto 0);
   txq_reb <= '1' when tx_fsm = get_msg_len or tx_fsm = send_body or
                       tx_fsm = send_header or tx_fsm = check_msg_len else
              '0';

   -- This is a place where recieved data are stored.
   -- It is organized to 16 queues of the same size.
   -- PPC may only read.
   RX_QUEUES : entity work.QUEUE_BRAM
   generic map(
      ITEMS_B  => 2**(QADDR_WIDTH+1)
   )
   port map(
      RESET    => CB_RESET,
      
      -- PPC interface - 64 bit
      CLKA     => CB_CLK,
      REA      => QRD,
      WEA      => '0',
      ADDRA    => QADDR(QADDR_WIDTH-2 downto 0),
      DIA      => (others => '0'),
      DMA      => (others => '0'),
      DOA_DV   => rxq_doa_dv,
      DOA      => rxq_doa,

      -- Control Bus interface - 16 bit, aligned to 32 bits internally
      CLKB     => CB_CLK,
      REB      => '0',
      WEB      => rxq_web,
      ADDRB    => rxq_addrb,
      DIB      => rxq_dib,
      DOB_DV   => open,
      DOB      => open
   );
   rxq_web <= '1' when (CB.UP.SRC_RDY_N = '0' and 
                        cb_in_dst_rdy_n = '0' and
                        CB.UP.SOP_N = '1') or
                       reg_rx_even = '1' else
              '0';
   rxq_dib <= CB.UP.DATA when (CB.UP.SRC_RDY_N = '0' and 
                               cb_in_dst_rdy_n = '0' and
                               CB.UP.SOP_N = '1') else
              X"0000";
   rxq_addrb <= src_id & rxep_doa(CNT_W-1 downto 0);

   -- This is a pointer to the oldest valid item in each RX queue.
   -- PPC writes number of items it has freed into RX counter
   -- and this value is also added to RX Start Pointer.
   -- PPC is connected to R/W port A
   RX_STARTP : entity work.DP_DISTMEM
   generic map(
      DATA_WIDTH  => CNT_W+1, -- One extra bit to detect fullnes like in FIFO
      ITEMS       => 16,-- 16 endpoints
      DISTMEM_TYPE=> 16,
      DEBUG       => false
   )
   port map(
      RESET       => CB_RESET,
      DI          => rxsp_di,
      WE          => rxsp_we,
      WCLK        => CB_CLK,
      ADDRA       => CADDR(3 downto 0),
      DOA         => rxsp_doa,
      ADDRB       => rxsp_addrb,
      DOB         => rxsp_dob
   );
   rxsp_addrb <= rxq_addrb(QADDR_WIDTH downto QADDR_WIDTH-3);
   rxsp_di <= rxsp_doa + ('0' & CDWR(CNT_W-1 downto 0));
   rxsp_we <= '1' when CADDR(7 downto 4) = "0000" and-- RX Counter address
                       CWR = '1' and                 -- Write request
                       CBE(0) = '1' else             -- Byte enabled
              '0';

   -- This is a pointer to the first free item in each RX queue.
   -- With each 16bit data word stored to RX Queue, this pointer
   -- is incremented by one.
   -- PPC is conected to R port B
   RX_ENDP : entity work.DP_DISTMEM
   generic map(
      DATA_WIDTH  => CNT_W+1, -- One extra bit to detect fullnes like in FIFO
      ITEMS       => 16,-- 16 endpoints
      DISTMEM_TYPE=> 16,
      DEBUG       => false
   )
   port map(
      RESET       => CB_RESET,
      DI          => rxep_di,
      WE          => rxep_we,
      WCLK        => CB_CLK,
      ADDRA       => rxq_addrb(QADDR_WIDTH downto QADDR_WIDTH-3),
      DOA         => rxep_doa,
      ADDRB       => CADDR(3 downto 0),
      DOB         => rxep_dob
   );
   rxep_di <= rxep_doa + 1;
   rxep_we <= '1' when rxq_web = '1' else
              '0';

   -- This is a pointer to the oldest valid item in each TX queue.
   -- With each 16bit data word sent via Control Bus, this pointer
   -- is incremented by one
   -- PPC is conected to R port B
   TX_STARTP : entity work.DP_DISTMEM
   generic map(
      DATA_WIDTH  => CNT_W+1, -- One extra bit to detect fullnes like in FIFO?
      ITEMS       => 16,-- 16 endpoints
      DISTMEM_TYPE=> 16,
      DEBUG       => false
   )
   port map(
      RESET       => CB_RESET,
      DI          => txsp_di,
      WE          => txsp_we,
      WCLK        => CB_CLK,
      ADDRA       => txq_addrb(QADDR_WIDTH downto QADDR_WIDTH-3),
      DOA         => txsp_doa,
      ADDRB       => CADDR(3 downto 0),
      DOB         => txsp_dob
   );
   txsp_di <= txsp_doa + 1;
   txsp_we <= '1' when (CB.DOWN.DST_RDY_N = '0' and cb_out_src_rdy_n = '0' and
                        (tx_fsm_next = send_body or tx_fsm_next = send_header))
                       or (tx_fsm_next = sel_queue and tx_fsm = send_body and
                           reg_tx_even = '1')
                       or (tx_fsm = check_msg_len and 
                           tx_fsm_next = send_header) else
              '0';

   -- This is pointer to the first free item in each TX queue.
   -- PPC writes number of items it has added to this queue to TX counter
   -- and this value is also added to TX End Pointer.
   -- PPC is conected to R/W port A
   TX_ENDP : entity work.DP_DISTMEM
   generic map(
      DATA_WIDTH  => CNT_W+1, -- One extra bit to detect fullnes like in FIFO?
      ITEMS       => 16,-- 16 endpoints
      DISTMEM_TYPE=> 16,
      DEBUG       => false
   )
   port map(
      RESET       => CB_RESET,
      DI          => txep_di,
      WE          => txep_we,
      WCLK        => CB_CLK,
      ADDRA       => CADDR(3 downto 0),
      DOA         => txep_doa,
      ADDRB       => txep_addrb,
      DOB         => txep_dob
   );
   txep_addrb <= (others => '0'); -- Port B is unused
   txep_di <= txep_doa + ('0' & CDWR(CNT_W-1 downto 0));
   txep_we <= '1' when CADDR(7 downto 4) = "0100" and
                       CWR = '1' and CBE(0) = '1' else
              '0';

   -- This is Counter of 16bit items in each RX queue.
   -- It is incremented by one with every item stored in RX queue and
   -- decremented when PPC writes value into it.
   RX_COUNTER : entity work.cntr_array
   generic map(
      DATA_WIDTH  => CNT_W,
      SWAP_PORTS  => false,
      FIFO_ITEMS  => 4,
      MASK_SET    => 0,
      MASK_BITS   => 2**CNT_W - 1
   )
   port map(
      CLK         => CB_CLK,
      RESET       => CB_RESET,

      VALUE_RD    => rxcnt_vrd,
      ADDR_RD     => CADDR(3 downto 0),

      ADDR_SUB    => CADDR(3 downto 0),
      VALUE_SUB   => CDWR(CNT_W-1 downto 0),
      OUT_SUB     => rxcnt_outsub,
      VLD_SUB     => rxcnt_vldsub,

      ADDR_ADD    => src_id,
      VALUE_ADD   => one(CNT_W-1 downto 0),
      VLD_ADD     => rxcnt_vldadd,
      FULL_ADD    => rxcnt_fulladd,

      MASK        => rxcnt_mask,
      PEND_REQ    => open
   );
   rxcnt_vldadd <= '1' when (CB.UP.SRC_RDY_N = '0' and 
                             cb_in_dst_rdy_n = '0' and
                             CB.UP.SOP_N = '1') or
                            reg_rx_even = '1' else
                   '0';
   rxcnt_vldsub <= '1' when CWR = '1' and CADDR(7 downto 4) = "0000"
                        and CBE(0) = '1' else
                   '0';

   -- This is counter of free items in each endpoint RX queue.
   -- It is incremented when message from that endpoint comes and
   -- decremented with every data word sent to that endpoint.
   ENDPOINT_DIFF_BUF : entity work.cntr_array
   generic map(
      DATA_WIDTH  => 8,
      SWAP_PORTS  => false,
      FIFO_ITEMS  => 4,
      MASK_SET    => 0,
      MASK_BITS   => 2**CNT_W - 1
   )
   port map(
      CLK         => CB_CLK,
      RESET       => CB_RESET,

      VALUE_RD    => edbuf_vrd,
      ADDR_RD     => CADDR(3 downto 0),

      ADDR_SUB    => dst_id,
      VALUE_SUB   => edbuf_valsub,
      VLD_SUB     => edbuf_vldsub,
      OUT_SUB     => edbuf_outsub,

      ADDR_ADD    => edbuf_addradd,
      VALUE_ADD   => endpoint_freed,
      VLD_ADD     => edbuf_vldadd,
      FULL_ADD    => edbuf_fulladd,

      MASK        => edbuf_mask,
      PEND_REQ    => open
   );
   edbuf_addradd <= CB.UP.DATA(15 downto 12);
   dst_id <= reg_tx_addr;
   edbuf_vldsub <= '1' when (cb_out_src_rdy_n = '0' and
                             CB.DOWN.DST_RDY_N = '0' and
                             cb_out_sop_n = '1') or
                            (tx_fsm = get_msg_len) else
                   '0';
   endpoint_freed <= CB.UP.DATA(7 downto 0);
   edbuf_vldadd <= '1' when CB.UP.SRC_RDY_N = '0' and cb_in_dst_rdy_n = '0' and
                            CB.UP.SOP_N = '0' else
                   '0';
   edbuf_valsub <= (others => '0') when tx_fsm = get_msg_len else
                   one;

   -- This is counter of freed items from each root RX buffer.
   -- It is incremented when PPC frees some items from RX queue and
   -- decremented (cleared) when Control Bus message is sent.
   -- This component has swapped ADD and SUB ports!
   ROOT_DIFF_BUF : entity work.cntr_array
   generic map(
      DATA_WIDTH  => CNT_W,
      SWAP_PORTS  => true,
      FIFO_ITEMS  => 4,
      MASK_SET    => 0,
      MASK_BITS   => 2**(CNT_W-1)
   )
   port map(
      CLK         => CB_CLK,
      RESET       => CB_RESET,

      VALUE_RD    => rdbuf_vrd,
      ADDR_RD     => rdbuf_addr_rd,

      -- This port substracts!
      ADDR_ADD    => rdbuf_addr_sub,
      VALUE_ADD   => rdbuf_value_sub,
      VLD_ADD     => rdbuf_vld_sub,
      FULL_ADD    => rdbuf_fullsub,

      -- This port adds!
      ADDR_SUB    => CADDR(3 downto 0),
      VALUE_SUB   => CDWR(CNT_W-1 downto 0),
      VLD_SUB     => rdbuf_vld_add,
      OUT_SUB     => rdbuf_out_sub,

      MASK        => rdbuf_mask,
      PEND_REQ    => rdbuf_pend
   );
   rdbuf_addr_rd <= CADDR(3 downto 0) when CRD = '1' else
                    reg_tx_addr;
   rdbuf_vld_sub <= '1' when (tx_fsm = send_header or tx_fsm = send_empty) and 
                             CB.DOWN.DST_RDY_N = '0' and
                             cb_out_src_rdy_n = '0' else
                    '0';
   rdbuf_addr_sub <= reg_tx_addr;
   rdbuf_value_sub <= rdbuf_vrd;
   rdbuf_vld_add <= '1' when CWR = '1' and CADDR(7 downto 4) = "0000" and
                             CBE(0) = '1' else
                    '0';

   -- This is counter of items in each TX queue. It is incremented
   -- when PPC writes value into it (that means it has prepared message
   -- into TX queue) and decremented with each data word sent to Control Bus
   -- This component has swapped ADD and SUB ports!
   TX_COUNTER : entity work.cntr_array
   generic map(
      DATA_WIDTH  => CNT_W,
      SWAP_PORTS  => true,
      FIFO_ITEMS  => 4,
      MASK_SET    => 0,
      MASK_BITS   => 2**CNT_W - 1
   )
   port map(
      CLK         => CB_CLK,
      RESET       => CB_RESET,

      VALUE_RD    => txcnt_vrd,
      ADDR_RD     => CADDR(3 downto 0),

      -- This ports substracts!
      ADDR_ADD    => reg_tx_addr,
      VALUE_ADD   => txcnt_valsub,
      VLD_ADD     => txcnt_vldsub,
      FULL_ADD    => txcnt_fullsub,

      -- This port adds!
      ADDR_SUB    => CADDR(3 downto 0),
      VALUE_SUB   => CDWR(CNT_W-1 downto 0),
      VLD_SUB     => txcnt_vldadd,
      OUT_SUB     => txcnt_outadd,

      MASK        => txcnt_mask,
      PEND_REQ    => txcnt_pend
   );
   txcnt_vldadd <= '1' when CWR = '1' and CADDR(7 downto 4) = "0100" and
                            CBE(0) = '1' else
                   '0';
   txcnt_valsub <= cnt_msg_len(CNT_W-1 downto 0) when 
                     (cnt_msg_len(0) = '0' or tx_fsm_1 = send_header) else
                   cnt_msg_len(CNT_W-1 downto 0) + 1;
   txcnt_vldsub <= '1' when tx_fsm = sel_queue and 
                          (tx_fsm_1 = send_body or tx_fsm_1 = send_header) else
                   '0';

   -- When message from CB comes, SRC_ID field is stored in this register
   src_id_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         src_id <= "0000";
      elsif CB_CLK'event and CB_CLK = '1' then
         if CB.UP.SRC_RDY_N = '0' and cb_in_dst_rdy_n = '0' and
            CB.UP.SOP_N = '0' then
            src_id <= CB.UP.DATA(15 downto 12);
         end if;
      end if;
   end process;

   -- This register is 1 when even word is being recieved from CB
   reg_rx_even_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_rx_even <= '0';
      elsif CB_CLK'event and CB_CLK = '1' then
         if (CB.UP.SRC_RDY_N = '0' and 
             cb_in_dst_rdy_n = '0' and
             CB.UP.SOP_N = '1') or
            reg_rx_even = '1' then
            reg_rx_even <= not reg_rx_even;
         end if;
      end if;
   end process;

   -- This register is 1 when even word is being sent to CB
   reg_tx_even_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_tx_even <= '0';
      elsif CB_CLK'event and CB_CLK = '1' then
         if (CB.DOWN.DST_RDY_N = '0' and
             cb_out_src_rdy_n = '0' and
             cb_out_sop_n = '1') or
            reg_tx_even = '1' then
            reg_tx_even <= not reg_tx_even;
         end if;
      end if;
   end process;

   -- Multiplexer of data read with Q interface
   QDRD_MUX : entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 64,
      MUX_WIDTH   => 2
   )
   port map(
      DATA_IN     => qdrd_mux_in,
      SEL         => reg_qaddr,
      DATA_OUT    => qdrd_mux_out
   );
   qdrd_mux_in <= txq_doa & rxq_doa;
   
   -- QADDR bit 9 register
   reg_qaddr_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_qaddr <= "0";
      elsif CB_CLK'event and CB_CLK = '1' then
         reg_qaddr <= QADDR(QADDR_WIDTH-1 downto QADDR_WIDTH-1);
      end if;
   end process;

   -- QDRD register
   reg_qdrd_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_qdrd <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         reg_qdrd <= qdrd_mux_out;
      end if;
   end process;

   -- QDRDY register
   reg_qdrdy_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_qdrdy <= '0';
      elsif CB_CLK'event and CB_CLK = '1' then
         reg_qdrdy <= txq_doa_dv or rxq_doa_dv;
      end if;
   end process;

   CMUX1 : entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 8,
      MUX_WIDTH   => 8
   )
   port map(
      DATA_IN     => cmux1_in,
      SEL         => CADDR(6 downto 4),
      DATA_OUT    => cmux1_out
   );
   cmux1_gen1 : if QADDR_WIDTH = 11 generate
      cmux1_in <= rdbuf_vrd & 
                  txep_doa(CNT_W-1 downto 0) & 
                  txsp_dob(CNT_W-1 downto 0) & 
                  txcnt_vrd & 
                  edbuf_vrd & 
                  rxep_dob(CNT_W-1 downto 0) & 
                  rxsp_doa(CNT_W-1 downto 0) & 
                  rxcnt_vrd;
   end generate;
   cmux1_gen2 : if QADDR_WIDTH < 11 generate
      cmux1_in <= zeros(8-CNT_W-1 downto 0) & rdbuf_vrd &
                  zeros(8-CNT_W-1 downto 0) & txep_doa(CNT_W-1 downto 0) &
                  zeros(8-CNT_W-1 downto 0) & txsp_doa(CNT_W-1 downto 0) &
                  zeros(8-CNT_W-1 downto 0) & txcnt_vrd &
                  edbuf_vrd &
                  zeros(8-CNT_W-1 downto 0) & rxep_dob(CNT_W-1 downto 0) &
                  zeros(8-CNT_W-1 downto 0) & rxsp_dob(CNT_W-1 downto 0) &
                  zeros(8-CNT_W-1 downto 0) & rxcnt_vrd;
   end generate;

   -- Register output of CMUX1
   reg_cdrd_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_cdrd <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         reg_cdrd <= cmux1_out;
      end if;
   end process;

   -- Register read request from C interface
   reg_cdrdy_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_cdrdy <= '0';
      elsif CB_CLK'event and CB_CLK = '1' then
         reg_cdrdy <= CRD;
      end if;
   end process;

   -- Register MSB of CADDR to use it as SEL input of CMUX2
   reg_caddr_msb_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_caddr_msb <= "0";
      elsif CB_CLK'event and CB_CLK = '1' then
         reg_caddr_msb <= CADDR(7 downto 7);
      end if;
   end process;
   
   -- Multiplexer for CDRD output
   CMUX2 : entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 16,
      MUX_WIDTH   => 2
   )
   port map(
      DATA_IN     => cmux2_in,
      SEL         => reg_caddr_msb,
      DATA_OUT    => cmux2_out
   );
   cmux2_in <= reg_cmuxm_out & 
               "00000000" & reg_cdrd;
               

   -- Register output of CMUXM
   reg_cmuxm_out_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_cmuxm_out <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         reg_cmuxm_out <= cmuxm_out;
      end if;
   end process;
   
   with CADDR select
   cmuxm_out <= rxcnt_mask when "10000000",
                txcnt_mask when "10000001",
                cnt_qfull  when "10000011",
                X"0000"    when others;

   -- Counter of "write to full RX queue" errors
   cnt_qfull_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         cnt_qfull <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         if rxep_doa(CNT_W-1 downto 0) = rxsp_dob(CNT_W-1 downto 0) and
            rxep_doa(CNT_W) /= rxsp_dob(CNT_W) then
            cnt_qfull <= cnt_qfull - 1;
         end if;
      end if;
   end process;

   -- This unit select next TX queue
   tx_arbiter : entity work.ARBITER
   generic map(
      VECTOR_WIDTH   => 16
   )
   port map(
      CLK            => CB_CLK,
      RESET          => CB_RESET,
      VECTOR         => arbiter_vector,
      STEP           => arbiter_step,
      ADDR           => arbiter_addr,
      VLD            => arbiter_vld
   );
   arbiter_vector <= txcnt_mask and not txcnt_pend when txcnt_vldsub = '0' else
                     (others => '0');
   arbiter_step <= '1' when tx_fsm_next = sel_queue else
                   '0';
      
   -- This arbiter detects if any Root Dif Buffer Size has reached 1/2.
   -- (Used to re-send flow control information.)
   flow_arbiter : entity work.ARBITER
   generic map(
      VECTOR_WIDTH   => 16
   )
   port map(
      CLK            => CB_CLK,
      RESET          => CB_RESET,
      VECTOR         => f_arbiter_vector,
      STEP           => f_arbiter_step,
      ADDR           => f_arbiter_addr,
      VLD            => f_arbiter_vld
   );
   f_arbiter_vector <= rdbuf_mask and not rdbuf_pend;
   f_arbiter_step <= '1' when tx_fsm_next = sel_queue else
                     '0';

   -- This counter is set to "0001" by PPC and incremented with every
   -- empty message sent during initialization phase
   cnt_send_init_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         cnt_send_init <= "0000";
      elsif CB_CLK'event and CB_CLK = '1' then
         if CWR = '1' and CADDR = "10000010" and 
            CBE(0) = '1' and CDWR(0) = '1' then
            cnt_send_init <= "0001";
         elsif tx_fsm = send_init and cnt_send_init /= "0000" and
               CB.DOWN.DST_RDY_N = '0' then
            cnt_send_init <= cnt_send_init + 1;
         end if;
      end if;
   end process;

   -- This counter prevents fsm from sending one empty message several times
   cnt_send_empty_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         cnt_send_empty <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         if tx_fsm = send_empty then 
            cnt_send_empty <= "001";
         elsif cnt_send_empty /= "000" and CB.UP.DST_RDY_N = '0' then
            cnt_send_empty <= cnt_send_empty + 1;
         end if;
      end if;
   end process;

   -- This register stores result of compration between message length
   -- and endpoint buffer free space
   reg_len_ok_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_len_ok <= '0';
      elsif CB_CLK'event and CB_CLK = '1' then
         if edbuf_outsub >= txq_dob(7 downto 0) then
            reg_len_ok <= '1';
         else
            reg_len_ok <= '0';
         end if;
      end if;
   end process;
   
   -- FSM running at CB_CLK clock
   tx_fsm_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         tx_fsm_1 <= sel_queue;
         tx_fsm <= sel_queue;
      elsif CB_CLK'event and CB_CLK = '1' then
         tx_fsm_1 <= tx_fsm;
         tx_fsm <= tx_fsm_next;
      end if;
   end process;

   -- Next state logic
   tx_fsm_next_p : process(arbiter_vld, f_arbiter_vld, cnt_send_init,
                           CB.DOWN.DST_RDY_N, cnt_msg_len, cnt_send_empty,
                           reg_msg_len, tx_fsm, edbuf_outsub, reg_len_ok,
                           tx_fsm_1, txq_dob, cb_out_src_rdy_n) 
                           -- Sensitivity list!!!!
   begin
      tx_fsm_next <= tx_fsm;
      
      case (tx_fsm) is
         when sel_queue =>
            if cnt_send_init /= "0000" then
               tx_fsm_next <= send_init;
            else
               if arbiter_vld = '1' and tx_fsm_1 = sel_queue then
                  tx_fsm_next <= get_msg_len;
               elsif f_arbiter_vld = '1' and cnt_send_empty = "000" then
                  tx_fsm_next <= send_empty;
               end if;
            end if;

         when get_msg_len =>
            tx_fsm_next <= compare_msg_len;

         when compare_msg_len =>
            tx_fsm_next <= check_msg_len;
            
         when check_msg_len =>
            if reg_len_ok = '1' then
               tx_fsm_next <= send_header;
            else
               tx_fsm_next <= sel_queue;
            end if;
         
         when send_header =>
            if reg_msg_len = "00000000" then 
               tx_fsm_next <= sel_queue; --empty message (only header)
            else
               if CB.DOWN.DST_RDY_N = '0' and cb_out_src_rdy_n = '0' then
                  tx_fsm_next <= send_body;
               end if;
            end if;
         
         when send_body =>
            if cnt_msg_len = reg_msg_len and CB.DOWN.DST_RDY_N = '0' and
               cb_out_src_rdy_n = '0' then
               tx_fsm_next <= sel_queue;
            end if;
         
         when send_init =>
            if cnt_send_init = "0000" then
               tx_fsm_next <= sel_queue;
            end if;

         when send_empty =>
            if CB.DOWN.DST_RDY_N = '0' then
               tx_fsm_next <= sel_queue;
            end if;
         
      end case;
   end process;

   -- This register stores address of currently active TX queue.
   reg_tx_addr_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_tx_addr <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         if tx_fsm = sel_queue then
            if arbiter_vld = '1' then
               reg_tx_addr <= arbiter_addr;
            elsif f_arbiter_vld = '1' then
               reg_tx_addr <= f_arbiter_addr;
            end if;
         end if;
      end if;
   end process;

   -- This register stores length of current TX message
   reg_msg_len_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_msg_len <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         if tx_fsm_1 = get_msg_len then
            reg_msg_len <= txq_dob(7 downto 0);
         end if;
      end if;
   end process;

   -- This counter has information about sent words of the message
   cnt_msg_len_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         cnt_msg_len <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         if cb_out_src_rdy_n = '0' and CB.DOWN.DST_RDY_N = '0' then
            if cb_out_sop_n = '0' then
               cnt_msg_len <= conv_std_logic_vector(1, cnt_msg_len'length);
            else
               cnt_msg_len <= cnt_msg_len + 1;
            end if;
         end if;
      end if;
   end process;

   -- This register stores last Control Bus Data output and is used in case
   -- of DST_RDY_N = '1'
   reg_cbout_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_cbout <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         reg_cbout <= cbmux_out;
      end if;
   end process;

   reg_rdy_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_rdy <= '0';
      elsif CB_CLK'event and CB_CLK = '1' then
         reg_rdy <= CB.DOWN.DST_RDY_N;
      end if;
   end process;
   
   -- Multiplexer for Control Bus data output
   CBMUX : entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 16,
      MUX_WIDTH   => 4
   )
   port map(
      DATA_IN     => cbmux_in,
      SEL         => cbmux_sel,
      DATA_OUT    => cbmux_out
   );
   gen_cbmux1 : if QADDR_WIDTH = 11 generate
      cbmux_in <= reg_tx_addr   &"0000"& rdbuf_vrd &
                  reg_cbout &
                  cnt_send_init &"0000"& conv_std_logic_vector(2**CNT_W-1, 8) &
                  txq_dob;
   end generate;
   gen_cbmux2 : if QADDR_WIDTH < 11 generate
      cbmux_in <= reg_tx_addr   &"0000"& zeros(7 downto CNT_W) & rdbuf_vrd&
                  reg_cbout &
                  cnt_send_init &"0000"& conv_std_logic_vector(2**CNT_W, 8) &
                  txq_dob;
   end generate;
   cbmux_sel(0) <= '1' when (tx_fsm = send_init) or
                            (tx_fsm = send_header) or
                            (tx_fsm = send_empty) else
                   '0';
   cbmux_sel(1) <= '1' when (tx_fsm = send_empty or tx_fsm = send_header or
                             reg_rdy = '1') and not
                            (tx_fsm = send_init) else
                   '0';
   
   cb_out_src_rdy_n <= '0' when (tx_fsm = send_header or
                                 tx_fsm = send_body or
                                 tx_fsm = send_init or
                                 tx_fsm = send_empty) and
                                (txcnt_fullsub = '0' and 
                                 (not (CRD='1' and(tx_fsm = send_header or 
                                                   tx_fsm = send_empty))) and 
                                rdbuf_fullsub = '0' ) else
                       '1';

   cb_out_sop_n <= '0' when tx_fsm = send_header or
                            tx_fsm = send_init or
                            tx_fsm = send_empty else
                   '1';

   cb_out_eop_n <= '0' when (tx_fsm = send_body and cnt_msg_len = reg_msg_len) or 
                            tx_fsm = send_init or
                            tx_fsm = send_empty or 
                            (tx_fsm = send_header and tx_fsm_next = sel_queue) else
                   '1';

   CB.DOWN.SRC_RDY_N <= cb_out_src_rdy_n;
   CB.DOWN.SOP_N <= cb_out_sop_n;
   CB.DOWN.EOP_N <= cb_out_eop_n;
   CB.DOWN.DATA <= cbmux_out;

   QDRD <= reg_qdrd;
   QDRDY <= reg_qdrdy;

   CDRD <= X"0000" & cmux2_out;
   CDRDY <= reg_cdrdy;

   -- Temporary!!!
   cb_in_dst_rdy_n <= '0' when edbuf_fulladd = '0' and rxcnt_fulladd = '0' else
                      '1';
   
   CB.UP.DST_RDY_N <= cb_in_dst_rdy_n;

end architecture cb_root_arch;
