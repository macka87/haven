-- cb_endpoint_arch.vhd: Control Bus Endpoint
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
use IEEE.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
use work.cb_pkg.all; -- Control Bus package
use work.fl_pkg.all; -- FrameLink package

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture CB_ENDPOINT_ARCH of CB_ENDPOINT is

signal tx_fifo_wr    : std_logic;
signal tx_fifo_full  : std_logic;
signal tx_fifo_do    : std_logic_vector(DATA_WIDTH-1 downto 0);
signal tx_fifo_rd    : std_logic;
signal tx_fifo_empty : std_logic;

signal ups_cnt       : std_logic_vector(log2(OUT_BUF_SIZE)-1 downto 0);
   -- Counter of message length

signal cnt_fifo_wr   : std_logic;
signal cnt_fifo_full : std_logic;
signal cnt_fifo_do   : std_logic_vector(log2(OUT_BUF_SIZE)-1 downto 0);
signal reg_cnt_fifo_do:std_logic_vector(log2(OUT_BUF_SIZE)-1 downto 0);
   -- Register because of performance issues
signal cnt_fifo_rd   : std_logic;
signal cnt_fifo_empty: std_logic;
signal reg_cnt_fifo_empty:std_logic;

signal cnt_cbtx      : std_logic_vector(log2(OUT_BUF_SIZE)-1 downto 0);
   -- DOWN counter of items that remain to be sent in the current message
signal msg_len       : std_logic_vector(7 downto 0);

signal reg_put_eop   : std_logic;   -- Send EOF to CB.UP

signal reg_rx        : std_logic;
   -- This register is 1 when message body is being recieved

signal tx_cnt        : std_logic_vector(7 downto 0);  
   -- counter of free items at the cb_root (receiver of TX stream)

signal cnt_empty     : std_logic_vector(log2(EMPTY_INTERVAL)+1 downto 0);

signal cb_out_data   : std_logic_vector(DATA_WIDTH-1 downto 0);
signal cb_out_data2  : std_logic_vector(DATA_WIDTH-1 downto 0);
signal cb_out_eop_n  : std_logic;
signal cb_out_sop_n  : std_logic;
signal cb_out_src_rdy_n:std_logic;
signal reg_cb_out_data   : std_logic_vector(DATA_WIDTH-1 downto 0);
signal reg_cb_out_eop_n  : std_logic;
signal reg_cb_out_sop_n  : std_logic;
signal reg_cb_out_src_rdy_n:std_logic;
signal reg_ack       : std_logic;

signal id_match      : std_logic;
signal rx_cnt        : std_logic_vector(7 downto 0);

signal rx_fifo_di    : std_logic_vector(DATA_WIDTH downto 0);
signal rx_fifo_wr    : std_logic;
signal rx_fifo_full  : std_logic;
signal rx_fifo_do    : std_logic_vector(DATA_WIDTH downto 0);
signal rx_fifo_rd    : std_logic;
signal rx_fifo_empty : std_logic;

signal reg_dns_sop   : std_logic;

type t_cb_ep_fsm is (wait_for_init, send_init, wait_for_msg, send_head,
                     send_body, send_empty);

signal fsm           : t_cb_ep_fsm;
signal fsm_next      : t_cb_ep_fsm;

begin
   
   -- User component -> Control Bus ---------------------------------------
   tx_data_fifo : entity work.fifo
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      DISTMEM_TYPE   => 16,
      ITEMS          => OUT_BUF_SIZE,
      BLOCK_SIZE     => 0
   )
   port map(
      RESET          => CB_RESET,
      CLK            => CB_CLK,

      -- Write interface
      DATA_IN        => UPS_FL.DATA,
      WRITE_REQ      => tx_fifo_wr,
      FULL           => tx_fifo_full,
      LSTBLK         => open,

      -- Read interface
      DATA_OUT       => tx_fifo_do,
      READ_REQ       => tx_fifo_rd,
      EMPTY          => tx_fifo_empty
   );

   tx_fifo_wr <= (not UPS_FL.SRC_RDY_N) and not tx_fifo_full;
   UPS_FL.DST_RDY_N <= tx_fifo_full;
   tx_fifo_rd <= '1' when fsm = send_body and reg_cb_out_src_rdy_n = '0' and
                          CB.UP.DST_RDY_N = '0' else
                 '0';

   cnt_fifo : entity work.fifo
   generic map(
      DATA_WIDTH     => log2(OUT_BUF_SIZE),
      DISTMEM_TYPE   => 16,
      ITEMS          => OUT_BUF_MSGS,
      BLOCK_SIZE     => 0
   )
   port map(
      RESET          => CB_RESET,
      CLK            => CB_CLK,

      -- Write interface
      DATA_IN        => ups_cnt,
      WRITE_REQ      => cnt_fifo_wr,
      FULL           => cnt_fifo_full,
      LSTBLK         => open,

      -- Read interface
      DATA_OUT       => cnt_fifo_do,
      READ_REQ       => cnt_fifo_rd,
      EMPTY          => cnt_fifo_empty
   );

   cnt_fifo_wr <= (not UPS_FL.EOF_N) and 
                  (not UPS_FL.SRC_RDY_N) and
                  (not tx_fifo_full) and
                  (not cnt_fifo_full);
                  
   cnt_fifo_rd <= '1' when fsm = send_head or
                           (reg_cnt_fifo_empty = '1' and cnt_fifo_empty = '0') 
                           else
                  '0';

   -- Registering output from FIFO before comparation
   reg_cnt_fifo_do_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_cnt_fifo_do <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         if cnt_fifo_rd = '1' then
            reg_cnt_fifo_do <= cnt_fifo_do;
         end if;
      end if;
   end process;

   -- Empty signal must also be registered
   reg_cnt_fifo_empty_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_cnt_fifo_empty <= '1';
      elsif CB_CLK'event and CB_CLK = '1' then
         if cnt_fifo_rd = '1' then
            reg_cnt_fifo_empty <= cnt_fifo_empty;
         end if;
      end if;
   end process;

   -- Counter of items in the message. EOP sets it to 0, any other word 
   -- increments it. Message length is one item greater than this counter
   -- value.
   ups_cnt_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         ups_cnt <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         if UPS_FL.SRC_RDY_N = '0' and tx_fifo_full = '0' then 
            if UPS_FL.EOF_N = '0' then
               ups_cnt <= (others => '0');
            else
               ups_cnt <= ups_cnt + 1;
            end if;
         end if;
      end if;
   end process;


   -- This is DOWN counter. It keeps information about number of
   -- items that remain to be sent.
   cnt_cbtx_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         cnt_cbtx <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         if cnt_fifo_rd = '1' then
            cnt_cbtx <= reg_cnt_fifo_do;
         end if;
         if fsm = send_body and reg_cb_out_src_rdy_n = '0' and
            CB.UP.DST_RDY_N = '0' then
            cnt_cbtx <= cnt_cbtx - 1;
         end if;
      end if;
   end process;

   reg_put_eop_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_put_eop <= '0';
      elsif CB_CLK'event and CB_CLK = '1' then
         if CB.UP.DST_RDY_N = '1' and cb_out_eop_n = '0' and 
            cb_out_sop_n = '1' then
            reg_put_eop <= '1';
         elsif CB.UP.DST_RDY_N = '0' and reg_put_eop = '1' then
            reg_put_eop <= '0';
         end if;
      end if;
   end process;

   msg_len_map1 : if log2(OUT_BUF_SIZE) < 8 generate
      msg_len <= conv_std_logic_vector(0, 8-log2(OUT_BUF_SIZE)) & reg_cnt_fifo_do;
   end generate;

   msg_len_map2 : if log2(OUT_BUF_SIZE) = 8 generate
      msg_len <= reg_cnt_fifo_do;
   end generate;
   
   -- This counter keeps inforamtion about free space at the root component
   tx_cnt_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         tx_cnt <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         if CB.UP.DST_RDY_N = '0' and reg_cb_out_src_rdy_n = '0' and
            reg_cb_out_sop_n = '1' then
            -- Sending
            if rx_fifo_full = '0' and CB.DOWN.SRC_RDY_N = '0' 
            and CB.DOWN.SOP_N = '0' and id_match = '1' then
               -- Sending and header just recieved
               tx_cnt <= tx_cnt + CB.DOWN.DATA(7 downto 0) - 1;
            else
               -- Only sending
               tx_cnt <= tx_cnt - 1;
            end if;
         else
            if rx_fifo_full = '0' and CB.DOWN.SRC_RDY_N = '0'
            and CB.DOWN.SOP_N = '0' and id_match = '1' then
               -- Only header just recieved
               tx_cnt <= tx_cnt + CB.DOWN.DATA(7 downto 0);
            end if;
         end if;
      end if;
   end process;

   -- This counter is incremented with every recieved packet
   -- and cleared with every sent packet
   cnt_empty_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         cnt_empty <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         if CB.UP.DST_RDY_N = '0' and reg_cb_out_src_rdy_n = '0' and
            reg_cb_out_sop_n = '0' then
            cnt_empty <= (others => '0');
         elsif reg_rx = '1' and
            CB.DOWN.EOP_N = '0' then
            cnt_empty <= cnt_empty + 1;
         end if;
      end if;
   end process;

   -- fsm running at CB_CLK clock
   fsm_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         fsm <= wait_for_init;
      elsif CB_CLK'event and CB_CLK = '1' then
         fsm <= fsm_next;
      end if;
   end process;

   -- Next state logic
   fsm_next_p : process(CB, reg_cnt_fifo_empty, id_match, reg_cb_out_src_rdy_n,
                        reg_ack, cnt_cbtx, msg_len, tx_cnt, 
                        cnt_empty, fsm)
               -- Possibly incomplete sensitivity list !!!
   begin
      fsm_next <= fsm;

      case (fsm) is
         when wait_for_init =>
            if CB.DOWN.EOP_N = '0' and
               id_match = '1' then
               fsm_next <= send_init;
            end if;

         when send_init =>
            fsm_next <= wait_for_msg;

         when wait_for_msg =>
            if ((reg_cb_out_src_rdy_n = '0' and CB.UP.DST_RDY_N = '0') or
               reg_ack = '0') and reg_cnt_fifo_empty = '0' and
               msg_len <= tx_cnt then
               fsm_next <= send_head;
            elsif cnt_empty >= EMPTY_INTERVAL and not
             (CB.UP.DST_RDY_N = '0' and reg_cb_out_src_rdy_n = '0' and
             reg_cb_out_sop_n = '0') then
               fsm_next <= send_empty;
            end if;

         when send_head =>
            fsm_next <= send_body;

         when send_body => 
            if cnt_cbtx = 0 then
               fsm_next <= wait_for_msg;
            end if;

         when send_empty =>
            fsm_next <= wait_for_msg;

         end case;
   end process;

   -- Store 0 if last CB.UP data word was sent.
   reg_ack_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_ack <= '1';
      elsif CB_CLK'event and CB_CLK = '1' then
         if reg_cb_out_src_rdy_n = '0' then
            reg_ack <= CB.UP.DST_RDY_N;
         end if;
      end if;
   end process;

   -- Control Bus -> User component --------------------------------------
   yesbuf: if IN_BUF_SIZE /= 0 generate
      rx_fifo : entity work.fifo
      generic map(
         DATA_WIDTH     => DATA_WIDTH + 1,
         DISTMEM_TYPE   => 16,
         ITEMS          => IN_BUF_SIZE,
         BLOCK_SIZE     => 0
      )
      port map(
         RESET          => CB_RESET,
         CLK            => CB_CLK,

         -- Write interface
         DATA_IN        => rx_fifo_di,
         WRITE_REQ      => rx_fifo_wr,
         FULL           => rx_fifo_full,
         LSTBLK         => open,

         -- Read interface
         DATA_OUT       => rx_fifo_do,
         READ_REQ       => rx_fifo_rd,
         EMPTY          => rx_fifo_empty
      );
   end generate;

   nobuf: if IN_BUF_SIZE = 0 generate
      rx_fifo_full <= DNS_FL.DST_RDY_N;
      rx_fifo_do <= rx_fifo_di;
      rx_fifo_empty <= CB.DOWN.SRC_RDY_N or (not reg_rx);
   end generate;

   rx_fifo_di <= CB.DOWN.DATA & (not CB.DOWN.EOP_N);
   rx_fifo_wr <= (not CB.DOWN.SRC_RDY_N) and (not rx_fifo_full) and reg_rx;
   rx_fifo_rd <= (not DNS_FL.DST_RDY_N) and not rx_fifo_empty;

   id_match <= '1' when (CB.DOWN.SRC_RDY_N = '0') and 
                        (rx_fifo_full = '0') and 
                        (CB.DOWN.SOP_N = '0') and
                        (CB.DOWN.DATA(15 downto 12) = SOURCE_ID) else
               '0';

   -- This register is 1 when data of packet are recieved
   reg_rx_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_rx <= '0';
      elsif CB_CLK'event and CB_CLK = '1' then
         if (id_match = '1' and CB.DOWN.EOP_N = '1') or 
            (reg_rx = '1' and CB.DOWN.EOP_N = '0') then
            reg_rx <= not reg_rx;
         end if;
      end if;
   end process;

   -- This register counts items that have been read out from input buffer
   rx_cnt_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         rx_cnt <= (others => '0');
      elsif CB_CLK'event and CB_CLK = '1' then
         if (cb_out_sop_n = '0' and cb_out_src_rdy_n = '0' and 
            CB.UP.DST_RDY_N='0') then
            if (rx_fifo_rd = '1' and rx_fifo_empty = '0') then
               rx_cnt <= "00000001";
            else
               rx_cnt <= "00000000";
            end if;
         elsif (rx_fifo_rd = '1' and rx_fifo_empty = '0') then
            rx_cnt <= rx_cnt + 1;
         end if;
      end if;
   end process;

   -- Registering EOP gives us SOP
   reg_dns_sop_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_dns_sop <= '1';
      elsif CB_CLK'event and CB_CLK = '1' then
         if DNS_FL.DST_RDY_N = '0' and (not rx_fifo_empty) = '1' then
            reg_dns_sop <= rx_fifo_do(0);
         end if;
      end if;
   end process;
   
   -- CB.UP signals (before output registers)
   with fsm select
      cb_out_data <= 
         tx_fifo_do 
            when send_body,
         SOURCE_ID & "0000" & rx_cnt 
            when send_empty,
         SOURCE_ID & "0000" & rx_cnt 
            when send_head,
         SOURCE_ID&"0000"&conv_std_logic_vector(IN_BUF_SIZE, 8) 
            when send_init,
         "0000000000000000" 
            when others;

   cb_out_sop_n <= '0' when fsm = send_head or 
                            fsm = send_init or
                            fsm = send_empty else
                   '1';
   cb_out_eop_n <= '0' when fsm = send_init or fsm = send_empty or
                           (fsm = send_body and cnt_cbtx = 0) else
                   '1';
   cb_out_src_rdy_n <= '0' when fsm = send_init or 
                                fsm = send_head or
                                fsm = send_empty or
                                fsm = send_body else
                       '1';

   process(cb_out_data, reg_put_eop, tx_fifo_do)
   begin
      if reg_put_eop = '1' then
         cb_out_data2 <= tx_fifo_do;
      else
         cb_out_data2 <= cb_out_data;
      end if;
   end process;

   cb_out_p : process(CB_CLK, CB_RESET)
   begin
      if CB_RESET = '1' then
         reg_cb_out_data <= (others => '0');
         reg_cb_out_sop_n <= '1';
         reg_cb_out_eop_n <= '1';
         reg_cb_out_src_rdy_n <= '1';
      elsif CB_CLK'event and CB_CLK = '1' then
         if CB.UP.DST_RDY_N = '0' then
            reg_cb_out_data <= cb_out_data2;
            reg_cb_out_sop_n <= cb_out_sop_n;
            reg_cb_out_eop_n <= cb_out_eop_n and not reg_put_eop;
            reg_cb_out_src_rdy_n <= cb_out_src_rdy_n and not reg_put_eop;
         end if;
      end if;
   end process;
   
   -- Port map -----------------------------------------------------------

   CB.UP.DATA  <= reg_cb_out_data;
   CB.UP.SOP_N <= reg_cb_out_sop_n;
   CB.UP.EOP_N <= reg_cb_out_eop_n;
   CB.UP.SRC_RDY_N <= reg_cb_out_src_rdy_n;

   CB.DOWN.DST_RDY_N <= rx_fifo_full;

   DNS_FL.DATA <= rx_fifo_do(DATA_WIDTH downto 1);
   DNS_FL.DREM <= "0";
   DNS_FL.SOP_N <= not reg_dns_sop;
   DNS_FL.EOP_N <= not rx_fifo_do(0);
   DNS_FL.SOF_N <= not reg_dns_sop;
   DNS_FL.EOF_N <= not rx_fifo_do(0);
   DNS_FL.SRC_RDY_N <= rx_fifo_empty;

end architecture CB_ENDPOINT_ARCH;
