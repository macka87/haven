-- agregator.vhd: FrameLink Agregator architecture
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_AGREGATOR is

   -- ------------------ Constants declaration --------------------------------
   constant PACKET_MEMORY_SIZE   : integer := 2048;   -- at least MTU
   constant FL_FIFO_ITEMS        : integer := PACKET_MEMORY_SIZE / (DATA_WIDTH/8);
   constant FIFO_LENGTH_ITEMS    : integer := PACKET_MEMORY_SIZE / 64;
   constant LENGTH_WIDTH         : integer := log2(BLOCK_SIZE);
   constant CNT_LENGTH_WIDTH     : integer := LENGTH_WIDTH-log2(DATA_WIDTH/8);
   constant REM_WIDTH            : integer := log2(DATA_WIDTH/8);
   constant NULL_REM             : std_logic_vector(REM_WIDTH-1 downto 0)
                                 := (others => '0');

   -- ------------------ Signals declaration ----------------------------------
   -- registers
   signal reg_sum                : std_logic_vector(LENGTH_WIDTH downto 0);
   signal reg_sum_clr            : std_logic;
   signal reg_sum_we             : std_logic;
   signal reg_first_packet       : std_logic;
   signal reg_first_packet_we    : std_logic;
   signal reg_last_packet        : std_logic;
   signal reg_last_packet_we     : std_logic;
   signal reg_ticket             : std_logic;
   signal reg_ticket_we          : std_logic;
   signal reg_status             : std_logic_vector(31 downto 0);
   signal reg_status_di          : std_logic_vector(31 downto 0);
   signal reg_enable             : std_logic;
   signal reg_enable_we          : std_logic;
   signal reg_frame_length       : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal reg_frame_length_we    : std_logic;

   
   -- multiplexers
   signal mx_reg_sum_di          : std_logic_vector(LENGTH_WIDTH downto 0);
   signal mx_reg_sum_di_sel      : std_logic;
   signal mx_adc_do              : std_logic_vector(31 downto 0);
   
   signal mx_rx_dst_rdy_n        : std_logic;
   signal mx_tx_sof_n            : std_logic;
   signal mx_tx_sop_n            : std_logic;
   signal mx_tx_eop_n            : std_logic;
   signal mx_tx_eof_n            : std_logic;
   signal mx_tx_src_rdy_n        : std_logic;
   signal mx_tx_data             : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal mx_tx_rem              : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

   -- counters
   signal cnt_length             : std_logic_vector(CNT_LENGTH_WIDTH-1 downto 0);
   signal cnt_length_ce          : std_logic;
   signal cnt_length_clr         : std_logic;
   signal cnt_timeout            : std_logic_vector(abs(log2(TIMEOUT)-1) downto 0);
   signal cnt_timeout_max        : std_logic;
   signal cnt_timeout_clr        : std_logic;
   signal cnt_bad_packets        : std_logic_vector(31 downto 0);
   signal cnt_bad_packets_ce     : std_logic;
   signal cnt_port0_packets      : std_logic_vector(31 downto 0);
   signal cnt_port0_packets_ce   : std_logic;

   -- FIFO with packet LENGTHs signals
   signal fifo_length_full       : std_logic;
   signal fifo_length_data_out   : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal fifo_length_read_req   : std_logic;
   signal fifo_length_empty      : std_logic;

   signal fifo_length_data_in    : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal fifo_length_write_req  : std_logic;
   
   -- FL_FIFO signals
   signal fl_fifo_rx_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_fifo_rx_rem         : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal fl_fifo_rx_src_rdy_n   : std_logic;
   signal fl_fifo_rx_dst_rdy_n   : std_logic;
   signal fl_fifo_rx_sop_n       : std_logic;
   signal fl_fifo_rx_eop_n       : std_logic;
   signal fl_fifo_rx_sof_n       : std_logic;
   signal fl_fifo_rx_eof_n       : std_logic;
   signal fl_fifo_tx_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_fifo_tx_rem         : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal fl_fifo_tx_src_rdy_n   : std_logic;
   signal fl_fifo_tx_dst_rdy_n   : std_logic;
   signal fl_fifo_tx_sof_n       : std_logic;
   signal fl_fifo_tx_eof_n       : std_logic;

   -- others
   signal input_allow_n          : std_logic;
   signal input_sof              : std_logic;
   signal input_eof              : std_logic;
   signal input_valid_n          : std_logic;
   signal output_allow_n         : std_logic;
   signal output_valid_n         : std_logic;
   signal output_sof             : std_logic;
   signal output_eof             : std_logic;
   signal output_timeout         : std_logic;
   signal adder_sum              : std_logic_vector(LENGTH_WIDTH downto 0);
   signal result_allow           : std_logic;
   signal result_deny            : std_logic;
   
   signal fifo_length_dv         : std_logic;
   signal write_ticket           : std_logic;
   signal write_last_ticket      : std_logic;
   
   signal agreg_rx_dst_rdy_n     : std_logic;
   signal agreg_tx_sof_n         : std_logic;
   signal agreg_tx_sop_n         : std_logic;
   signal agreg_tx_eop_n         : std_logic;
   signal agreg_tx_eof_n         : std_logic;
   signal agreg_tx_src_rdy_n     : std_logic;
   signal agreg_tx_dst_rdy_n     : std_logic;
   signal agreg_tx_data          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal agreg_tx_rem           : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal packet_length          : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   
   signal cmp_sum_greater        : std_logic;
   signal cmp_bad_length         : std_logic;
   signal cmp_port0              : std_logic;

begin
   -- ------------------ Directly mapped signals ------------------------------
   input_allow_n        <= fifo_length_full and (not RX_EOF_N);
   input_valid_n        <= fl_fifo_rx_src_rdy_n or fl_fifo_rx_dst_rdy_n;
   input_sof            <= not (fl_fifo_rx_sof_n or input_valid_n);
   input_eof            <= not (fl_fifo_rx_eof_n or input_valid_n);
   output_valid_n       <= fl_fifo_tx_src_rdy_n or fl_fifo_tx_dst_rdy_n 
                           or output_allow_n;
   output_eof           <= not (output_valid_n or fl_fifo_tx_eof_n);
   output_sof           <= not (output_valid_n or fl_fifo_tx_sof_n);
   output_allow_n       <= (not (fl_fifo_tx_sof_n or reg_ticket)) or 
                           (not (fl_fifo_tx_eof_n or reg_last_packet or reg_ticket));
   output_timeout       <= cnt_timeout_max;
   
   fifo_length_dv       <= not fifo_length_empty;

   adder_sum            <= reg_sum + ('0' & fifo_length_data_out);

   result_allow         <= fifo_length_dv and not cmp_sum_greater;
   result_deny          <= fifo_length_dv and cmp_sum_greater;

   write_ticket         <= fifo_length_dv and not (reg_ticket or reg_last_packet) 
                           and result_allow and (not output_timeout);
   write_last_ticket    <= fifo_length_dv and not (reg_ticket or reg_last_packet) 
                           and result_deny and (not output_timeout);

   packet_length        <= ((cnt_length-1) & RX_REM)+1;

   -- control signals
   reg_sum_clr          <= output_timeout and not reg_last_packet;
   reg_sum_we           <= write_ticket or write_last_ticket;
   reg_last_packet_we   <= write_last_ticket or output_timeout or output_eof;
   reg_first_packet_we  <= (reg_last_packet and output_eof) or output_sof;
   reg_ticket_we        <= output_sof or write_last_ticket or (fifo_length_dv and not reg_ticket);
   reg_frame_length_we  <= input_sof;
   
   cnt_length_ce        <= not (input_valid_n or input_allow_n);
   cnt_length_clr       <= input_eof;
   cnt_timeout_clr      <= cnt_timeout_max or reg_first_packet;
   cnt_bad_packets_ce   <= fifo_length_write_req and cmp_bad_length;
   cnt_port0_packets_ce <= input_sof and cmp_port0;

   mx_reg_sum_di_sel    <= write_last_ticket;
   
   -- status register data in
   reg_status_di(3 downto 0) <= fifo_length_empty & fifo_length_full 
                                & input_allow_n & output_allow_n;
   reg_status_di(7 downto 4) <= '0' & reg_last_packet & reg_first_packet 
                                & reg_ticket;
   reg_status_di(31 downto 8)<= (others => '0');

   -- FL_FIFO inputs
   fl_fifo_rx_data      <= RX_DATA;
   fl_fifo_rx_rem       <= RX_REM;
   -- stop when FIFO_LENGTH or packet FIFO is full:
   fl_fifo_rx_src_rdy_n <= RX_SRC_RDY_N or input_allow_n or (not reg_enable);
   fl_fifo_rx_sop_n     <= RX_SOP_N;
   fl_fifo_rx_eop_n     <= RX_EOP_N;
   fl_fifo_rx_sof_n     <= RX_SOF_N;
   fl_fifo_rx_eof_n     <= RX_EOF_N;
   
   -- FrameLink output ports
   RX_DST_RDY_N         <= mx_rx_dst_rdy_n;

   TX_SOF_N             <= mx_tx_sof_n;
   TX_SOP_N             <= mx_tx_sop_n;
   TX_EOP_N             <= mx_tx_eop_n;
   TX_EOF_N             <= mx_tx_eof_n;
   TX_SRC_RDY_N         <= mx_tx_src_rdy_n;
   TX_DATA              <= mx_tx_data;
   TX_REM               <= mx_tx_rem;  -- output segments are aligned
   
   -- ADC output signals
   ADC_DO               <= mx_adc_do;
   ADC_DRDY             <= ADC_RD;

   -- agregator output ports
   agreg_rx_dst_rdy_n   <= fl_fifo_rx_dst_rdy_n or input_allow_n;

   agreg_TX_SOF_N       <= fl_fifo_tx_sof_n or (not reg_first_packet);
   agreg_TX_SOP_N       <= fl_fifo_tx_sof_n or (not reg_first_packet);
   agreg_TX_EOP_N       <= fl_fifo_tx_eof_n or (not reg_last_packet);
   agreg_TX_EOF_N       <= fl_fifo_tx_eof_n or (not reg_last_packet);
   agreg_TX_SRC_RDY_N   <= fl_fifo_tx_src_rdy_n or output_allow_n;
   agreg_tx_dst_rdy_n   <= TX_DST_RDY_N or output_allow_n or (not reg_enable);
   fl_fifo_tx_dst_rdy_n <= agreg_tx_dst_rdy_n;
   agreg_TX_DATA        <= fl_fifo_tx_data;
   agreg_TX_REM         <= (others => '1');  -- output segments are aligned

   -- FIFO inputs
   fifo_length_data_in  <= cnt_length & NULL_REM;
   fifo_length_write_req <= input_eof;
   fifo_length_read_req <= write_ticket or write_last_ticket;
   
   -- comparator cmp_bad_length
   cmp_bad_lengthp : process (packet_length, reg_frame_length)
   begin
      if (packet_length = reg_frame_length) then
         cmp_bad_length <= '0';
      else
         cmp_bad_length <= '1';
      end if;
   end process;

   -- comparator cmp_sum_greater
   cmp_sum_greaterp : process (adder_sum)
   begin
      if (adder_sum > conv_std_logic_vector(BLOCK_SIZE, adder_sum'length)) then
         cmp_sum_greater <= '1';
      else
         cmp_sum_greater <= '0';
      end if;
   end process;

   -- comparator cmp_port0
   cmp_port0p : process (RX_DATA)
   begin
      if (RX_DATA(35 downto 32) = X"1") then
         cmp_port0 <= '1';
      else
         cmp_port0 <= '0';
      end if;
   end process;

   -- multiplex reg_sum input
   mx_reg_sum_dip : process (mx_reg_sum_di_sel,adder_sum,fifo_length_data_out)
   begin
      case mx_reg_sum_di_sel is
         when '0' => mx_reg_sum_di <= adder_sum;
         when '1' => mx_reg_sum_di <= '0' & fifo_length_data_out;
         when others => mx_reg_sum_di <= adder_sum;
      end case;
   end process;

   -- multiplex ADC data output
   mx_adc_dop : process (ADC_ADDR, reg_status, reg_enable, cnt_bad_packets, cnt_port0_packets)
   begin
      case ADC_ADDR(3 downto 2) is
         when "00" => mx_adc_do <= reg_status;
         when "01" => mx_adc_do <= X"0000000" & "000" & reg_enable;
         when "10" => mx_adc_do <= cnt_bad_packets;
         when "11" => mx_adc_do <= cnt_port0_packets;
         when others => mx_adc_do <= (others => '0');
      end case;
   end process;

   -- AGREGATTOR BYPASS multiplexers ------------------------------------------

   -- multiplex RX_DST_RDY_N
   mx_rx_dst_rdy_np: process(reg_enable, TX_DST_RDY_N, agreg_rx_dst_rdy_n)
   begin
      case reg_enable is
         when '0' => mx_rx_dst_rdy_n <= TX_DST_RDY_N;
         when '1' => mx_rx_dst_rdy_n <= agreg_rx_dst_rdy_n;
         when others => mx_rx_dst_rdy_n <= '1';
      end case;
   end process;

   -- multiplex TX_SOF_N
   mx_tx_sof_np: process(reg_enable, RX_SOF_N, agreg_tx_sof_n)
   begin
      case reg_enable is
         when '0' => mx_tx_sof_n <= RX_SOF_N;
         when '1' => mx_tx_sof_n <= agreg_tx_sof_n;
         when others => mx_tx_sof_n <= '1';
      end case;
   end process;
   
   -- multiplex TX_SOP_N
   mx_tx_sop_np: process(reg_enable, RX_SOP_N, agreg_tx_sop_n)
   begin
      case reg_enable is
         when '0' => mx_tx_sop_n <= RX_SOP_N;
         when '1' => mx_tx_sop_n <= agreg_tx_sop_n;
         when others => mx_tx_sop_n <= '1';
      end case;
   end process;

   -- multiplex TX_EOP_N
   mx_tx_eop_np: process(reg_enable, RX_EOP_N, agreg_tx_eop_n)
   begin
      case reg_enable is
         when '0' => mx_tx_eop_n <= RX_EOP_N;
         when '1' => mx_tx_eop_n <= agreg_tx_eop_n;
         when others => mx_tx_eop_n <= '1';
      end case;
   end process;

   -- multiplex TX_EOF_N
   mx_tx_eof_np: process(reg_enable, RX_EOF_N, agreg_tx_eof_n)
   begin
      case reg_enable is
         when '0' => mx_tx_eof_n <= RX_EOF_N;
         when '1' => mx_tx_eof_n <= agreg_tx_eof_n;
         when others => mx_tx_eof_n <= '1';
      end case;
   end process;

   -- multiplex TX_SRC_RDY_N
   mx_tx_src_rdy_np: process(reg_enable, RX_SRC_RDY_N, agreg_tx_src_rdy_n)
   begin
      case reg_enable is
         when '0' => mx_tx_src_rdy_n <= RX_SRC_RDY_N;
         when '1' => mx_tx_src_rdy_n <= agreg_tx_src_rdy_n;
         when others => mx_tx_src_rdy_n <= '1';
      end case;
   end process;

   -- multiplex TX_DATA
   mx_tx_datap: process(reg_enable, RX_DATA, agreg_tx_data)
   begin
      case reg_enable is
         when '0' => mx_tx_data <= RX_DATA;
         when '1' => mx_tx_data <= agreg_tx_data;
         when others => mx_tx_data <= (others => '0');
      end case;
   end process;
   
   -- multiplex TX_REM
   mx_tx_remp: process(reg_enable, RX_REM, agreg_tx_rem)
   begin
      case reg_enable is
         when '0' => mx_tx_rem <= RX_REM;
         when '1' => mx_tx_rem <= agreg_tx_rem;
         when others => mx_tx_rem <= (others => '0');
      end case;
   end process;

   -- -------------------------------------------------------------------------

   -- register reg_last_packet
   reg_last_packetp:process (CLK)
   begin
      if CLK'event and CLK='1' then  
         if RESET='1' then   
            reg_last_packet <= '0';
         elsif (reg_last_packet_we = '1') then
            reg_last_packet <= write_last_ticket or output_timeout;
         end if;
      end if;
   end process;

   -- register reg_first_packet
   reg_first_packetp:process (CLK)
   begin
      if CLK'event and CLK='1' then  
         if RESET='1' then   
            reg_first_packet <= '1';
         elsif (reg_first_packet_we = '1') then
            reg_first_packet <= reg_last_packet and output_eof;
         end if;
      end if;
   end process;

   -- register reg_ticket - permit ticket for outgoing packets
   reg_ticketp:process (CLK)
   begin
      if CLK'event and CLK='1' then  
         if RESET='1' then   
            reg_ticket <= '0';
         elsif (reg_ticket_we = '1') then
            reg_ticket <= write_ticket or write_last_ticket;
         end if;
      end if;
   end process;

   -- register reg_sum - total bytes sent in current block
   reg_sump:process (CLK)
   begin
      if CLK'event and CLK='1' then  
         if RESET='1' or reg_sum_clr='1' then   
            reg_sum <= (others => '0');
         elsif (reg_sum_we = '1') then
            reg_sum <= mx_reg_sum_di;
         end if;
      end if;
   end process;

   -- register reg_enable - enable FL_AGREGATOR
   reg_enablep:process (CLK)
   begin
      if CLK'event and CLK='1' then  
         if RESET='1' then   
            reg_enable <= '0';
         else
            reg_enable <= ENABLE;
         end if;
      end if;
   end process;

   -- register reg_status - Agregator status word
   reg_statusp:process (CLK)
   begin
      if CLK'event and CLK='1' then  
         reg_status <= reg_status_di;
      end if;
   end process;

   -- register reg_frame_length
   reg_frame_lengthp:process (CLK)
   begin
      if CLK'event and CLK='1' then  
         if RESET='1' then   
            reg_frame_length <= (others => '0');
         elsif (reg_frame_length_we = '1') then
            reg_frame_length <= RX_DATA(LENGTH_WIDTH-1 downto 0);
         end if;
      end if;
   end process;

   -- counter cnt_length 
   cnt_lengthp: process (CLK) 
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' or cnt_length_clr = '1' then
            cnt_length <= conv_std_logic_vector(1, CNT_LENGTH_WIDTH);
         elsif cnt_length_ce = '1' then
            cnt_length <= cnt_length + 1;
         end if;
      end if;
   end process;

   -- counter cnt_bad_packets 
   cnt_bad_packetsp: process (CLK) 
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' then
            cnt_bad_packets <= (others => '0');
         elsif cnt_bad_packets_ce = '1' then
            cnt_bad_packets <= cnt_bad_packets + 1;
         end if;
      end if;
   end process;

   -- counter cnt_port0_packets 
   cnt_port0_packetsp: process (CLK) 
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' then
            cnt_port0_packets <= (others => '0');
         elsif cnt_port0_packets_ce = '1' then
            cnt_port0_packets <= cnt_port0_packets + 1;
         end if;
      end if;
   end process;
   
   -- generate TIMEOUT logic --------------------------------------------------
   GEN_CNT_TIMEOUT : if TIMEOUT > 0 generate
      -- counter cnt_timeout 
      cnt_timeoutp: process (CLK) 
      begin
         if CLK='1' and CLK'event then
            if RESET = '1' or cnt_timeout_clr = '1' then
               cnt_timeout <= (others => '0');
            else
               cnt_timeout <= cnt_timeout + 1;
            end if;
         end if;
      end process;

      -- compare if counter has hit the timeout value
      cnt_timeout_maxp: process(CLK)
      begin
         if (CLK'event and CLK ='1') then   
            if (cnt_timeout = conv_std_logic_vector(TIMEOUT-1,log2(TIMEOUT))) then 
               cnt_timeout_max <= '1';
            else 
               cnt_timeout_max <= '0';
            end if;
         end if; 
      end process; 
   end generate;

   GEN_NO_TIMEOUT : if TIMEOUT = 0 generate
      cnt_timeout_max <= '0';
   end generate;

   -- ------------------ Components -------------------------------------------
   -- FIFO for storing lengths of packets in FL_FIFO
   FIFO_LENGTH_I : entity work.FIFO
      generic map(
         -- Set data width here
         DATA_WIDTH     => LENGTH_WIDTH,
         -- Distributed RAM type, only 16, 32, 64 bits
         DISTMEM_TYPE   => 16,
         -- Set number of items in FIFO here
         ITEMS          => FIFO_LENGTH_ITEMS,
         -- for last block identification
         BLOCK_SIZE     => 0
      )
      port map(
         RESET       => RESET,
         CLK         => CLK,
         -- Write interface
         DATA_IN     => fifo_length_data_in,
         WRITE_REQ   => fifo_length_write_req,
         FULL        => fifo_length_full,
         LSTBLK      => open,
         -- Read interface
         DATA_OUT    => fifo_length_data_out,
         READ_REQ    => fifo_length_read_req,
         EMPTY       => fifo_length_empty
      );

   -- FL_FIFO for storing packets
   FL_FIFO_I : entity work.FL_FIFO
      generic map(
         DATA_WIDTH     => DATA_WIDTH,
         USE_BRAMS      => true,
         ITEMS          => FL_FIFO_ITEMS,
         BLOCK_SIZE     => 0,
         STATUS_WIDTH   => 1,
         PARTS          => FRAME_PARTS
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- write interface
         RX_DATA        => fl_fifo_rx_data,
         RX_REM         => fl_fifo_rx_rem,
         RX_SRC_RDY_N   => fl_fifo_rx_src_rdy_n,
         RX_DST_RDY_N   => fl_fifo_rx_dst_rdy_n,
         RX_SOP_N       => fl_fifo_rx_sop_n,
         RX_EOP_N       => fl_fifo_rx_eop_n,
         RX_SOF_N       => fl_fifo_rx_sof_n,
         RX_EOF_N       => fl_fifo_rx_eof_n,
         -- read interface
         TX_DATA        => fl_fifo_tx_data,
         TX_REM         => fl_fifo_tx_rem,
         TX_SRC_RDY_N   => fl_fifo_tx_src_rdy_n,
         TX_DST_RDY_N   => fl_fifo_tx_dst_rdy_n,
         TX_SOP_N       => open,
         TX_EOP_N       => open,
         TX_SOF_N       => fl_fifo_tx_sof_n,
         TX_EOF_N       => fl_fifo_tx_eof_n,
         -- FIFO state signals
         LSTBLK         => open,
         FULL           => open,
         EMPTY          => open,
         STATUS         => open
      );

end architecture full;
