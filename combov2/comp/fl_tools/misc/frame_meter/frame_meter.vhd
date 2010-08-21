-- frame_meter.vhd: FrameLink frame meter architecture
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
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
architecture full of FL_FRAME_METER is

   -- ------------------ Constants declaration --------------------------------
   
   -- at least MTU
   constant PACKET_MEMORY_SIZE   : integer := 2048;   
   constant FL_FIFO_ITEMS        : integer := PACKET_MEMORY_SIZE / (DATA_WIDTH/8);
   constant FIFO_LENGTH_ITEMS    : integer := PACKET_MEMORY_SIZE / 64;
   
   -- counted length signal size
   constant CNT_SIZE             : integer := 16;
   
   -- minimum size for storing idle cycles (8 < DATA_WIDTH < 64) in fifo
   -- Example:
   -- DATA_WIDTH        REM         IDLE_WIDTH      MAXIMAL_IDLES
   -- 64                3           0              N/A
   -- 32                2           1              1
   -- 16                1           2              3
   -- 8                 N/A         N/A            N/A

   constant IDLE_WIDTH           : integer := 3 - log2(DATA_WIDTH/8);
   constant ONES_REM             : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0)
                                 := (others => '1');
                                 
   -- ------------------ Signals declaration ----------------------------------

   -- input registers
   signal reg_header_len         : std_logic_vector(CNT_SIZE-1 downto 0);
   signal reg_header_len_we      : std_logic;

   -- input counters
   signal cnt_header             : std_logic_vector(CNT_SIZE-1 downto 0);
   signal cnt_header_ce          : std_logic;
   signal cnt_header_clr         : std_logic;
   signal cnt_payload            : std_logic_vector(CNT_SIZE-1 downto 0);
   signal cnt_payload_ce         : std_logic;
   signal cnt_payload_clr        : std_logic;
   
   -- fsm signals
   signal fsm_eof_valid_n        : std_logic;
   signal fsm_eop_valid_n        : std_logic;
   signal fsm_fifo_empty         : std_logic;
   signal fsm_next_data          : std_logic;
   signal fsm_wait_state         : std_logic;
   signal fsm_send_length        : std_logic;
   signal fsm_send_header        : std_logic;
   signal fsm_send_idle          : std_logic;
   signal fsm_send_data          : std_logic;
   signal fsm_is_idle            : std_logic;
   
   -- fifo signals
   signal fifo_data_in           : std_logic_vector((2*CNT_SIZE+IDLE_WIDTH)-1 downto 0);
   signal fifo_write_req         : std_logic;
   signal fifo_data_out          : std_logic_vector((2*CNT_SIZE+IDLE_WIDTH)-1 downto 0);
   signal fifo_read_req          : std_logic;
   signal fifo_full              : std_logic;
   signal fifo_empty             : std_logic;

   -- fl_fifo signals
   signal fl_fifo_tx_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_fifo_tx_rem         : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_fifo_tx_src_rdy_n   : std_logic;
   signal fl_fifo_tx_dst_rdy_n   : std_logic;
   signal fl_fifo_rx_dst_rdy_n   : std_logic;
   signal fl_fifo_tx_sop_n       : std_logic;
   signal fl_fifo_tx_eop_n       : std_logic;
   signal fl_fifo_tx_sof_n       : std_logic;
   signal fl_fifo_tx_eof_n       : std_logic;

   -- fl_dec signals
   signal fl_dec_hdr_frame       : std_logic; 
   signal fl_dec_pld_frame       : std_logic;
   signal fl_dec_eof             : std_logic;
   signal fl_dec_src_rdy         : std_logic;
   signal fl_dec_dst_rdy         : std_logic;

   -- input logic signals
   signal input_allow_n          : std_logic;
   signal input_allow            : std_logic;
   signal input_valid            : std_logic;
   signal input_eof              : std_logic;
   
   -- header lenght align to 8 bytes
   signal header_len_8B          : std_logic_vector(CNT_SIZE-1 downto 0);
   
   -- idle cycles storing
   signal idle_bytes             : std_logic_vector(log2(DATA_WIDTH/8)+2 downto 0);
   
   -- idle cycles storing, truncated to minimal width
   signal idle_bytes_trunc       : std_logic_vector(IDLE_WIDTH-1 downto 0);
   
   -- header len truncated to minimal width
   signal h_len_trunc            : std_logic_vector(log2(DATA_WIDTH/8)+2 downto 0);
   
   -- header len aligned to 8 bytes, truncated to minimal width
   signal h_len_8B_trunc         : std_logic_vector(log2(DATA_WIDTH/8)+2 downto 0);

   -- computed payload len
   signal payload_len            : std_logic_vector(CNT_SIZE-1 downto 0);

   -- output indcation need for idle cycles (data_width = 32)
   signal reg_is_idle            : std_logic;
   signal reg_is_idle_we         : std_logic;
   signal reg_is_idle_clr        : std_logic;
   
   -- output data selector
   signal mxs_sel                : std_logic;
   
   -- output indcation needs for idle cycles (data_width != 32)
   signal is_idle                : std_logic;
   
   -- output idle cycles counter (data_width != 32)
   signal cnt_idle_cycles        : std_logic_vector(IDLE_WIDTH-1 downto 0);
   signal cnt_idle_cycles_ld     : std_logic; -- load
   signal cnt_idle_cycles_ce     : std_logic; 
   
   -- how many time needs to be length multiplexed to output
   -- maximal counter width of output length mux selector is IDLE_WIDTH - 1
   signal cnt_length_part        : std_logic_vector(abs(IDLE_WIDTH-2) downto 0);
   signal cnt_length_part_clr    : std_logic;
   signal cnt_length_part_ce     : std_logic;
   
   -- indicate first part of transmited length (data_width != 32)
   signal first_part             : std_logic;

   -- indicate last part of transmited length (data_width != 32)
   signal last_part              : std_logic;
   
   -- multiplexor input, for multiplex counted length
   signal mx_data_in             : std_logic_vector(2*CNT_SIZE-1 downto 0);
   
   -- multiplexor output, for multiplex counted length
   signal mx_data_out            : std_logic_vector(DATA_WIDTH-1 downto 0);
   
   
begin

   input_allow_n     <= fifo_full and fl_dec_eof;
   input_allow       <= not input_allow_n;
   input_valid       <= fl_dec_src_rdy and fl_dec_dst_rdy;
   input_eof         <= fl_dec_eof and input_valid;
   fl_dec_dst_rdy    <= not (fl_fifo_rx_dst_rdy_n or input_allow_n);

   -- final size computed as header len aligned to 8 bytes + payload len,
   -- last few added bits are idle cycles
   fifo_data_in      <=  reg_header_len & (header_len_8B + payload_len)
                         & idle_bytes_trunc;

   fifo_write_req    <= input_eof;

   cnt_header_ce     <= input_valid and input_allow and fl_dec_hdr_frame;
   cnt_header_clr    <= input_eof;
   
   cnt_payload_ce    <= input_valid and input_allow and fl_dec_pld_frame;
   cnt_payload_clr   <= input_eof;

   reg_header_len_we <= (not RX_EOP_N) and cnt_header_ce;

   -- computed payload len, shifted by REM, with added one
   -- it is true number of bytes of actual data_width
   payload_len       <= (cnt_payload(CNT_SIZE-(log2(DATA_WIDTH/8))-1 downto 0)
                                 & RX_REM) + 1;
                                 
   -- counting header len aligned to 8 bytes
   header_len_8B     <= (reg_header_len(CNT_SIZE-1 downto 3) +
                        (reg_header_len(0) or
                           reg_header_len(1) or
                              reg_header_len(2)) ) & "000";

   -- truncation to minimal width
   h_len_8B_trunc    <= header_len_8B(log2(DATA_WIDTH/8)+2 downto 0);
   h_len_trunc       <= reg_header_len(log2(DATA_WIDTH/8)+2 downto 0);
   
   -- counting idle cycles
   idle_bytes        <= h_len_8B_trunc - h_len_trunc;
   
   -- truncation with rem_width (maximum is 3)
   idle_bytes_trunc  <= idle_bytes(2 downto log2(DATA_WIDTH/8));


   -- ------------------ Size counters ----------------------------------------
   
   -- input counter cnt_header
   cnt_header_i: process (CLK) 
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' or cnt_header_clr = '1' then
            cnt_header <= conv_std_logic_vector(0, CNT_SIZE);
         elsif cnt_header_ce = '1' then
            cnt_header <= cnt_header + 1;
         end if;
      end if;
   end process;
   
   -- input counter cnt_payload
   cnt_payload_i: process (CLK)
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' or cnt_payload_clr = '1' then
            cnt_payload <= conv_std_logic_vector(0, CNT_SIZE);
         elsif cnt_payload_ce = '1' then
            cnt_payload <= cnt_payload + 1;
         end if;
      end if;
   end process;

   -- ------------------ Registers --------------------------------------------

   -- input register reg_header_len
   reg_header_len_i: process (CLK)
   begin
      if CLK'event and CLK='1' then
         if RESET='1' then
            reg_header_len <= conv_std_logic_vector(0, CNT_SIZE);
         elsif (reg_header_len_we = '1') then
            reg_header_len <= (cnt_header(CNT_SIZE-(log2(DATA_WIDTH/8))-1 downto 0)
                                 & RX_REM) + 1;
         end if;
      end if;
   end process;

   -- ------------------ Generate output logic --------------------------------
   
   fsm_fifo_empty    <= fifo_empty;

   OUTPUT_LOGIC_I: if DATA_WIDTH = 32 generate
   
   fsm_next_data     <= (not TX_DST_RDY_N) and fsm_send_length;
   fsm_is_idle       <= reg_is_idle;
   reg_is_idle_clr   <= (not TX_DST_RDY_N)
                           and fsm_send_header and (not fl_fifo_tx_eop_n);
   reg_is_idle_we    <= fsm_next_data;

   -- ------------------ Registers --------------------------------------------

   -- output register reg_is_idle
   reg_is_idle_i: process (CLK)
   begin
      if CLK'event and CLK='1' then
         if RESET='1' or reg_is_idle_clr = '1' then
            reg_is_idle <= '0';
         elsif (reg_is_idle_we = '1') then
            reg_is_idle <= fifo_data_out(0);
         end if;
      end if;
   end process;
   
   -- ------------------ Multiplexors -----------------------------------------
   
   -- multiplex TX_DATA
   mx_tx_data_i: process(mxs_sel, fifo_data_out, fl_fifo_tx_data)
   begin
      case mxs_sel is
         -- data without idle cycles stored on last bits in fifo
         when '1' => TX_DATA <= fifo_data_out(2*CNT_SIZE+IDLE_WIDTH-1 downto IDLE_WIDTH);
         when '0' => TX_DATA <= fl_fifo_tx_data;
         when others => TX_DATA <= fl_fifo_tx_data;
      end case;
   end process;
   
   -- set output flow link signals
   
   TX_SOF_N <= not fsm_send_length;
   TX_SOP_N <= not (fsm_send_length or
                  (fsm_send_data and (not fl_fifo_tx_sop_n)));
   TX_EOP_N <= not (fsm_send_idle   -- only possible on 32 bits!
                  -- last header data without idle
                  or ((not reg_is_idle) and fsm_send_header and (not fl_fifo_tx_eop_n)) 
                  -- last data
                  or ((not fl_fifo_tx_eop_n) and fsm_send_data));
                  
   end generate;
   
   OUTPUT_LOGIC_II: if DATA_WIDTH < 32 generate

   fsm_next_data        <= (not TX_DST_RDY_N ) and last_part;
   fsm_is_idle          <= is_idle;
   
   cnt_idle_cycles_ld   <= first_part and fsm_send_length;
   cnt_idle_cycles_ce   <= (((not TX_DST_RDY_N) and is_idle and fsm_send_idle) -- idle mode
                              -- start sending idles
                              or ((not TX_DST_RDY_N) and (not fl_fifo_tx_eop_n) and fsm_send_header) );
   
   cnt_length_part_clr  <= fsm_wait_state and fsm_send_data;
   cnt_length_part_ce   <= (not TX_DST_RDY_N ) and fsm_send_length;
   
   mx_data_in           <= fifo_data_out(2*CNT_SIZE+IDLE_WIDTH-1 downto IDLE_WIDTH);

   -- ------------------ Counters --------------------------------------------

   -- output down counter for cnt_idle_cycles
   cnt_idle_cycles_i: process (CLK)
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' then
            cnt_idle_cycles <= conv_std_logic_vector(0, IDLE_WIDTH);
         elsif cnt_idle_cycles_ld = '1' then
            cnt_idle_cycles <= fifo_data_out(IDLE_WIDTH-1 downto 0);
         elsif cnt_idle_cycles_ce = '1' then
            cnt_idle_cycles <= cnt_idle_cycles - 1;
         end if;
      end if;
   end process;
   
   -- output counter for multiplex actual transmited length part
   cnt_length_part_i: process (CLK)
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' or cnt_length_part_clr = '1' then
            cnt_length_part <= conv_std_logic_vector(0, IDLE_WIDTH-1);
         elsif cnt_length_part_ce = '1' then
            cnt_length_part <= cnt_length_part + 1;
         end if;
      end if;
   end process;
   
   -- ------------------ Comparators ------------------------------------------
   
   -- comparator cmp_is_idle
   cmp_idle_cycles : process (cnt_idle_cycles)
   begin
      if (cnt_idle_cycles = conv_std_logic_vector(0, cnt_idle_cycles'length)) then
         is_idle <= '0';
      else
         is_idle <= '1';
      end if;
   end process;
   
   -- comparator first_part
   cmp_first_part : process (cnt_length_part)
   begin
      if (cnt_length_part = conv_std_logic_vector(0, cnt_length_part'length)) then
         first_part <= '1';
      else
         first_part <= '0';
      end if;
   end process;
   
   -- comparator last_part
   cmp_last_part : process (cnt_length_part)
   begin
      if (cnt_length_part = conv_std_logic_vector(1, cnt_length_part'length)) then
         last_part <= '1';
      else
         last_part <= '0';
      end if;
   end process;

   -- ------------------ Other components -------------------------------------

   -- connect generic multiplexor for multiplex 32 bit length width
   -- to output, fragmented in time
   MUX_I : entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => DATA_WIDTH,
         MUX_WIDTH   => 32/DATA_WIDTH
      )
      port map(
         DATA_IN  => mx_data_in,
         SEL      => cnt_length_part,
         DATA_OUT => mx_data_out
      );
   
   -- ------------------ Multiplexors -----------------------------------------
   
   -- multiplex TX_DATA
   mx_tx_data_i: process(mxs_sel, mx_data_out, fl_fifo_tx_data)
   begin
      case mxs_sel is
         when '1' => TX_DATA <= mx_data_out;
         when '0' => TX_DATA <= fl_fifo_tx_data;
         when others => TX_DATA <= fl_fifo_tx_data;
      end case;
   end process;
   
   -- set output flow link signals
   
   TX_SOF_N <= not (first_part and fsm_send_length);
   TX_SOP_N <= not((first_part and fsm_send_length) -- SOP on start of transmit
                  -- others, when data (header)
                  or (fsm_send_data and (not fl_fifo_tx_sop_n)));
   TX_EOP_N <= not((not(fl_fifo_tx_eop_n) and fsm_send_data) -- last data
                  -- last header data without idle
                  or ((not is_idle) and fsm_send_header and (not fl_fifo_tx_eop_n))
                  -- last idle
                  or ((not is_idle) and fsm_send_idle)) ;
   
   end generate;


   -- SHARED (for all data width) output logic resources
   
   fsm_eop_valid_n   <= fl_fifo_tx_eop_n or TX_DST_RDY_N;
   fsm_eof_valid_n   <= fl_fifo_tx_eof_n or TX_DST_RDY_N;
   mxs_sel           <= fsm_send_length or fsm_send_idle or fsm_wait_state;
   fifo_read_req     <= fsm_next_data;
   TX_EOF_N          <= not((not fl_fifo_tx_eof_n) and fsm_send_data);
   TX_SRC_RDY_N      <= not (fsm_send_idle or fsm_send_length or
                        (fsm_send_data and (not fl_fifo_tx_src_rdy_n)) or
                        (fsm_send_header and (not fl_fifo_tx_src_rdy_n)));
                        
   -- ------------------ Multiplexors -----------------------------------------
   
   -- multiplex TX_REM
   mx_tx_remi: process(mxs_sel, fl_fifo_tx_rem)
   begin
      case mxs_sel is
         when '1' => TX_REM <= ONES_REM; -- always valid
         when '0' => TX_REM <= fl_fifo_tx_rem;
         when others => TX_REM <= fl_fifo_tx_rem;
      end case;
   end process;
   
   --- multiplex fl_fifo read request
   mx_fl_fifo_tx_dst_rdy_n_i: process(mxs_sel, TX_DST_RDY_N)
   begin
      case mxs_sel is
         when '1' => fl_fifo_tx_dst_rdy_n <= '1';
         when '0' => fl_fifo_tx_dst_rdy_n <= TX_DST_RDY_N;
         when others => fl_fifo_tx_dst_rdy_n <= TX_DST_RDY_N;
      end case;
   end process;
   
   -- ------------------ Other components -------------------------------------
          
   -- mapping main FSM
   FL_FRAME_METER_FSM_I : entity work.FL_FRAME_METER_FSM
      port map(
         CLK         => CLK,
         RESET       => RESET,
         -- input signals
         EOF_VLD_N      => fsm_eof_valid_n,
         EOP_VLD_N      => fsm_eop_valid_n,
         FIFO_EMPTY     => fsm_fifo_empty,
         IS_IDLE        => fsm_is_idle,
         NEXT_DATA      => fsm_next_data,

         -- output signals
         WAIT_STATE     => fsm_wait_state,
         SEND_LENGTH    => fsm_send_length,
         SEND_HEADER    => fsm_send_header,
         SEND_IDLE      => fsm_send_idle,
         SEND_DATA      => fsm_send_data
      );

   -- FIFO for storing lengths of header and segment stored in FL_FIFO
   FIFO_LENGTH_I : entity work.FIFO
      generic map(
         DATA_WIDTH     => 2*CNT_SIZE + IDLE_WIDTH,
         DISTMEM_TYPE   => 16,
         ITEMS          => FIFO_LENGTH_ITEMS
      )
      port map(
         RESET       => RESET,
         CLK         => CLK,
         -- write interface
         DATA_IN     => fifo_data_in,
         WRITE_REQ   => fifo_write_req,
         FULL        => fifo_full,
         LSTBLK      => open,
         -- read interface
         DATA_OUT    => fifo_data_out,
         READ_REQ    => fifo_read_req,
         EMPTY       => fifo_empty
      );
   
   -- FL_FIFO for storing packets
   FL_FIFO_I : entity work.FL_FIFO
      generic map(
         DATA_WIDTH     => DATA_WIDTH,
         USE_BRAMS      => true,
         ITEMS          => FL_FIFO_ITEMS,
         BLOCK_SIZE     => 0,
         STATUS_WIDTH   => 1,
         PARTS          => 2
      )  
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- write interface
         RX_DATA        => RX_DATA,
         RX_REM         => RX_REM,
         RX_SRC_RDY_N   => RX_SRC_RDY_N,
         RX_DST_RDY_N   => fl_fifo_rx_dst_rdy_n,
         RX_SOP_N       => RX_SOP_N,
         RX_EOP_N       => RX_EOP_N,
         RX_SOF_N       => RX_SOF_N,
         RX_EOF_N       => RX_EOF_N,
         -- read interface
         TX_DATA        => fl_fifo_tx_data,
         TX_REM         => fl_fifo_tx_rem,
         TX_SRC_RDY_N   => fl_fifo_tx_src_rdy_n,
         TX_DST_RDY_N   => fl_fifo_tx_dst_rdy_n,
         TX_SOP_N       => fl_fifo_tx_sop_n,
         TX_EOP_N       => fl_fifo_tx_eop_n,
         TX_SOF_N       => fl_fifo_tx_sof_n,
         TX_EOF_N       => fl_fifo_tx_eof_n,
         -- FIFO state signals
         LSTBLK         => open,
         FULL           => open,
         EMPTY          => open,
         STATUS         => open
      );
      
   -- FL_DEC for used state signals in architecture
   FL_DEC_I: entity work.FL_DEC
      generic map(
         HEADER      => true,
         FOOTER      => false
      )
      port map(
         CLK         => CLK,
         RESET       => RESET,  
         -- input interface
         SOF_N          => RX_SOF_N,
         SOP_N          => RX_SOP_N,
         EOP_N          => RX_EOP_N,
         EOF_N          => RX_EOF_N,
         SRC_RDY_N      => RX_SRC_RDY_N,
         DST_RDY_N      => RX_DST_RDY_N,
         -- output signals
         SOF            => open,
         SOHDR          => open,  
         EOHDR          => open,
         HDR_FRAME      => fl_dec_hdr_frame,  
         SOPLD          => open,
         EOPLD          => open, 
         PLD_FRAME      => fl_dec_pld_frame,
         SOFTR          => open, 
         EOFTR          => open, 
         FTR_FRAME      => open,  
         EOF            => fl_dec_eof,  
         SRC_RDY        => fl_dec_src_rdy,
         DST_RDY        => fl_dec_dst_rdy
       );
      
end architecture full;
