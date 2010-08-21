-- sw_txbuf.vhd: SW_TXBUF top architecture
-- Copyright (C) 2006 CESNET
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

-- library containing log2 function
use work.math_pack.all;
-- auxilarity function needed to compute address width
use work.bmem_func.all;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of SW_TXBUF is

   -- ------------------ Constants declaration --------------------------------
   constant BMEM_OFFSET_WIDTH : integer := 20;
   constant BMEM_LENGTH_WIDTH : integer := 12;
   constant BMEM_ADDR_WIDTH   : integer := log2(BMEM_ITEMS);
   constant BMEM_WIDTH        : integer := DATA_WIDTH;
   constant BMEM_TYPE         : integer := 18;
   constant ADDR_PREFIX       : integer := log2(DATA_WIDTH/8);
   -- CTRL_MEM_WIDTH: width of mem. offset + length value
   constant CTRL_MEM_WIDTH    : integer := BMEM_OFFSET_WIDTH + BMEM_LENGTH_WIDTH;
   -- CTRL memory: Distributed RAM type, only 16, 32, 64 bits
   constant CTRL_MEM_TYPE     : integer := 16;
   constant STATUS_WIDTH      : integer := 8;
   
   -- ------------------ Signals declaration ----------------------------------
   -- registers
   signal reg_enable_ack      : std_logic;
   signal reg_enable_ack_we   : std_logic;
   signal reg_ctrl_mem_do     : std_logic_vector(CTRL_MEM_WIDTH-1 downto 0);
   signal reg_ctrl_mem_pipe_en : std_logic;
   signal reg_ctrl_mem_rd     : std_logic;
   signal reg_ctrl_mem_dv     : std_logic;
   signal reg_ready           : std_logic;
   signal reg_ready_we        : std_logic;
   signal reg_status          : std_logic_vector(31 downto 0);
   signal reg_status_di       : std_logic_vector(31 downto 0);
   
   -- BlockRAM memory signals
   signal bmem_pipe_ena       : std_logic;
   signal bmem_waddra         : std_logic_vector(BMEM_ADDR_WIDTH-1 downto 0);
   signal bmem_raddra         : std_logic_vector(BMEM_ADDR_WIDTH-1 downto 0);
   signal mx_bmem_addra       : std_logic_vector(BMEM_ADDR_WIDTH-1 downto 0);
   signal bmem_rd             : std_logic;
   signal bmem_wr             : std_logic;
   signal bmem_dia            : std_logic_vector(BMEM_WIDTH-1 downto 0);
   signal bmem_oper           : std_logic;   -- 0: read ifc; 1: write ifc
   signal bmem_doa            : std_logic_vector(BMEM_WIDTH-1 downto 0);
   signal bmem_doa_dv         : std_logic;
   -- B interface
   signal bmem_pipe_enb       : std_logic;
   signal bmem_reb            : std_logic;
   signal bmem_beb            : std_logic_vector(DATA_WIDTH/8-1 downto 0);
   signal bmem_addrb          : std_logic_vector(log2(BMEM_ITEMS)-1 downto 0);
   signal bmem_dib            : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal bmem_dob_dv         : std_logic;
   signal bmem_dob            : std_logic_vector(DATA_WIDTH-1 downto 0);

   -- ctrl memory + FIFO signals
   signal ctrl_oper           : std_logic;   -- 0: rd from IB, 1: wr from FIFO
   signal ctrl_din_ib         : std_logic_vector(CTRL_MEM_WIDTH-1 downto 0);
   signal ctrl_din_cb         : std_logic_vector(CTRL_MEM_WIDTH-1 downto 0);
   signal mx_ctrl_din         : std_logic_vector(CTRL_MEM_WIDTH-1 downto 0);
   signal mx_ctrl_addr        : std_logic_vector(log2(CTRL_MEM_ITEMS)-1 
                                                                     downto 0);
   signal mx_ctrl_addr_sel    : std_logic; 
   signal mx_fifo_wr          : std_logic;                                                                  
   signal ctrl_doa            : std_logic_vector(CTRL_MEM_WIDTH-1 downto 0);
   signal ctrl_dob            : std_logic_vector(CTRL_MEM_WIDTH-1 downto 0);
   signal fifo_waddr          : std_logic_vector(log2(CTRL_MEM_ITEMS)-1 
                                                                     downto 0);
   signal fifo_raddr          : std_logic_vector(log2(CTRL_MEM_ITEMS)-1 
                                                                     downto 0);
   signal fifo_wr_cb          : std_logic;   -- write from CB
   signal fifo_wr_ib          : std_logic;   -- write from IB
   signal fifo_rd             : std_logic;
   signal fifo_oper           : std_logic;   -- 0: wr from IB, 1: wr from CB
   signal fifo_full           : std_logic;
   signal fifo_status         : std_logic_vector(STATUS_WIDTH-1 downto 0);
   signal fifo_empty          : std_logic;

   -- CU
   signal cu_ack              : std_logic;
   signal cu_send_ack_rdy     : std_logic;

   signal cu_sof_n            : std_logic;
   signal cu_sop_n            : std_logic;
   signal cu_eop_n            : std_logic;
   signal cu_eof_n            : std_logic;
   signal cu_src_ready        : std_logic;
   signal cu_dst_ready        : std_logic;
   signal cu_data_out         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal cu_rem_out          : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

   -- output transformer
   signal trans_rx_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal trans_rx_rem        : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal trans_rx_sof_n      : std_logic;
   signal trans_rx_eof_n      : std_logic;
   signal trans_rx_sop_n      : std_logic;
   signal trans_rx_eop_n      : std_logic;
   signal trans_rx_src_rdy_n  : std_logic;
   signal trans_rx_dst_rdy_n  : std_logic;

   -- others
   signal read_req            : std_logic;

begin
   -- directly mapped signals -------------------------------------------------
   mx_ctrl_addr_sel     <= ctrl_oper or fifo_wr_cb;
   cu_send_ack_rdy      <= not reg_ready;
   
   -- BMEM signals
   bmem_waddra(BMEM_ADDR_WIDTH-1 downto 0)
                        <= WR_ADDR(BMEM_ADDR_WIDTH+ADDR_PREFIX-1 
                              downto ADDR_PREFIX);
   bmem_raddra(BMEM_ADDR_WIDTH-1 downto 0)
                        <= RD_ADDR(BMEM_ADDR_WIDTH+ADDR_PREFIX-1 
                              downto ADDR_PREFIX);
   bmem_dia             <= WR_DATA(BMEM_WIDTH-1 downto 0);
   bmem_dib             <= (others => '0');
   bmem_beb             <= (others => '0');
   bmem_pipe_ena        <= RD_DST_RDY;

   -- Control memory signals
   ctrl_din_cb(BMEM_OFFSET_WIDTH-1 downto 0) <= CTRL_OFFSET;
   ctrl_din_cb(CTRL_MEM_WIDTH-1 downto BMEM_OFFSET_WIDTH) <= CTRL_LENGTH;
   ctrl_din_ib          <= WR_DATA(CTRL_MEM_WIDTH-1 downto 0);

   -- registers' control signals
   reg_ready_we         <= (reg_enable_ack and cu_ack) or (reg_ready and ACK);
   reg_ctrl_mem_pipe_en <= RD_DST_RDY;
   
   -- FIFO signals
   fifo_oper            <= CTRL_WRITE;
   fifo_wr_cb           <= CTRL_WRITE;
   
   -- output transformer signals
   trans_rx_data        <= cu_data_out;
   trans_rx_rem         <= cu_rem_out;
   trans_rx_sof_n       <= cu_sof_n;
   trans_rx_eof_n       <= cu_eof_n;
   trans_rx_sop_n       <= cu_sop_n;
   trans_rx_eop_n       <= cu_eop_n;
   trans_rx_src_rdy_n   <= not cu_src_ready;
   cu_dst_ready         <= not trans_rx_dst_rdy_n;

   -- Output interface signals
   DIFF                 <= (others => '0');  -- unused at this time
   READY                <= reg_ready;
   CTRL_READY           <= not fifo_full;
   
   -- IB endpoint control signals
   read_req             <= RD_REQ and RD_DST_RDY;

   -- status register data in
   reg_status_di(0)     <= not cu_src_ready; -- SRC_RDY_N
   reg_status_di(1)     <= not cu_dst_ready; -- DST_RDY_N
   reg_status_di(2)     <= fifo_empty;    -- packet record FIFO empty
   reg_status_di(3)     <= fifo_full;     -- packet record FIFO full
   reg_status_di(4)     <= CTRL_WRITE;    -- new packet record from PPC
   reg_status_di(5)     <= not fifo_full; -- ready to receive packet record
   reg_status_di(6)     <= reg_ready;     -- packet sent (ack record ready)
   reg_status_di(7)     <= ACK;           -- packet sent message ack signal
   reg_status_di(15 downto 8) <= fifo_status;
   reg_status_di(31 downto 16) <= (others => '0');

   -- ------------------ ADC WR_REQ -------------------------------------------
   adc_wrp: process (WR_ADDR, WR_REQ, fifo_oper)
   begin
      bmem_wr           <= '0';
      bmem_oper         <= '0';
      reg_enable_ack_we <= '0';
      ctrl_oper         <= '0';
      WR_RDY            <= '1';
      fifo_wr_ib        <= '0';
      
      case WR_ADDR(20) is
         when '0'  =>      -- main bram memory with packet data
            bmem_wr     <= WR_REQ;
            bmem_oper   <= WR_REQ;
         when '1' =>       -- other memories
            case WR_ADDR(12) is
               when '0'  =>      -- ctrl memory
                  null;
               when '1' =>       -- FIFO logic over ctrl memory
                  case WR_ADDR(3 downto 0) is
                     when X"0" =>
                        fifo_wr_ib  <= WR_REQ and (not fifo_oper);
                        ctrl_oper   <= WR_REQ and (not fifo_oper);
                        WR_RDY      <= not fifo_oper;
                     when X"8" =>
                        reg_enable_ack_we <= WR_REQ;
                     when others => null;
                  end case;
               when others => null;
            end case;
         when others => null;
      end case;
   end process;

   -- ------------------ ADC RD_REQ -------------------------------------------
   adc_rdp: process (RD_ADDR, read_req, bmem_oper, bmem_doa, bmem_doa_dv, 
                     ctrl_oper, reg_ctrl_mem_do, reg_ctrl_mem_dv, 
                     reg_enable_ack, RD_REQ)
   begin
      RD_DATA           <= (others => '0');
      RD_ARDY           <= '1';
      bmem_rd           <= '0';
      RD_SRC_RDY        <= '0';
      reg_ctrl_mem_rd   <= '0';
      
      case RD_ADDR(20) is
         when '0'  =>      -- main bram memory with packet data
            bmem_rd     <= read_req and (not bmem_oper);
            RD_ARDY     <= read_req and (not bmem_oper);
            RD_DATA(BMEM_WIDTH-1 downto 0) <= bmem_doa;
            RD_SRC_RDY  <= bmem_doa_dv;
         when '1' =>       -- other memories
            case RD_ADDR(12) is
               when '0'  =>      -- ctrl memory
                  reg_ctrl_mem_rd <= read_req and (not ctrl_oper);
                  RD_ARDY        <= read_req and (not ctrl_oper);
                  RD_DATA(CTRL_MEM_WIDTH-1 downto 0) <= reg_ctrl_mem_do;
                  RD_SRC_RDY     <= reg_ctrl_mem_dv;
               when '1' =>       -- FIFO logic over ctrl memory
                  case RD_ADDR(7 downto 0) is
                     when X"00" => null;
                     when X"08" =>
                        RD_ARDY     <= read_req;
                        RD_DATA(0)  <= reg_enable_ack;
                        RD_SRC_RDY  <= RD_REQ;
                     when X"10" =>
                        RD_ARDY     <= read_req;
                        RD_DATA(31 downto 0) <= reg_status;
                        RD_SRC_RDY  <= RD_REQ;
                     when others => null;
                  end case;
               when others => null;
            end case;
         when others => null;
      end case;
   end process;

   -- ------------------ Main Packet memory -----------------------------------
   MAIN_MEMORY : entity work.DP_BMEM_BE
   generic map(
      DATA_WIDTH  => DATA_WIDTH,
      ITEMS       => BMEM_ITEMS,
      OUTPUT_REG  => FALSE
   )
   port map(
      -- Common interface
      RESET       => RESET,
      -- Interface A
      CLKA        => CLK,
      PIPE_ENA    => bmem_pipe_ena,
      REA         => bmem_rd,
      WEA         => bmem_wr,
      BEA         => WR_BE((DATA_WIDTH/8)-1 downto 0),
      ADDRA       => mx_bmem_addra,
      DIA         => bmem_dia,
      DOA_DV      => bmem_doa_dv,
      DOA         => bmem_doa,
      -- Interface B
      CLKB        => CLK,
      PIPE_ENB    => bmem_pipe_enb,
      REB         => bmem_reb,
      WEB         => '0',
      BEB         => bmem_beb,
      ADDRB       => bmem_addrb,
      DIB         => bmem_dib,
      DOB_DV      => bmem_dob_dv,
      DOB         => bmem_dob
   );

   -- ------------------ FIFO control logic -----------------------------------
   SWT_FIFO_CTRL_I : entity work.SWT_FIFO_CTRL
      generic map(
         DISTMEM_TYPE   => CTRL_MEM_TYPE,
         ITEMS          => CTRL_MEM_ITEMS,
         STATUS_WIDTH   => STATUS_WIDTH
      )
      port map(
         RESET          => RESET,
         CLK            => CLK,
         -- Write interface
         WADDR          => fifo_waddr,
         WRITE_REQ      => mx_fifo_wr,
         FULL           => fifo_full,
         STATUS         => fifo_status,
         -- Read interface
         RADDR          => fifo_raddr,
         READ_REQ       => fifo_rd,
         EMPTY          => fifo_empty
      );

   -- ------------------ Control Memory ---------------------------------------
   DP_DISTMEM_I : entity work.DP_DISTMEM
      generic map(
         DATA_WIDTH  => CTRL_MEM_WIDTH,
         ITEMS       => CTRL_MEM_ITEMS,
         DISTMEM_TYPE => CTRL_MEM_TYPE,
         DEBUG       => false
      )
      port map(
         -- Common interface
         RESET       => RESET,
         -- R/W Port
         DI          => mx_ctrl_din,
         WE          => mx_fifo_wr,
         WCLK        => CLK,
         ADDRA       => mx_ctrl_addr,
         DOA         => ctrl_doa,
         -- Read Port
         ADDRB       => fifo_raddr,
         DOB         => ctrl_dob
      );
   
   -- ------------------ Control Unit -----------------------------------------
   SWT_CU_I : entity work.SWT_CU
      generic map(
         DATA_WIDTH     => DATA_WIDTH,
         BMEM_ITEMS     => BMEM_ITEMS,
         BMEM_LENGTH_WIDTH => BMEM_LENGTH_WIDTH,
         BMEM_OFFSET_WIDTH => BMEM_OFFSET_WIDTH,
         CTRL_MEM_ITEMS => CTRL_MEM_ITEMS,
         CONTROL_DATA_LENGTH => CONTROL_DATA_LENGTH,
         CONSTANT_HW_HEADER_LENGTH => CONSTANT_HW_HEADER_LENGTH,
         CONSTANT_HW_HEADER_DATA   => CONSTANT_HW_HEADER_DATA
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- BlockRAM interface
         BMEM_ADDR      => bmem_addrb,
         BMEM_RD        => bmem_reb,
         BMEM_PIPE_EN   => bmem_pipe_enb,
         BMEM_DO        => bmem_dob,
         BMEM_DV        => bmem_dob_dv,
         -- Control Bus interface
         SEND_ACK       => cu_ack,
         SEND_ACK_RDY   => cu_send_ack_rdy,
         -- Control Memory interface
         CTRL_OFFSET    => ctrl_dob(BMEM_OFFSET_WIDTH-1 downto 0),
         CTRL_LENGTH    => ctrl_dob(BMEM_OFFSET_WIDTH + BMEM_LENGTH_WIDTH-1 
                           downto BMEM_OFFSET_WIDTH),
         CTRL_EMPTY     => fifo_empty,
         CTRL_RRQ       => fifo_rd,
         -- output interface
         SOF_N          => cu_sof_n,
         SOP_N          => cu_sop_n,
         EOP_N          => cu_eop_n,
         EOF_N          => cu_eof_n,
         SRC_READY      => cu_src_ready,
         DST_READY      => cu_dst_ready,
         DATA_OUT       => cu_data_out,
         REM_OUT        => cu_rem_out
      );

   -- ------------------ Multiplexer ------------------------------------------
   mx_bmem_addrap: process( bmem_oper, bmem_waddra, bmem_raddra )
   begin
      case bmem_oper is
         when '0' => mx_bmem_addra <= bmem_raddra;
         when '1' => mx_bmem_addra <= bmem_waddra;
         when others => mx_bmem_addra <= (others => '0');
      end case;
   end process;

   -- ------------------ Multiplexer ------------------------------------------
   mx_ctrl_addrp: process( mx_ctrl_addr_sel, RD_ADDR, fifo_waddr )
   begin
      case mx_ctrl_addr_sel is
         when '0' => mx_ctrl_addr <=
            RD_ADDR(log2(CTRL_MEM_ITEMS)+ADDR_PREFIX-1 downto ADDR_PREFIX);
         when '1' => mx_ctrl_addr <= fifo_waddr;
         when others => mx_ctrl_addr <= (others => '0');
      end case;
   end process;

   -- ------------------ Multiplexer ------------------------------------------
   mx_ctrl_dinp: process( fifo_oper, ctrl_din_ib, ctrl_din_cb )
   begin
      case fifo_oper is
         when '0' => mx_ctrl_din <= ctrl_din_ib;
         when '1' => mx_ctrl_din <= ctrl_din_cb;
         when others => mx_ctrl_din <= (others => '0');
      end case;
   end process;

   -- ------------------ Multiplexer ------------------------------------------
   mx_fifo_wrp: process( fifo_oper, fifo_wr_ib, fifo_wr_cb )
   begin
      case fifo_oper is
         when '0' => mx_fifo_wr <= fifo_wr_ib;
         when '1' => mx_fifo_wr <= fifo_wr_cb;
         when others => mx_fifo_wr <= '0';
      end case;
   end process;

   -- register reg_enable_ack -------------------------------------------------
   reg_enable_ackp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_enable_ack <= '1';
         elsif (reg_enable_ack_we = '1') then
            reg_enable_ack <= WR_DATA(0);
         end if;
      end if;
   end process;

   -- register reg_ready ------------------------------------------------------
   reg_readyp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_ready <= '0';
         elsif (reg_ready_we = '1') then
            reg_ready <= cu_ack and ((not ACK) or (not reg_ready));
         end if;
      end if;
   end process;

   -- register reg_status -----------------------------------------------------
   reg_statusp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg_status <= reg_status_di;
      end if;
   end process;

   -- control memory output registers -----------------------------------------
   process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_ctrl_mem_do   <= (others => '0');
            reg_ctrl_mem_dv   <= '0';
         elsif (reg_ctrl_mem_pipe_en = '1') then
            reg_ctrl_mem_do <= ctrl_doa;
            reg_ctrl_mem_dv <= reg_ctrl_mem_rd;
         end if;
      end if;
   end process;

   -- mapping output data transformer
   FL_TRANSFORMER_I : entity work.FL_TRANSFORMER
      generic map(
         RX_DATA_WIDTH  => DATA_WIDTH,
         TX_DATA_WIDTH  => OUTPUT_WIDTH
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- RX interface
         RX_DATA        => trans_rx_data,
         RX_REM         => trans_rx_rem,
         RX_SOF_N       => trans_rx_sof_n,
         RX_EOF_N       => trans_rx_eof_n,
         RX_SOP_N       => trans_rx_sop_n,
         RX_EOP_N       => trans_rx_eop_n,
         RX_SRC_RDY_N   => trans_rx_src_rdy_n,
         RX_DST_RDY_N   => trans_rx_dst_rdy_n,
         -- TX interface
         TX_DATA        => DATA_OUT,
         TX_REM         => REM_OUT,
         TX_SOF_N       => SOF_N,
         TX_EOF_N       => EOF_N,
         TX_SOP_N       => SOP_N,
         TX_EOP_N       => EOP_N,
         TX_SRC_RDY_N   => SRC_RDY_N,
         TX_DST_RDY_N   => DST_RDY_N
      );

end architecture full;
