-- sw_rxbuf.vhd: SW_RXBUF top architecture
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

use work.bmem_func.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of SW_RXBUF is

   -- ------------------ Constants declaration --------------------------------
   constant OFFSET_WIDTH      : integer := 20;
   constant LENGTH_WIDTH      : integer := 12;
   constant IFC_WIDTH         : integer := 4;
   constant BMEM_WIDTH        : integer := DATA_WIDTH;
   constant BMEM_ADDR_WIDTH   : integer := log2(BMEM_ITEMS);
   constant BMEM_TYPE         : integer := 18;
   constant CTRL_MEM_WIDTH    : integer := OFFSET_WIDTH + LENGTH_WIDTH + 
                                           IFC_WIDTH;
   -- CTRL memory: Distributed RAM type, only 16, 32, 64 bits
   constant CTRL_MEM_TYPE     : integer := 16;
   constant RESERVED_ITEMS    : integer := (CONTROL_SIZE + ((DATA_WIDTH/8)-1))
                                           / (DATA_WIDTH/8);
   constant STATUS_WIDTH      : integer := 16;

   -- ------------------ Signals declaration ----------------------------------
   -- registers
   signal reg_cb_ctrl_ready   : std_logic;
   signal reg_cb_ctrl_ready_we: std_logic;
   signal reg_ctrl_mem        : std_logic_vector(CTRL_MEM_WIDTH-1 downto 0);
   signal reg_ctrl_mem_we     : std_logic;
   signal reg_status          : std_logic_vector(STATUS_WIDTH-1 downto 0);
   signal reg_ctrl_mem_do     : std_logic_vector(CTRL_MEM_WIDTH-1 downto 0);
   signal reg_ctrl_mem_pipe_en : std_logic;
   signal reg_ctrl_mem_rd     : std_logic;
   signal reg_ctrl_mem_dv     : std_logic;
   
   -- BlockRAM memory signals
   signal bmem_addra          : std_logic_vector(BMEM_ADDR_WIDTH-1 downto 0);
   signal bmem_wea            : std_logic;
   signal bmem_dia            : std_logic_vector(BMEM_WIDTH-1 downto 0);
   -- B interface
   signal bmem_reb            : std_logic;
   signal bmem_pipe_enb       : std_logic;
   signal bmem_addrb          : std_logic_vector(BMEM_ADDR_WIDTH-1 downto 0);
   signal bmem_dib            : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal bmem_dob_dv         : std_logic;
   signal bmem_dob            : std_logic_vector(DATA_WIDTH-1 downto 0);

   -- ctrl memory + FIFO signals
   signal ctrl_di             : std_logic_vector(CTRL_MEM_WIDTH-1 downto 0);
   signal mx_ctrl_raddr       : std_logic_vector(log2(CTRL_MEM_ITEMS)-1 
                                                                     downto 0);
   signal ctrl_dob            : std_logic_vector(CTRL_MEM_WIDTH-1 downto 0);
   signal fifo_waddr          : std_logic_vector(log2(CTRL_MEM_ITEMS)-1 
                                                                     downto 0);
   signal fifo_raddr          : std_logic_vector(log2(CTRL_MEM_ITEMS)-1 
                                                                     downto 0);
   signal fifo_status         : std_logic_vector(7 downto 0);
   signal fifo_wr             : std_logic;
   signal fifo_rd             : std_logic;
   signal fifo_full           : std_logic;
   signal fifo_empty          : std_logic;

   -- CU signals
   signal cu_ctrl_offset      : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal cu_ctrl_length      : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal cu_ctrl_ifc         : std_logic_vector(IFC_WIDTH-1 downto 0);
   signal cu_ctrl_we          : std_logic;
   signal cu_ctrl_full        : std_logic;
   signal cu_debug_info       : std_logic_vector(3 downto 0);

   -- others
   signal cb_read_ctrl        : std_logic;
   signal read_req            : std_logic;
   signal reg_status_di       : std_logic_vector(STATUS_WIDTH-1 downto 0);
   
begin
   -- directly mapped signals -------------------------------------------------
   ctrl_di(OFFSET_WIDTH-1 downto 0) <= cu_ctrl_offset;
   ctrl_di(OFFSET_WIDTH+LENGTH_WIDTH-1 downto OFFSET_WIDTH) <= cu_ctrl_length;
   ctrl_di(OFFSET_WIDTH+LENGTH_WIDTH+IFC_WIDTH-1 downto 
      OFFSET_WIDTH+LENGTH_WIDTH) <= cu_ctrl_ifc;

   fifo_wr           <= cu_ctrl_we;
   cu_ctrl_full      <= fifo_full;
   
   -- bmem signals
   bmem_addrb        <= RD_ADDR(BMEM_ADDR_WIDTH+log2(DATA_WIDTH/8)-1 
                        downto log2(DATA_WIDTH/8));
   bmem_dib          <= (others => '0');
   bmem_pipe_enb     <= RD_DST_RDY;

   -- setting signals for Control Bus
   INFO_READY        <= reg_cb_ctrl_ready;
   fifo_rd           <= cb_read_ctrl;
   CTRL_OFFSET       <= reg_ctrl_mem(OFFSET_WIDTH-1 downto 0);
   CTRL_LENGTH       <= reg_ctrl_mem(OFFSET_WIDTH+LENGTH_WIDTH-1 downto
                        OFFSET_WIDTH);
   CTRL_IFC          <= reg_ctrl_mem(OFFSET_WIDTH+LENGTH_WIDTH+IFC_WIDTH-1 
                        downto OFFSET_WIDTH+LENGTH_WIDTH);

   -- control signals
   reg_ctrl_mem_we   <= cb_read_ctrl;
   reg_cb_ctrl_ready_we <= cb_read_ctrl or ACK;
   cb_read_ctrl      <= (not fifo_empty) and (not reg_cb_ctrl_ready);
   reg_ctrl_mem_pipe_en <= RD_DST_RDY;
   
   -- STATUS register input
   reg_status_di(3 downto 0)  <= cu_debug_info;
   reg_status_di(4)           <= reg_cb_ctrl_ready;
   reg_status_di(7 downto 5)  <= (others => '0');
   reg_status_di(15 downto 8) <= fifo_status;

   -- IB endpoint control signals
   read_req          <= RD_REQ and RD_DST_RDY;
   
   -- ------------------ ADC RD -----------------------------------------------
   adc_rdp: process (RD_ADDR, RD_REQ, read_req, bmem_dob, bmem_dob_dv, 
                     cb_read_ctrl, reg_ctrl_mem_do, reg_ctrl_mem_dv, 
                     reg_status)
   begin
      RD_DATA           <= (others => '0');
      RD_ARDY           <= '1';
      bmem_reb          <= '0';
      reg_ctrl_mem_rd   <= '0';
      RD_SRC_RDY        <= '0';
      
      case RD_ADDR(20) is
         when '0'  =>      -- main bram memory with packet data
            bmem_reb    <= read_req;
            RD_ARDY     <= read_req;
            RD_DATA(BMEM_WIDTH-1 downto 0) <= bmem_dob;
            RD_SRC_RDY  <= bmem_dob_dv;
         when '1' =>       -- control memory
            case RD_ADDR(12) is
               when '0'  =>      -- ctrl memory
                  reg_ctrl_mem_rd <= read_req and (not cb_read_ctrl);
                  RD_ARDY        <= read_req and (not cb_read_ctrl);
                  RD_DATA(CTRL_MEM_WIDTH-1 downto 0) <= reg_ctrl_mem_do;
                  RD_SRC_RDY     <= reg_ctrl_mem_dv;
               when '1' =>       -- debug register
                  case RD_ADDR(3 downto 0) is
                     when X"0" => null;
                        RD_ARDY     <= read_req;
                        RD_DATA(STATUS_WIDTH-1 downto 0) <= reg_status;
                        RD_SRC_RDY  <= RD_REQ;
                     when others => null;
                  end case;
               when others => null;
            end case;
         when others => null;
      end case;
   end process;

   -- ------------------ Main Packet memory -----------------------------------
   DP_BMEM_I : entity work.DP_BMEM
   generic map(
      DATA_WIDTH  => BMEM_WIDTH,
      ITEMS       => BMEM_ITEMS,
      BRAM_TYPE   => BMEM_TYPE,
      OUTPUT_REG  => TRUE
   )
   port map(
      -- Common interface
      RESET       => RESET,
      -- Interface A
      CLKA        => CLK,
      PIPE_ENA    => '1',
      REA         => '0',
      WEA         => bmem_wea,
      ADDRA       => bmem_addra,
      DIA         => bmem_dia,
      DOA_DV      => open,
      DOA         => open,
      -- Interface B
      CLKB        => CLK,
      PIPE_ENB    => bmem_pipe_enb,
      REB         => bmem_reb,
      WEB         => '0',
      ADDRB       => bmem_addrb,
      DIB         => bmem_dib,
      DOB_DV      => bmem_dob_dv,
      DOB         => bmem_dob
   );

   -- ------------------ FIFO control logic -----------------------------------
   SWT_FIFO_CTRL_I : entity work.SWR_FIFO_CTRL
      generic map(
         DISTMEM_TYPE   => CTRL_MEM_TYPE,
         ITEMS          => CTRL_MEM_ITEMS,
         STATUS_WIDTH   => 8
      )
      port map(
         RESET          => RESET,
         CLK            => CLK,
         -- Write interface
         WADDR          => fifo_waddr,
         WRITE_REQ      => fifo_wr,
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
         DI          => ctrl_di,
         WE          => fifo_wr,
         WCLK        => CLK,
         ADDRA       => fifo_waddr,
         DOA         => open,
         -- Read Port
         ADDRB       => mx_ctrl_raddr,
         DOB         => ctrl_dob
      );
   
   -- ------------------ Control Unit -----------------------------------------
   SWR_CU_I : entity work.SWR_CU
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         BMEM_ITEMS     => BMEM_ITEMS,
         BFIFO_ITEMS    => BMEM_MAX_BLOCKS,
         RESERVED_ITEMS => RESERVED_ITEMS,
         OFFSET_WIDTH   => OFFSET_WIDTH,
         LENGTH_WIDTH   => LENGTH_WIDTH,
         HEADER         => HEADER,
         FOOTER         => FOOTER
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- input FrameLink interface
         RX_SOF_N       => RX_SOF_N,
         RX_SOP_N       => RX_SOP_N,
         RX_EOP_N       => RX_EOP_N,
         RX_EOF_N       => RX_EOF_N,
         RX_SRC_RDY_N   => RX_SRC_RDY_N,
         RX_DST_RDY_N   => RX_DST_RDY_N,
         RX_DATA        => RX_DATA,
         RX_REM         => RX_REM,
         RX_SKIP_HEADER => RX_SKIP_HEADER,
         -- BlockRAM interface
         BMEM_DATA      => bmem_dia,
         BMEM_ADDR      => bmem_addra,
         BMEM_WE        => bmem_wea,
         -- Control bus interface
         CTRL_OFFSET    => cu_ctrl_offset,
         CTRL_LENGTH    => cu_ctrl_length,
         CTRL_IFC       => cu_ctrl_ifc,
         CTRL_WE        => cu_ctrl_we,
         CTRL_FULL      => cu_ctrl_full,
         FREE_PACKET    => FREE_PACKET,
         DEBUG_INFO     => cu_debug_info
      );

   -- ------------------ Multiplexer ------------------------------------------
   mx_ctrl_raddrp: process( cb_read_ctrl, fifo_raddr, RD_ADDR )
   begin
      case cb_read_ctrl is
         when '0' => mx_ctrl_raddr <= RD_ADDR(3+log2(CTRL_MEM_ITEMS)-1 downto 3);
         when '1' => mx_ctrl_raddr <= fifo_raddr;
         when others => mx_ctrl_raddr <= (others => '0');
      end case;
   end process;

   -- register reg_ctrl_mem ---------------------------------------------------
   reg_ctrl_memp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if reg_ctrl_mem_we = '1' then
            reg_ctrl_mem <= ctrl_dob;
         end if;
      end if;
   end process;

   -- register reg_cb_ctrl_ready ----------------------------------------------
   reg_cb_ctrl_readyp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_cb_ctrl_ready <= '0';
         elsif reg_cb_ctrl_ready_we = '1' then
            reg_cb_ctrl_ready <= cb_read_ctrl;
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
            reg_ctrl_mem_do <= ctrl_dob;
            reg_ctrl_mem_dv <= reg_ctrl_mem_rd;
         end if;
      end if;
   end process;
   
end architecture full;
