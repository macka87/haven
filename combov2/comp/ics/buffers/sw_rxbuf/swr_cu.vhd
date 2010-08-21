-- swr_cu.vhd: Control unit
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek    <kosek@liberouter.org>
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


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity SWR_CU is
   generic (
      DATA_WIDTH     : integer;
      BMEM_ITEMS     : integer;
      BFIFO_ITEMS    : integer;  -- number of block FIFO items
      RESERVED_ITEMS : integer;  -- number of items to reserve for control data
      OFFSET_WIDTH   : integer;
      LENGTH_WIDTH   : integer;
      HEADER         : boolean;
      FOOTER         : boolean
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;
      
      -- input FrameLink interface
      RX_SOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SKIP_HEADER : in  std_logic;

      -- BlockRAM interface
      BMEM_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      BMEM_ADDR      : out std_logic_vector(log2(BMEM_ITEMS)-1 downto 0);
      BMEM_WE        : out std_logic;

      -- Control bus interface
      CTRL_OFFSET    : out std_logic_vector(OFFSET_WIDTH-1 downto 0);
      CTRL_LENGTH    : out std_logic_vector(LENGTH_WIDTH-1 downto 0);
      CTRL_IFC       : out std_logic_vector(3 downto 0);
      CTRL_WE        : out std_logic;
      CTRL_FULL      : in  std_logic;
      FREE_PACKET    : in  std_logic;
      DEBUG_INFO     : out std_logic_vector(3 downto 0)
   );
end entity SWR_CU;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of SWR_CU is

   -- ------------------ Constants declaration --------------------------------
   constant BMEM_ADDR_W       : integer := log2(BMEM_ITEMS);
   constant BLOCK_WIDTH       : integer := log2(RESERVED_ITEMS - 1) + 1;
   constant REM_WIDTH         : integer := log2(DATA_WIDTH/8);

   -- ------------------ Signals declaration ----------------------------------
   -- counters
   signal cnt_length          : std_logic_vector
                              (LENGTH_WIDTH-log2(DATA_WIDTH/8) downto 0);
   signal cnt_length_ce       : std_logic;
   signal cnt_length_rst      : std_logic;
   
   -- registers
   signal reg_drem            : std_logic_vector(REM_WIDTH-1 downto 0);
   signal reg_drem_we         : std_logic;
   signal reg_offset          : std_logic_vector(log2(BMEM_ITEMS)-1 downto 0);
   signal reg_offset_we       : std_logic;
   signal reg_ifc             : std_logic_vector(3 downto 0);
   signal reg_ifc_we          : std_logic;

   -- decoder signals
   signal dec_payload         : std_logic;
   signal dec_eopld           : std_logic;
   signal dec_sof             : std_logic;
   signal dec_eof             : std_logic;
   signal dec_src_rdy         : std_logic;
   signal dec_dst_rdy         : std_logic;
   
   -- others
   signal dv                  : std_logic;
   signal input_eof           : std_logic;
   signal bmem_ctrl_we        : std_logic;
   signal bmem_ctrl_eof       : std_logic;
   signal bmem_ctrl_full      : std_logic;
   signal bmem_ctrl_ready     : std_logic;
   signal bmem_ctrl_offset    : std_logic_vector(log2(BMEM_ITEMS)-1 downto 0);
   signal packet_length       : std_logic_vector(LENGTH_WIDTH downto 0);

   signal trimmer_tx_sof_n    : std_logic;
   signal trimmer_tx_sop_n    : std_logic;
   signal trimmer_tx_eop_n    : std_logic;
   signal trimmer_tx_eof_n    : std_logic;
   signal trimmer_tx_src_rdy_n : std_logic;
   signal trimmer_tx_dst_rdy_n : std_logic;
   signal trimmer_tx_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal trimmer_tx_rem      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

   signal trimmer_rx_dst_rdy_n : std_logic;
   
begin
   -- directly mapped signals -------------------------------------------------
   dv             <= dec_src_rdy and dec_dst_rdy;
   dec_dst_rdy    <= not bmem_ctrl_full and not ((not RX_EOF_N) and CTRL_FULL)
                     and bmem_ctrl_ready;
   cnt_length_ce  <= dec_payload and (not dec_eopld) and dv;
   input_eof      <= dec_eof and dv;
   cnt_length_rst <= input_eof;
   reg_offset_we  <= dec_sof and dv;
   reg_drem_we    <= dec_eopld and dv;
   reg_ifc_we     <= not (RX_SOF_N or RX_SRC_RDY_N or trimmer_rx_dst_rdy_n);

   bmem_ctrl_we   <= dec_src_rdy;
   bmem_ctrl_eof  <= input_eof;
   
   -- mapping interface output signals
   CTRL_OFFSET(OFFSET_WIDTH-1 downto log2(BMEM_ITEMS)+log2(DATA_WIDTH/8))
                  <= (others => '0');
   CTRL_OFFSET(log2(BMEM_ITEMS)+log2(DATA_WIDTH/8)-1 downto log2(DATA_WIDTH/8))
                  <= reg_offset;
   CTRL_OFFSET(log2(DATA_WIDTH/8)-1 downto 0)
                  <= (others => '0');
   CTRL_LENGTH    <= packet_length(LENGTH_WIDTH-1 downto 0);
   
   CTRL_IFC       <= reg_ifc;
   CTRL_WE        <= input_eof;

   DEBUG_INFO     <= bmem_ctrl_ready & bmem_ctrl_full & (not dec_dst_rdy) & (not dec_src_rdy);

   RX_DST_RDY_N   <= trimmer_rx_dst_rdy_n;

   -- ------------------ counter cnt_length -----------------------------------
   cnt_lengthp: process (CLK) 
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' or cnt_length_rst = '1' then 
            cnt_length <= conv_std_logic_vector(0, cnt_length'length);
         elsif cnt_length_ce = '1' then
            cnt_length <= cnt_length + 1;
         end if;
      end if;
   end process;
   
   -- slightly different REM computation --------------------------------------
   GEN_REG_DREM : if FOOTER generate

      CTRL_LENGTH(log2(DATA_WIDTH/8)-1 downto 0) <= reg_drem + 1;
      packet_length  <= (cnt_length & reg_drem) + 1;

      reg_dremp: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (reg_drem_we = '1') then
               reg_drem <= RX_REM;
            end if;
         end if;
      end process;
   
   end generate;

   GEN_NO_REG_DREM : if not FOOTER generate

      packet_length  <= (cnt_length & RX_REM) + 1;

   end generate;

   -- ------------------ register reg_offset ----------------------------------
   reg_offsetp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (reg_offset_we = '1') then
            reg_offset <= bmem_ctrl_offset;
         end if;
      end if;
   end process;

   -- ------------------ register reg_ifc -------------------------------------
   reg_ifcp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (reg_ifc_we = '1') then
            reg_ifc <= trimmer_tx_data(35 downto 32);   -- IFC_ID
         end if;
      end if;
   end process;

   -- frame trimmer: cuts header before storing into the memory if desired
   FL_TRIMMER_I : entity work.FL_TRIMMER
      generic map(
         DATA_WIDTH     => DATA_WIDTH,
         HEADER         => true,
         FOOTER         => false,
         TRIM_HEADER    => true,
         TRIM_FOOTER    => false
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- input interface
         RX_SOF_N       => RX_SOF_N,
         RX_SOP_N       => RX_SOP_N,
         RX_EOP_N       => RX_EOP_N,
         RX_EOF_N       => RX_EOF_N,
         RX_SRC_RDY_N   => RX_SRC_RDY_N,
         RX_DST_RDY_N   => trimmer_rx_dst_rdy_n,
         RX_DATA        => RX_DATA,
         RX_REM         => RX_REM,
         -- output interface
         TX_SOF_N       => trimmer_tx_sof_n,
         TX_SOP_N       => trimmer_tx_sop_n,
         TX_EOP_N       => trimmer_tx_eop_n,
         TX_EOF_N       => trimmer_tx_eof_n,
         TX_SRC_RDY_N   => trimmer_tx_src_rdy_n,
         TX_DST_RDY_N   => trimmer_tx_dst_rdy_n,
         TX_DATA        => trimmer_tx_data,
         TX_REM         => trimmer_tx_rem,
         -- control signals
         ENABLE         => RX_SKIP_HEADER
      );

   -- Main Packet Memory Controller
   SWR_BMEM_CTRL_I : entity work.SWR_BMEM_CTRL
      generic map(
         DATA_WIDTH     => DATA_WIDTH,
         BMEM_ITEMS     => BMEM_ITEMS,
         BFIFO_ITEMS    => BFIFO_ITEMS,
         RESERVED_ITEMS => RESERVED_ITEMS
      )
      port map(
         CLK         => CLK,
         RESET       => RESET,
         -- Write interface
         DATA_IN     => trimmer_tx_data,
         WE          => bmem_ctrl_we,
         IS_DATA     => dec_payload,
         EOF         => bmem_ctrl_eof,
         FREE_BLOCK  => FREE_PACKET,
         FULL        => bmem_ctrl_full,
         READY       => bmem_ctrl_ready,
         OFFSET      => bmem_ctrl_offset,
         -- BlockRAM interface
         BMEM_DATA   => BMEM_DATA,
         BMEM_ADDR   => BMEM_ADDR,
         BMEM_WE     => BMEM_WE
      );

   -- mapping FrameLink decoder
   FL_DEC_I : entity work.FL_DEC
      generic map(
         HEADER      => HEADER,
         FOOTER      => FOOTER
      )
      port map(
         CLK         => CLK,
         RESET       => RESET,
         -- FrameLink interface
         SOF_N       => trimmer_tx_sof_n,
         SOP_N       => trimmer_tx_sop_n,
         EOP_N       => trimmer_tx_eop_n,
         EOF_N       => trimmer_tx_eof_n,
         SRC_RDY_N   => trimmer_tx_src_rdy_n,
         DST_RDY_N   => trimmer_tx_dst_rdy_n,
         -- decoder signals
         SOF         => dec_sof,
         SOHDR       => open,
         EOHDR       => open,
         HDR_FRAME   => open,
         SOPLD       => open,
         EOPLD       => dec_eopld,
         PLD_FRAME   => dec_payload,
         SOFTR       => open,
         EOFTR       => open,
         FTR_FRAME   => open,
         EOF         => dec_eof,
         SRC_RDY     => dec_src_rdy,
         DST_RDY     => dec_dst_rdy
      );

end architecture full;
