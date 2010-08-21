-- sw_1rx_4tx_buf_nocb.vhd: 1 SW_RXBUFs and 4 SW_TXBUFs cover (without CB)
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
use work.math_pack.all;
use work.fl_pkg.all;
use work.ib_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity SW_1RX_4TX_BUF_NOCB is
   generic(
      -- common generics ------------------------------------------------------
      -- if true FULL architecture of SW_RXBUF will be used
      FULL_SW_RXBUF        : boolean := true;
      -- if true FULL architecture of SW_RXBUF will be used
      FULL_SW_TXBUF        : boolean := true;
      -- SW_TXBUFs generics ---------------------------------------------------
      -- number of items in BlockRAM memory
      TX_BMEM_ITEMS        : integer;
      -- number of items in Control memory
      TX_CTRL_MEM_ITEMS    : integer := 16;
      -- Control data length (in bytes)
      TX_CONTROL_DATA_LENGTH : integer;
      -- send constant HW header for every outcoming packet
      TX_CONSTANT_HW_HEADER_LENGTH : integer := 0;
      -- constant HW header data in Bytes (max 8 Bytes) - for each SW_TXBUF
      TX_CONSTANT_HW_HEADER_DATA0 : std_logic_vector(63 downto 0) := X"0000000000000000";
      TX_CONSTANT_HW_HEADER_DATA1 : std_logic_vector(63 downto 0) := X"0000000000000000";
      TX_CONSTANT_HW_HEADER_DATA2 : std_logic_vector(63 downto 0) := X"0000000000000000";
      TX_CONSTANT_HW_HEADER_DATA3 : std_logic_vector(63 downto 0) := X"0000000000000000";
      -- SW_RXBUF generics ----------------------------------------------------
      -- number of items in BlockRAM memory
      -- has to be power of 2 (2, 4, 8, ...)
      RX_BMEM_ITEMS        : integer;
      -- maximal number of blocks in BlockRAM memory
      RX_BMEM_MAX_BLOCKS   : integer;
      -- number of items in Control memory
      RX_CTRL_MEM_ITEMS    : integer := 16;
      -- reserved space in packet memory before the payload (in Bytes)
      RX_CONTROL_SIZE      : integer;
      -- header is present in payload
      RX_HEADER            : boolean;
      -- footer is present in payload
      RX_FOOTER            : boolean
   ); 
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;
      -- Input interface
      RX             : inout t_fl64;
      -- Output interface
      TX0            : inout t_fl16;
      TX1            : inout t_fl16;
      TX2            : inout t_fl16;
      TX3            : inout t_fl16;
      -- Internal Bus: Write Interface
      WR             : inout t_ibmi_write64;
      -- Internal Bus: Read Interface
      RD             : inout t_ibmi_read64s;
      -- remove header before storing frame into memory
      RX_SKIP_HEADER : in  std_logic;
      -- PDMA Interface
      -- SW_RXBUF
      -- Output:
      RX_PKT_OFFSET  : out std_logic_vector(19 downto 0);
      RX_PKT_LENGTH  : out std_logic_vector(11 downto 0);
      RX_PKT_IFC     : out std_logic_vector(3 downto 0);
      RX_PKT_READY   : out std_logic;  -- packet information is ready
      RX_PKT_ACK     : in  std_logic;  -- record has been read
      -- Input:
      RX_PKT_FREE    : in  std_logic;   -- free oldest packet in memory

      -- SW_TXBUF 0
      -- Output:
      TX0_PKT_SENT     : out std_logic;
      TX0_PKT_SENT_ACK : in  std_logic;
      -- Input:
      TX0_PKT_OFFSET   : in  std_logic_vector(19 downto 0);
      TX0_PKT_LENGTH   : in  std_logic_vector(11 downto 0);
      TX0_PKT_WRITE    : in  std_logic;
      TX0_PKT_READY    : out std_logic;

      -- -- SW_TXBUF 1
      -- Output:
      TX1_PKT_SENT     : out std_logic;
      TX1_PKT_SENT_ACK : in  std_logic;
      -- Input:
      TX1_PKT_OFFSET   : in  std_logic_vector(19 downto 0);
      TX1_PKT_LENGTH   : in  std_logic_vector(11 downto 0);
      TX1_PKT_WRITE    : in  std_logic;
      TX1_PKT_READY    : out std_logic;

      -- -- SW_TXBUF 2
      -- Output:
      TX2_PKT_SENT     : out std_logic;
      TX2_PKT_SENT_ACK : in  std_logic;
      -- Input:
      TX2_PKT_OFFSET   : in  std_logic_vector(19 downto 0);
      TX2_PKT_LENGTH   : in  std_logic_vector(11 downto 0);
      TX2_PKT_WRITE    : in  std_logic;
      TX2_PKT_READY    : out std_logic;

      -- SW_TXBUF 3
      -- Output:
      TX3_PKT_SENT     : out std_logic;
      TX3_PKT_SENT_ACK : in  std_logic;
      -- Input:
      TX3_PKT_OFFSET   : in  std_logic_vector(19 downto 0);
      TX3_PKT_LENGTH   : in  std_logic_vector(11 downto 0);
      TX3_PKT_WRITE    : in  std_logic;
      TX3_PKT_READY    : out std_logic
   );
end entity SW_1RX_4TX_BUF_NOCB;

architecture full of SW_1RX_4TX_BUF_NOCB is

   -- ------------------ Signals declaration ----------------------------------
   -- auxiliary signals for de/multiplexing
   signal ib_rx_rd_sel        : std_logic;
   signal ib_tx_rd_sel        : std_logic;

   -- IB read interface signals
   signal ib_rx_rd_req        : std_logic;
   signal ib_tx_rd_req        : std_logic;

   signal ib_rx_rd_data       : std_logic_vector(63 downto 0);
   signal ib_tx_rd_data       : std_logic_vector(63 downto 0);

   signal ib_rx_rd_ardy       : std_logic;
   signal ib_tx_rd_ardy       : std_logic;
   
   signal ib_rx_rd_src_rdy    : std_logic;
   signal ib_tx_rd_src_rdy    : std_logic;

   -- auxiliary records
   signal sw_rx_rd            : t_ibmi_read64s;
   signal sw_tx_rd            : t_ibmi_read64s;
   
begin
   -- select signals
   ib_rx_rd_sel  <= not RD.ADDR(23);
   ib_tx_rd_sel  <= RD.ADDR(23);

   -- read request signals
   ib_rx_rd_req  <= RD.REQ and ib_rx_rd_sel;
   ib_tx_rd_req  <= RD.REQ and ib_tx_rd_sel;
   
   -- data out multiplexing
   rd_datap: process( ib_rx_rd_sel, ib_tx_rd_data, ib_rx_rd_data )
   begin
      case ib_rx_rd_sel is
         when '0' => RD.DATA <= ib_tx_rd_data;
         when '1' => RD.DATA <= ib_rx_rd_data;
         when others => RD.DATA <= (others => 'X');
      end case;
   end process;
   
   -- ardy multiplexing
   rd_ardyp: process( ib_rx_rd_sel, ib_rx_rd_ardy, ib_tx_rd_ardy )
   begin
      case ib_rx_rd_sel is
         when '0' => RD.ARDY <= ib_tx_rd_ardy;
         when '1' => RD.ARDY <= ib_rx_rd_ardy;
         when others => RD.ARDY <= 'X';
      end case;
   end process;

   -- src_rdy multiplexing
   rd_src_rdyp: process( ib_rx_rd_sel, ib_rx_rd_src_rdy, ib_tx_rd_src_rdy )
   begin
      case ib_rx_rd_sel is
         when '0' => RD.SRC_RDY <= ib_tx_rd_src_rdy;
         when '1' => RD.SRC_RDY <= ib_rx_rd_src_rdy;
         when others => RD.SRC_RDY <= 'X';
      end case;
   end process;
   
   -- create auxiliary RD records for components
   sw_rx_rd.ADDR(20 downto 0)  <= RD.ADDR(20 downto 0);
   sw_rx_rd.ADDR(31 downto 21) <= (others => '0');
   sw_rx_rd.BE          <= RD.BE;
   sw_rx_rd.REQ         <= ib_rx_rd_req;
   ib_rx_rd_ardy        <= sw_rx_rd.ARDY;
   sw_rx_rd.SOF_IN      <= RD.SOF_IN;
   sw_rx_rd.EOF_IN      <= RD.EOF_IN;
   ib_rx_rd_data        <= sw_rx_rd.DATA;
   ib_rx_rd_src_rdy     <= sw_rx_rd.SRC_RDY;
   sw_rx_rd.DST_RDY     <= RD.DST_RDY;

   sw_tx_rd.ADDR(22 downto 0)  <= RD.ADDR(22 downto 0);
   sw_tx_rd.ADDR(31 downto 23) <= (others => '0');
   sw_tx_rd.BE          <= RD.BE;
   sw_tx_rd.REQ         <= ib_tx_rd_req;
   ib_tx_rd_ardy        <= sw_tx_rd.ARDY;
   sw_tx_rd.SOF_IN      <= RD.SOF_IN;
   sw_tx_rd.EOF_IN      <= RD.EOF_IN;
   ib_tx_rd_data        <= sw_tx_rd.DATA;
   ib_tx_rd_src_rdy     <= sw_tx_rd.SRC_RDY;
   sw_tx_rd.DST_RDY     <= RD.DST_RDY;

   -- SW_RXBUF cover mapping --------------------------------------------------
   GEN_FULL_RX : if FULL_SW_RXBUF generate
      SW_RXBUF_FL64_I : entity work.SW_RXBUF_FL64_NOCB(full)
         generic map(
            BMEM_ITEMS     => RX_BMEM_ITEMS,
            BMEM_MAX_BLOCKS => RX_BMEM_MAX_BLOCKS,
            CTRL_MEM_ITEMS => RX_CTRL_MEM_ITEMS,
            CONTROL_SIZE   => RX_CONTROL_SIZE,
            HEADER         => RX_HEADER,
            FOOTER         => RX_FOOTER
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- input FrameLink interface
            RX             => RX,
            -- Internal bus interface
            RD             => sw_rx_rd,
            -- remove header before storing frame into memory
            RX_SKIP_HEADER => RX_SKIP_HEADER,
            -- PDMA Interface
            -- Output:
            RX_PKT_OFFSET  => RX_PKT_OFFSET,
            RX_PKT_LENGTH  => RX_PKT_LENGTH,
            RX_PKT_IFC     => RX_PKT_IFC,
            RX_PKT_READY   => RX_PKT_READY,
            RX_PKT_ACK     => RX_PKT_ACK,
            -- Input:
            RX_PKT_FREE    => RX_PKT_FREE
         );
   end generate;

   GEN_EMPTY_RX : if not FULL_SW_RXBUF generate
      SW_RXBUF_FL64_I : entity work.SW_RXBUF_FL64_NOCB(empty)
         generic map(
            BMEM_ITEMS     => RX_BMEM_ITEMS,
            BMEM_MAX_BLOCKS => RX_BMEM_MAX_BLOCKS,
            CTRL_MEM_ITEMS => RX_CTRL_MEM_ITEMS,
            CONTROL_SIZE   => RX_CONTROL_SIZE,
            HEADER         => RX_HEADER,
            FOOTER         => RX_FOOTER
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- input FrameLink interface
            RX             => RX,
            -- Internal bus interface
            RD             => sw_rx_rd,
            -- remove header before storing frame into memory
            RX_SKIP_HEADER => RX_SKIP_HEADER,
            -- PDMA Interface
            -- Output:
            RX_PKT_OFFSET  => RX_PKT_OFFSET,
            RX_PKT_LENGTH  => RX_PKT_LENGTH,
            RX_PKT_IFC     => RX_PKT_IFC,
            RX_PKT_READY   => RX_PKT_READY,
            RX_PKT_ACK     => RX_PKT_ACK,
            -- Input:
            RX_PKT_FREE    => RX_PKT_FREE
         );
   end generate;

   -- 4 SW_TXBUFs cover mapping -----------------------------------------------
   GEN_FULL_TX : if FULL_SW_TXBUF generate
      SW_TXBUF_FL16_TOP4_I : entity work.SW_TXBUF_FL16_TOP4_NOCB(full)
         generic map(
            -- number of items in BlockRAM memory
            BMEM_ITEMS     => TX_BMEM_ITEMS,
            -- number of items in Control memory
            CTRL_MEM_ITEMS => TX_CTRL_MEM_ITEMS,
            -- Control data length (in bytes)
            CONTROL_DATA_LENGTH => TX_CONTROL_DATA_LENGTH,
            -- send constant HW header for every outcomming packet
            CONSTANT_HW_HEADER_LENGTH => TX_CONSTANT_HW_HEADER_LENGTH,
            -- constant HW header data in Bytes (max 8 Bytes) - for each SW_TXBUF
            CONSTANT_HW_HEADER_DATA0 => TX_CONSTANT_HW_HEADER_DATA0,
            CONSTANT_HW_HEADER_DATA1 => TX_CONSTANT_HW_HEADER_DATA1,
            CONSTANT_HW_HEADER_DATA2 => TX_CONSTANT_HW_HEADER_DATA2,
            CONSTANT_HW_HEADER_DATA3 => TX_CONSTANT_HW_HEADER_DATA3
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- input interface
            TX0            => TX0,
            TX1            => TX1,
            TX2            => TX2,
            TX3            => TX3,
            -- Internal Bus: Write Interface
            WR             => WR,
            -- Internal Bus: Read Interface
            RD             => sw_tx_rd,
            -- PDMA Interface - TX0
            -- Output:
            TX0_PKT_SENT     => TX0_PKT_SENT,
            TX0_PKT_SENT_ACK => TX0_PKT_SENT_ACK,
            -- Input:
            TX0_PKT_OFFSET   => TX0_PKT_OFFSET,
            TX0_PKT_LENGTH   => TX0_PKT_LENGTH,
            TX0_PKT_WRITE    => TX0_PKT_WRITE,
            TX0_PKT_READY    => TX0_PKT_READY,
            -- PDMA Interface - TX1
            -- Output:
            TX1_PKT_SENT     => TX1_PKT_SENT,
            TX1_PKT_SENT_ACK => TX1_PKT_SENT_ACK,
            -- Input:
            TX1_PKT_OFFSET   => TX1_PKT_OFFSET,
            TX1_PKT_LENGTH   => TX1_PKT_LENGTH,
            TX1_PKT_WRITE    => TX1_PKT_WRITE,
            TX1_PKT_READY    => TX1_PKT_READY,
            -- PDMA Interface - TX2
            -- Output:
            TX2_PKT_SENT     => TX2_PKT_SENT,
            TX2_PKT_SENT_ACK => TX2_PKT_SENT_ACK,
            -- Input:
            TX2_PKT_OFFSET   => TX2_PKT_OFFSET,
            TX2_PKT_LENGTH   => TX2_PKT_LENGTH,
            TX2_PKT_WRITE    => TX2_PKT_WRITE,
            TX2_PKT_READY    => TX2_PKT_READY,
            -- PDMA Interface - TX3
            -- Output:
            TX3_PKT_SENT     => TX3_PKT_SENT,
            TX3_PKT_SENT_ACK => TX3_PKT_SENT_ACK,
            -- Input:
            TX3_PKT_OFFSET   => TX3_PKT_OFFSET,
            TX3_PKT_LENGTH   => TX3_PKT_LENGTH,
            TX3_PKT_WRITE    => TX3_PKT_WRITE,
            TX3_PKT_READY    => TX3_PKT_READY
         );
   end generate;

   GEN_EMPTY_TX : if not FULL_SW_TXBUF generate
      TX0.SRC_RDY_N  <= '1';
      TX1.SRC_RDY_N  <= '1';
      TX2.SRC_RDY_N  <= '1';
      TX3.SRC_RDY_N  <= '1';
      
      WR.RDY         <= '0';
      sw_tx_rd.ARDY  <= '0';
      sw_tx_rd.SRC_RDY  <= '0';
      TX0_PKT_SENT   <= '0';
      TX0_PKT_READY  <= '0';
      TX1_PKT_SENT   <= '0';
      TX1_PKT_READY  <= '0';
      TX2_PKT_SENT   <= '0';
      TX2_PKT_READY  <= '0';
      TX3_PKT_SENT   <= '0';
      TX3_PKT_READY  <= '0';
   end generate;

end architecture full; 

