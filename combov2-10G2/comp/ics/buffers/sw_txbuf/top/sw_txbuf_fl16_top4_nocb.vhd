-- sw_txbuf_fl16_top4.vhd_nocb: SW TXBuffer cover for 4 SW_TXBUFs
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
entity SW_TXBUF_FL16_TOP4_NOCB is
   generic(
      -- number of items in BlockRAM memory
      BMEM_ITEMS     : integer;
      -- number of items in Control memory
      CTRL_MEM_ITEMS : integer := 16;
      -- Control data length (in bytes), which are sent as frame header
      -- this data are located in Packet memory, before the payload itself
      CONTROL_DATA_LENGTH : integer;
      -- send constant HW header for every outcomming packet
      CONSTANT_HW_HEADER_LENGTH : integer := 0;
      -- constant HW header data in Bytes (max 8 Bytes) - for each SW_TXBUF
      CONSTANT_HW_HEADER_DATA0 : std_logic_vector(63 downto 0) := X"0000000000000000";
      CONSTANT_HW_HEADER_DATA1 : std_logic_vector(63 downto 0) := X"0000000000000000";
      CONSTANT_HW_HEADER_DATA2 : std_logic_vector(63 downto 0) := X"0000000000000000";
      CONSTANT_HW_HEADER_DATA3 : std_logic_vector(63 downto 0) := X"0000000000000000"
   ); 
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;
      -- input interface
      TX0            : inout t_fl16;
      TX1            : inout t_fl16;
      TX2            : inout t_fl16;
      TX3            : inout t_fl16;
      -- Internal Bus: Write Interface
      WR             : inout t_ibmi_write64;
      -- Internal Bus: Read Interface
      RD             : inout t_ibmi_read64s;
      -- PDMA Interface - TX0
      -- Output:
      TX0_PKT_SENT     : out std_logic;
      TX0_PKT_SENT_ACK : in  std_logic;
      -- Input:
      TX0_PKT_OFFSET   : in  std_logic_vector(19 downto 0);
      TX0_PKT_LENGTH   : in  std_logic_vector(11 downto 0);
      TX0_PKT_WRITE    : in  std_logic;
      TX0_PKT_READY    : out std_logic;
      -- PDMA Interface - TX1
      -- Output:
      TX1_PKT_SENT     : out std_logic;
      TX1_PKT_SENT_ACK : in  std_logic;
      -- Input:
      TX1_PKT_OFFSET   : in  std_logic_vector(19 downto 0);
      TX1_PKT_LENGTH   : in  std_logic_vector(11 downto 0);
      TX1_PKT_WRITE    : in  std_logic;
      TX1_PKT_READY    : out std_logic;
      -- PDMA Interface - TX2
      -- Output:
      TX2_PKT_SENT     : out std_logic;
      TX2_PKT_SENT_ACK : in  std_logic;
      -- Input:
      TX2_PKT_OFFSET   : in  std_logic_vector(19 downto 0);
      TX2_PKT_LENGTH   : in  std_logic_vector(11 downto 0);
      TX2_PKT_WRITE    : in  std_logic;
      TX2_PKT_READY    : out std_logic;
      -- PDMA Interface - TX3
      -- Output:
      TX3_PKT_SENT     : out std_logic;
      TX3_PKT_SENT_ACK : in  std_logic;
      -- Input:
      TX3_PKT_OFFSET   : in  std_logic_vector(19 downto 0);
      TX3_PKT_LENGTH   : in  std_logic_vector(11 downto 0);
      TX3_PKT_WRITE    : in  std_logic;
      TX3_PKT_READY    : out std_logic
   );
end entity SW_TXBUF_FL16_TOP4_NOCB;

architecture full of SW_TXBUF_FL16_TOP4_NOCB is
   -- ------------------ Constants declaration --------------------------------
   constant COUNT             : integer := 4;

   -- ------------------ Signals declaration ----------------------------------
   -- auxiliary signals for de/multiplexing
   signal ib_tx0_rd_sel       : std_logic;
   signal ib_tx1_rd_sel       : std_logic;
   signal ib_tx2_rd_sel       : std_logic;
   signal ib_tx3_rd_sel       : std_logic;

   signal ib_tx0_wr_sel       : std_logic;
   signal ib_tx1_wr_sel       : std_logic;
   signal ib_tx2_wr_sel       : std_logic;
   signal ib_tx3_wr_sel       : std_logic;

   -- IB read interface
   signal ib_tx0_rd_req       : std_logic;
   signal ib_tx1_rd_req       : std_logic;
   signal ib_tx2_rd_req       : std_logic;
   signal ib_tx3_rd_req       : std_logic;

   signal ib_tx0_rd_data      : std_logic_vector(63 downto 0);
   signal ib_tx1_rd_data      : std_logic_vector(63 downto 0);
   signal ib_tx2_rd_data      : std_logic_vector(63 downto 0);
   signal ib_tx3_rd_data      : std_logic_vector(63 downto 0);

   signal ib_tx0_rd_ardy      : std_logic;
   signal ib_tx1_rd_ardy      : std_logic;
   signal ib_tx2_rd_ardy      : std_logic;
   signal ib_tx3_rd_ardy      : std_logic;
   
   signal ib_tx0_rd_src_rdy   : std_logic;
   signal ib_tx1_rd_src_rdy   : std_logic;
   signal ib_tx2_rd_src_rdy   : std_logic;
   signal ib_tx3_rd_src_rdy   : std_logic;

   -- IB write interface
   signal ib_tx0_wr_rdy       : std_logic;
   signal ib_tx1_wr_rdy       : std_logic;
   signal ib_tx2_wr_rdy       : std_logic;
   signal ib_tx3_wr_rdy       : std_logic;
   
   signal ib_tx0_wr_req       : std_logic;
   signal ib_tx1_wr_req       : std_logic;
   signal ib_tx2_wr_req       : std_logic;
   signal ib_tx3_wr_req       : std_logic;

   signal ib_wr_addr          : std_logic_vector(31 downto 0);

   alias wr_sel               : std_logic_vector(1 downto 0)
                              is WR.ADDR(22 downto 21);
   alias rd_sel               : std_logic_vector(1 downto 0)
                              is RD.ADDR(22 downto 21);

begin

   -- select signals
   ib_tx0_rd_selp: process(rd_sel)
   begin
      if (rd_sel = "00") then
         ib_tx0_rd_sel  <= '1';
      else
         ib_tx0_rd_sel  <= '0';
      end if;
   end process;

   ib_tx1_rd_selp: process(rd_sel)
   begin
      if (rd_sel = "01") then
         ib_tx1_rd_sel  <= '1';
      else
         ib_tx1_rd_sel  <= '0';
      end if;
   end process;

   ib_tx2_rd_selp: process(rd_sel)
   begin
      if (rd_sel = "10") then
         ib_tx2_rd_sel  <= '1';
      else
         ib_tx2_rd_sel  <= '0';
      end if;
   end process;

   ib_tx3_rd_selp: process(rd_sel)
   begin
      if (rd_sel = "11") then
         ib_tx3_rd_sel  <= '1';
      else
         ib_tx3_rd_sel  <= '0';
      end if;
   end process;

   ib_tx0_wr_selp: process(wr_sel)
   begin
      if (wr_sel = "00") then
         ib_tx0_wr_sel  <= '1';
      else
         ib_tx0_wr_sel  <= '0';
      end if;
   end process;

   ib_tx1_wr_selp: process(wr_sel)
   begin
      if (wr_sel = "01") then
         ib_tx1_wr_sel  <= '1';
      else
         ib_tx1_wr_sel  <= '0';
      end if;
   end process;

   ib_tx2_wr_selp: process(wr_sel)
   begin
      if (wr_sel = "10") then
         ib_tx2_wr_sel  <= '1';
      else
         ib_tx2_wr_sel  <= '0';
      end if;
   end process;

   ib_tx3_wr_selp: process(wr_sel)
   begin
      if (wr_sel = "11") then
         ib_tx3_wr_sel  <= '1';
      else
         ib_tx3_wr_sel  <= '0';
      end if;
   end process;
   
   -- read request signals
   ib_tx0_rd_req  <= RD.REQ and ib_tx0_rd_sel;
   ib_tx1_rd_req  <= RD.REQ and ib_tx1_rd_sel;
   ib_tx2_rd_req  <= RD.REQ and ib_tx2_rd_sel;
   ib_tx3_rd_req  <= RD.REQ and ib_tx3_rd_sel;
   
   -- write request signals
   ib_tx0_wr_req  <= WR.REQ and ib_tx0_wr_sel;
   ib_tx1_wr_req  <= WR.REQ and ib_tx1_wr_sel;
   ib_tx2_wr_req  <= WR.REQ and ib_tx2_wr_sel;
   ib_tx3_wr_req  <= WR.REQ and ib_tx3_wr_sel;

   
   -- data out multiplexing
   rd_datap: process( rd_sel, ib_tx0_rd_data, ib_tx1_rd_data, ib_tx2_rd_data, 
                      ib_tx3_rd_data )
   begin
      case rd_sel is
         when "00" => RD.DATA <= ib_tx0_rd_data;
         when "01" => RD.DATA <= ib_tx1_rd_data;
         when "10" => RD.DATA <= ib_tx2_rd_data;
         when "11" => RD.DATA <= ib_tx3_rd_data;
         when others => RD.DATA <= (others => 'X');
      end case;
   end process;
   
   -- ardy multiplexing
   rd_ardyp: process( rd_sel, ib_tx0_rd_ardy, ib_tx1_rd_ardy, ib_tx2_rd_ardy, 
                      ib_tx3_rd_ardy )
   begin
      case rd_sel is
         when "00" => RD.ARDY <= ib_tx0_rd_ardy;
         when "01" => RD.ARDY <= ib_tx1_rd_ardy;
         when "10" => RD.ARDY <= ib_tx2_rd_ardy;
         when "11" => RD.ARDY <= ib_tx3_rd_ardy;
         when others => RD.ARDY <= 'X';
      end case;
   end process;

   -- src_rdy multiplexing
   rd_src_rdyp: process( rd_sel, ib_tx0_rd_src_rdy, ib_tx1_rd_src_rdy, 
                         ib_tx2_rd_src_rdy, ib_tx3_rd_src_rdy )
   begin
      case rd_sel is
         when "00" => RD.SRC_RDY <= ib_tx0_rd_src_rdy;
         when "01" => RD.SRC_RDY <= ib_tx1_rd_src_rdy;
         when "10" => RD.SRC_RDY <= ib_tx2_rd_src_rdy;
         when "11" => RD.SRC_RDY <= ib_tx3_rd_src_rdy;
         when others => RD.SRC_RDY <= 'X';
      end case;
   end process;
   
   -- wr_rdy multiplexing
   wr_rdyp: process( wr_sel, ib_tx0_wr_rdy, ib_tx1_wr_rdy, ib_tx2_wr_rdy, 
                     ib_tx3_wr_rdy )
   begin
      case wr_sel is
         when "00" => WR.RDY <= ib_tx0_wr_rdy;
         when "01" => WR.RDY <= ib_tx1_wr_rdy;
         when "10" => WR.RDY <= ib_tx2_wr_rdy;
         when "11" => WR.RDY <= ib_tx3_wr_rdy;
         when others => WR.RDY <= 'X';
      end case;
   end process;

   -- address creating
   ib_wr_addr(20 downto 0)  <=  WR.ADDR(20 downto 0);
   ib_wr_addr(31 downto 21) <= (others => '0');
   
   -- SW_TXBUF 0 --------------------------------------------------------------
   SW_TXBUF_FL64_0_I: entity work.sw_txbuf(full)
      generic map(
         DATA_WIDTH          => 64,
         OUTPUT_WIDTH        => 16,
         BMEM_ITEMS          => BMEM_ITEMS,
         CTRL_MEM_ITEMS      => CTRL_MEM_ITEMS,
         CONTROL_DATA_LENGTH => CONTROL_DATA_LENGTH,
         CONSTANT_HW_HEADER_LENGTH => CONSTANT_HW_HEADER_LENGTH,
         CONSTANT_HW_HEADER_DATA => CONSTANT_HW_HEADER_DATA0
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
   
         -- Output FrameLink interface
         SOF_N          => TX0.SOF_N,
         SOP_N          => TX0.SOP_N,
         EOP_N          => TX0.EOP_N,
         EOF_N          => TX0.EOF_N,
         SRC_RDY_N      => TX0.SRC_RDY_N,
         DST_RDY_N      => TX0.DST_RDY_N,
         DATA_OUT       => TX0.DATA,
         REM_OUT        => TX0.DREM,
   
         -- Internal Bus: Write Interface
         WR_ADDR        => ib_wr_addr,
         WR_DATA        => WR.DATA,
         WR_BE          => WR.BE,
         WR_REQ         => ib_tx0_wr_req,
         WR_RDY         => ib_tx0_wr_rdy,
         WR_LENGTH      => WR.LENGTH,
         WR_SOF         => WR.SOF,
         WR_EOF         => WR.EOF,
         -- Internal Bus: Read Interface
         RD_ADDR        => RD.ADDR,
         RD_BE          => RD.BE,
         RD_REQ         => ib_tx0_rd_req,
         RD_ARDY        => ib_tx0_rd_ardy,
         RD_SOF_IN      => RD.SOF_IN,
         RD_EOF_IN      => RD.EOF_IN,
         -- Output Interface
         RD_DATA        => ib_tx0_rd_data,
         RD_SRC_RDY     => ib_tx0_rd_src_rdy,
         RD_DST_RDY     => RD.DST_RDY,
   
         -- control bus interface
         DIFF           => open,
         READY          => TX0_PKT_SENT,
         ACK            => TX0_PKT_SENT_ACK,
         CTRL_OFFSET    => TX0_PKT_OFFSET,
         CTRL_LENGTH    => TX0_PKT_LENGTH,
         CTRL_READY     => TX0_PKT_READY,
         CTRL_WRITE     => TX0_PKT_WRITE
      );

   -- SW_TXBUF 1 --------------------------------------------------------------
   SW_TXBUF_FL64_1_I: entity work.sw_txbuf(full)
      generic map(
         DATA_WIDTH          => 64,
         OUTPUT_WIDTH        => 16,
         BMEM_ITEMS          => BMEM_ITEMS,
         CTRL_MEM_ITEMS      => CTRL_MEM_ITEMS,
         CONTROL_DATA_LENGTH => CONTROL_DATA_LENGTH,
         CONSTANT_HW_HEADER_LENGTH => CONSTANT_HW_HEADER_LENGTH,
         CONSTANT_HW_HEADER_DATA => CONSTANT_HW_HEADER_DATA1
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
   
         -- Output FrameLink interface
         SOF_N          => TX1.SOF_N,
         SOP_N          => TX1.SOP_N,
         EOP_N          => TX1.EOP_N,
         EOF_N          => TX1.EOF_N,
         SRC_RDY_N      => TX1.SRC_RDY_N,
         DST_RDY_N      => TX1.DST_RDY_N,
         DATA_OUT       => TX1.DATA,
         REM_OUT        => TX1.DREM,
   
         -- Internal Bus: Write Interface
         WR_ADDR        => ib_wr_addr,
         WR_DATA        => WR.DATA,
         WR_BE          => WR.BE,
         WR_REQ         => ib_tx1_wr_req,
         WR_RDY         => ib_tx1_wr_rdy,
         WR_LENGTH      => WR.LENGTH,
         WR_SOF         => WR.SOF,
         WR_EOF         => WR.EOF,
         -- Internal Bus: Read Interface
         RD_ADDR        => RD.ADDR,
         RD_BE          => RD.BE,
         RD_REQ         => ib_tx1_rd_req,
         RD_ARDY        => ib_tx1_rd_ardy,
         RD_SOF_IN      => RD.SOF_IN,
         RD_EOF_IN      => RD.EOF_IN,
         -- Output Interface
         RD_DATA        => ib_tx1_rd_data,
         RD_SRC_RDY     => ib_tx1_rd_src_rdy,
         RD_DST_RDY     => RD.DST_RDY,
   
         -- control bus interface
         DIFF           => open,
         READY          => TX1_PKT_SENT,
         ACK            => TX1_PKT_SENT_ACK,
         CTRL_OFFSET    => TX1_PKT_OFFSET,
         CTRL_LENGTH    => TX1_PKT_LENGTH,
         CTRL_READY     => TX1_PKT_READY,
         CTRL_WRITE     => TX1_PKT_WRITE
      );
      
   -- SW_TXBUF 2 --------------------------------------------------------------
   SW_TXBUF_FL64_2_I: entity work.sw_txbuf(full)
      generic map(
         DATA_WIDTH          => 64,
         OUTPUT_WIDTH        => 16,
         BMEM_ITEMS          => BMEM_ITEMS,
         CTRL_MEM_ITEMS      => CTRL_MEM_ITEMS,
         CONTROL_DATA_LENGTH => CONTROL_DATA_LENGTH,
         CONSTANT_HW_HEADER_LENGTH => CONSTANT_HW_HEADER_LENGTH,
         CONSTANT_HW_HEADER_DATA => CONSTANT_HW_HEADER_DATA2
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
   
         -- Output FrameLink interface
         SOF_N          => TX2.SOF_N,
         SOP_N          => TX2.SOP_N,
         EOP_N          => TX2.EOP_N,
         EOF_N          => TX2.EOF_N,
         SRC_RDY_N      => TX2.SRC_RDY_N,
         DST_RDY_N      => TX2.DST_RDY_N,
         DATA_OUT       => TX2.DATA,
         REM_OUT        => TX2.DREM,
   
         -- Internal Bus: Write Interface
         WR_ADDR        => ib_wr_addr,
         WR_DATA        => WR.DATA,
         WR_BE          => WR.BE,
         WR_REQ         => ib_tx2_wr_req,
         WR_RDY         => ib_tx2_wr_rdy,
         WR_LENGTH      => WR.LENGTH,
         WR_SOF         => WR.SOF,
         WR_EOF         => WR.EOF,
         -- Internal Bus: Read Interface
         RD_ADDR        => RD.ADDR,
         RD_BE          => RD.BE,
         RD_REQ         => ib_tx2_rd_req,
         RD_ARDY        => ib_tx2_rd_ardy,
         RD_SOF_IN      => RD.SOF_IN,
         RD_EOF_IN      => RD.EOF_IN,
         -- Output Interface
         RD_DATA        => ib_tx2_rd_data,
         RD_SRC_RDY     => ib_tx2_rd_src_rdy,
         RD_DST_RDY     => RD.DST_RDY,
   
         -- control bus interface
         DIFF           => open,
         READY          => TX2_PKT_SENT,
         ACK            => TX2_PKT_SENT_ACK,
         CTRL_OFFSET    => TX2_PKT_OFFSET,
         CTRL_LENGTH    => TX2_PKT_LENGTH,
         CTRL_READY     => TX2_PKT_READY,
         CTRL_WRITE     => TX2_PKT_WRITE
      );
      
   -- SW_TXBUF 3 --------------------------------------------------------------
   SW_TXBUF_FL64_3_I: entity work.sw_txbuf(full)
      generic map(
         DATA_WIDTH          => 64,
         OUTPUT_WIDTH        => 16,
         BMEM_ITEMS          => BMEM_ITEMS,
         CTRL_MEM_ITEMS      => CTRL_MEM_ITEMS,
         CONTROL_DATA_LENGTH => CONTROL_DATA_LENGTH,
         CONSTANT_HW_HEADER_LENGTH => CONSTANT_HW_HEADER_LENGTH,
         CONSTANT_HW_HEADER_DATA => CONSTANT_HW_HEADER_DATA3
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
   
         -- Output FrameLink interface
         SOF_N          => TX3.SOF_N,
         SOP_N          => TX3.SOP_N,
         EOP_N          => TX3.EOP_N,
         EOF_N          => TX3.EOF_N,
         SRC_RDY_N      => TX3.SRC_RDY_N,
         DST_RDY_N      => TX3.DST_RDY_N,
         DATA_OUT       => TX3.DATA,
         REM_OUT        => TX3.DREM,
   
         -- Internal Bus: Write Interface
         WR_ADDR        => ib_wr_addr,
         WR_DATA        => WR.DATA,
         WR_BE          => WR.BE,
         WR_REQ         => ib_tx3_wr_req,
         WR_RDY         => ib_tx3_wr_rdy,
         WR_LENGTH      => WR.LENGTH,
         WR_SOF         => WR.SOF,
         WR_EOF         => WR.EOF,
         -- Internal Bus: Read Interface
         RD_ADDR        => RD.ADDR,
         RD_BE          => RD.BE,
         RD_REQ         => ib_tx3_rd_req,
         RD_ARDY        => ib_tx3_rd_ardy,
         RD_SOF_IN      => RD.SOF_IN,
         RD_EOF_IN      => RD.EOF_IN,
         -- Output Interface
         RD_DATA        => ib_tx3_rd_data,
         RD_SRC_RDY     => ib_tx3_rd_src_rdy,
         RD_DST_RDY     => RD.DST_RDY,
   
         -- control bus interface
         DIFF           => open,
         READY          => TX3_PKT_SENT,
         ACK            => TX3_PKT_SENT_ACK,
         CTRL_OFFSET    => TX3_PKT_OFFSET,
         CTRL_LENGTH    => TX3_PKT_LENGTH,
         CTRL_READY     => TX3_PKT_READY,
         CTRL_WRITE     => TX3_PKT_WRITE
      );

end architecture full; 

