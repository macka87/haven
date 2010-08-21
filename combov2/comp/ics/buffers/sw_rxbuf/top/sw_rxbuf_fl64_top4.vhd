-- sw_rxbuf_fl64.vhd: SW RXBuffer cover for 4 SW_RXBUFs
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
entity sw_rxbuf_fl64_top4 is
   generic(
      -- number of items in BlockRAM memory
      -- has to be power of 2 (2, 4, 8, ...)
      BMEM_ITEMS     : integer;
      -- maximal number of blocks in BlockRAM memory
      BMEM_MAX_BLOCKS: integer;
      -- number of items in Control memory
      CTRL_MEM_ITEMS : integer := 16;
      -- reserved space in packet memory before the payload (in Bytes)
      CONTROL_SIZE   : integer;
      -- header is present in payload
      HEADER         : boolean;
      -- footer is present in payload
      FOOTER         : boolean
   ); 
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;
      -- input FrameLink interface
      RX0            : inout t_fl64;
      RX1            : inout t_fl64;
      RX2            : inout t_fl64;
      RX3            : inout t_fl64;
      -- Internal Bus: Read Interface
      RD             : inout t_ibmi_read64s;
      -- remove header before storing frame into memory
      RX_SKIP_HEADER : in  std_logic;
      -- Control bus interface
      -- User Component Upstream Interface
      UPS_FL         : inout t_fl16;
      -- User Component Downstream Interface
      DNS_FL         : inout t_fl16
   );
end entity sw_rxbuf_fl64_top4;

architecture full of sw_rxbuf_fl64_top4 is
   -- ------------------ Constants declaration --------------------------------
   constant COUNT             : integer := 4;
   
   -- ------------------ Signals declaration ----------------------------------
   -- SW_RXBUF Control Bus signals
   signal cb_ctrl_offset      : std_logic_vector(COUNT*20-1 downto 0);
   signal cb_ctrl_length      : std_logic_vector(COUNT*12-1 downto 0);
   signal cb_ctrl_ifc         : std_logic_vector(COUNT*4-1 downto 0);
   signal cb_info_ready       : std_logic_vector(COUNT-1 downto 0);
   signal cb_ack              : std_logic_vector(COUNT-1 downto 0);
   signal cb_free_packet      : std_logic_vector(COUNT-1 downto 0);

   -- auxiliary signals for de/multiplexing
   signal ib_rx0_rd_sel       : std_logic;
   signal ib_rx1_rd_sel       : std_logic;
   signal ib_rx2_rd_sel       : std_logic;
   signal ib_rx3_rd_sel       : std_logic;
   
   signal ib_rx0_rd_req       : std_logic;
   signal ib_rx1_rd_req       : std_logic;
   signal ib_rx2_rd_req       : std_logic;
   signal ib_rx3_rd_req       : std_logic;

   signal ib_rx0_rd_data      : std_logic_vector(63 downto 0);
   signal ib_rx1_rd_data      : std_logic_vector(63 downto 0);
   signal ib_rx2_rd_data      : std_logic_vector(63 downto 0);
   signal ib_rx3_rd_data      : std_logic_vector(63 downto 0);

   signal ib_rx0_rd_ardy      : std_logic;
   signal ib_rx1_rd_ardy      : std_logic;
   signal ib_rx2_rd_ardy      : std_logic;
   signal ib_rx3_rd_ardy      : std_logic;
   
   signal ib_rx0_rd_src_rdy   : std_logic;
   signal ib_rx1_rd_src_rdy   : std_logic;
   signal ib_rx2_rd_src_rdy   : std_logic;
   signal ib_rx3_rd_src_rdy   : std_logic;

begin

   -- select signals
   ib_rx0_rd_sel  <= '1' when RD.ADDR(22 downto 21) = "00" else '0';
   ib_rx1_rd_sel  <= '1' when RD.ADDR(22 downto 21) = "01" else '0';
   ib_rx2_rd_sel  <= '1' when RD.ADDR(22 downto 21) = "10" else '0';
   ib_rx3_rd_sel  <= '1' when RD.ADDR(22 downto 21) = "11" else '0';
   
   -- read request signals
   ib_rx0_rd_req  <= RD.REQ when ib_rx0_rd_sel = '1' else '0';
   ib_rx1_rd_req  <= RD.REQ when ib_rx1_rd_sel = '1' else '0';
   ib_rx2_rd_req  <= RD.REQ when ib_rx2_rd_sel = '1' else '0';
   ib_rx3_rd_req  <= RD.REQ when ib_rx3_rd_sel = '1' else '0';
   
   -- data out multiplexing
   RD.DATA        <= ib_rx0_rd_data when ib_rx0_rd_sel = '1' else
                     ib_rx1_rd_data when ib_rx1_rd_sel = '1' else
                     ib_rx2_rd_data when ib_rx2_rd_sel = '1' else
                     ib_rx3_rd_data;
   
   -- ardy multiplexing
   RD.ARDY        <= ib_rx0_rd_ardy when ib_rx0_rd_sel = '1' else
                     ib_rx1_rd_ardy when ib_rx1_rd_sel = '1' else
                     ib_rx2_rd_ardy when ib_rx2_rd_sel = '1' else
                     ib_rx3_rd_ardy;

   -- src_rdy multiplexing
   RD.SRC_RDY     <= ib_rx0_rd_src_rdy when ib_rx0_rd_sel = '1' else
                     ib_rx1_rd_src_rdy when ib_rx1_rd_sel = '1' else
                     ib_rx2_rd_src_rdy when ib_rx2_rd_sel = '1' else
                     ib_rx3_rd_src_rdy;

   -- SW_RXBUF 0 --------------------------------------------------------------
   SW_RXBUF_FL64_0_I: entity work.sw_rxbuf(full)
      generic map(
         DATA_WIDTH     => 64,
         BMEM_ITEMS     => BMEM_ITEMS,
         BMEM_MAX_BLOCKS=> BMEM_MAX_BLOCKS,
         CTRL_MEM_ITEMS => CTRL_MEM_ITEMS,
         CONTROL_SIZE   => CONTROL_SIZE,
         HEADER         => HEADER,
         FOOTER         => FOOTER
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
   
         -- Internal Bus: Read Interface
         RD_ADDR        => RD.ADDR,
         RD_BE          => RD.BE,
         RD_REQ         => ib_rx0_rd_req,
         RD_ARDY        => ib_rx0_rd_ardy,
         RD_SOF_IN      => RD.SOF_IN,
         RD_EOF_IN      => RD.EOF_IN,
         -- Output Interface
         RD_DATA        => ib_rx0_rd_data,
         RD_SRC_RDY     => ib_rx0_rd_src_rdy,
         RD_DST_RDY     => RD.DST_RDY,
   
         -- input FrameLink interface
         RX_SOF_N       => RX0.SOF_N,
         RX_SOP_N       => RX0.SOP_N,
         RX_EOP_N       => RX0.EOP_N,
         RX_EOF_N       => RX0.EOF_N,
         RX_SRC_RDY_N   => RX0.SRC_RDY_N,
         RX_DST_RDY_N   => RX0.DST_RDY_N,
         RX_DATA        => RX0.DATA,
         RX_REM         => RX0.DREM,

         -- remove header before storing frame into memory
         RX_SKIP_HEADER => RX_SKIP_HEADER,
   
         -- control bus interface
         CTRL_OFFSET    => cb_ctrl_offset((0+1)*20-1 downto 0*20),
         CTRL_LENGTH    => cb_ctrl_length((0+1)*12-1 downto 0*12),
         CTRL_IFC       => cb_ctrl_ifc((0+1)*4-1 downto 0*4),
         INFO_READY     => cb_info_ready(0),
         ACK            => cb_ack(0),
         FREE_PACKET    => cb_free_packet(0)
      );
   
   -- SW_RXBUF 1 --------------------------------------------------------------
   SW_RXBUF_FL64_1_I: entity work.sw_rxbuf(full)
      generic map(
         DATA_WIDTH     => 64,
         BMEM_ITEMS     => BMEM_ITEMS,
         BMEM_MAX_BLOCKS=> BMEM_MAX_BLOCKS,
         CTRL_MEM_ITEMS => CTRL_MEM_ITEMS,
         CONTROL_SIZE   => CONTROL_SIZE,
         HEADER         => HEADER,
         FOOTER         => FOOTER
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
   
         -- Internal Bus: Read Interface
         RD_ADDR        => RD.ADDR,
         RD_BE          => RD.BE,
         RD_REQ         => ib_rx1_rd_req,
         RD_ARDY        => ib_rx1_rd_ardy,
         RD_SOF_IN      => RD.SOF_IN,
         RD_EOF_IN      => RD.EOF_IN,
         -- Output Interface
         RD_DATA        => ib_rx1_rd_data,
         RD_SRC_RDY     => ib_rx1_rd_src_rdy,
         RD_DST_RDY     => RD.DST_RDY,
   
         -- input FrameLink interface
         RX_SOF_N       => RX1.SOF_N,
         RX_SOP_N       => RX1.SOP_N,
         RX_EOP_N       => RX1.EOP_N,
         RX_EOF_N       => RX1.EOF_N,
         RX_SRC_RDY_N   => RX1.SRC_RDY_N,
         RX_DST_RDY_N   => RX1.DST_RDY_N,
         RX_DATA        => RX1.DATA,
         RX_REM         => RX1.DREM,

         -- remove header before storing frame into memory
         RX_SKIP_HEADER => RX_SKIP_HEADER,
   
         -- control bus interface
         CTRL_OFFSET    => cb_ctrl_offset((1+1)*20-1 downto 1*20),
         CTRL_LENGTH    => cb_ctrl_length((1+1)*12-1 downto 1*12),
         CTRL_IFC       => cb_ctrl_ifc((1+1)*4-1 downto 1*4),
         INFO_READY     => cb_info_ready(1),
         ACK            => cb_ack(1),
         FREE_PACKET    => cb_free_packet(1)
      );
   
   -- SW_RXBUF 2 --------------------------------------------------------------
   SW_RXBUF_FL64_2_I: entity work.sw_rxbuf(full)
      generic map(
         DATA_WIDTH     => 64,
         BMEM_ITEMS     => BMEM_ITEMS,
         BMEM_MAX_BLOCKS=> BMEM_MAX_BLOCKS,
         CTRL_MEM_ITEMS => CTRL_MEM_ITEMS,
         CONTROL_SIZE   => CONTROL_SIZE,
         HEADER         => HEADER,
         FOOTER         => FOOTER
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
   
         -- Internal Bus: Read Interface
         RD_ADDR        => RD.ADDR,
         RD_BE          => RD.BE,
         RD_REQ         => ib_rx2_rd_req,
         RD_ARDY        => ib_rx2_rd_ardy,
         RD_SOF_IN      => RD.SOF_IN,
         RD_EOF_IN      => RD.EOF_IN,
         -- Output Interface
         RD_DATA        => ib_rx2_rd_data,
         RD_SRC_RDY     => ib_rx2_rd_src_rdy,
         RD_DST_RDY     => RD.DST_RDY,
   
         -- input FrameLink interface
         RX_SOF_N       => RX2.SOF_N,
         RX_SOP_N       => RX2.SOP_N,
         RX_EOP_N       => RX2.EOP_N,
         RX_EOF_N       => RX2.EOF_N,
         RX_SRC_RDY_N   => RX2.SRC_RDY_N,
         RX_DST_RDY_N   => RX2.DST_RDY_N,
         RX_DATA        => RX2.DATA,
         RX_REM         => RX2.DREM,

         -- remove header before storing frame into memory
         RX_SKIP_HEADER => RX_SKIP_HEADER,
   
         -- control bus interface
         CTRL_OFFSET    => cb_ctrl_offset((2+1)*20-1 downto 2*20),
         CTRL_LENGTH    => cb_ctrl_length((2+1)*12-1 downto 2*12),
         CTRL_IFC       => cb_ctrl_ifc((2+1)*4-1 downto 2*4),
         INFO_READY     => cb_info_ready(2),
         ACK            => cb_ack(2),
         FREE_PACKET    => cb_free_packet(2)
      );
   
   -- SW_RXBUF 3 --------------------------------------------------------------
   SW_RXBUF_FL64_3_I: entity work.sw_rxbuf(full)
      generic map(
         DATA_WIDTH     => 64,
         BMEM_ITEMS     => BMEM_ITEMS,
         BMEM_MAX_BLOCKS=> BMEM_MAX_BLOCKS,
         CTRL_MEM_ITEMS => CTRL_MEM_ITEMS,
         CONTROL_SIZE   => CONTROL_SIZE,
         HEADER         => HEADER,
         FOOTER         => FOOTER
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
   
         -- Internal Bus: Read Interface
         RD_ADDR        => RD.ADDR,
         RD_BE          => RD.BE,
         RD_REQ         => ib_rx3_rd_req,
         RD_ARDY        => ib_rx3_rd_ardy,
         RD_SOF_IN      => RD.SOF_IN,
         RD_EOF_IN      => RD.EOF_IN,
         -- Output Interface
         RD_DATA        => ib_rx3_rd_data,
         RD_SRC_RDY     => ib_rx3_rd_src_rdy,
         RD_DST_RDY     => RD.DST_RDY,
   
         -- input FrameLink interface
         RX_SOF_N       => RX3.SOF_N,
         RX_SOP_N       => RX3.SOP_N,
         RX_EOP_N       => RX3.EOP_N,
         RX_EOF_N       => RX3.EOF_N,
         RX_SRC_RDY_N   => RX3.SRC_RDY_N,
         RX_DST_RDY_N   => RX3.DST_RDY_N,
         RX_DATA        => RX3.DATA,
         RX_REM         => RX3.DREM,

         -- remove header before storing frame into memory
         RX_SKIP_HEADER => RX_SKIP_HEADER,
   
         -- control bus interface
         CTRL_OFFSET    => cb_ctrl_offset((3+1)*20-1 downto 3*20),
         CTRL_LENGTH    => cb_ctrl_length((3+1)*12-1 downto 3*12),
         CTRL_IFC       => cb_ctrl_ifc((3+1)*4-1 downto 3*4),
         INFO_READY     => cb_info_ready(3),
         ACK            => cb_ack(3),
         FREE_PACKET    => cb_free_packet(3)
      );
   
   -- CB Management Unit ------------------------------------------------------
   SWR_CB_MGMT_I : entity work.SWR_CB_MGMT_FL16
      generic map(
         COUNT          => COUNT
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- Control Bus interface
         -- User Component Upstream Interface
         UPS_FL         => UPS_FL,
         -- User Component Downstream Interface
         DNS_FL         => DNS_FL,
         -- SW_RXBUF Control Bus interface
         CTRL_OFFSET    => cb_ctrl_offset,
         CTRL_LENGTH    => cb_ctrl_length,
         CTRL_IFC       => cb_ctrl_ifc,
         INFO_READY     => cb_info_ready,
         ACK            => cb_ack,
         FREE_PACKET    => cb_free_packet
      );

end architecture full; 

