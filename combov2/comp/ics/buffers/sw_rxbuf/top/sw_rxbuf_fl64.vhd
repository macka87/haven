-- sw_rxbuf_fl64.vhd: SW RXBuffer cover for 1 SW_RXBUF
-- Copyright (C) 2006 CESNET
-- Author(s): Jiri Tobola  <tobola@liberouter.org>
--            Martin Kosek <kosek@liberouter.org>
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
entity sw_rxbuf_fl64 is
   generic(
      -- number of items in BlockRAM memory
      -- has to be power of 2 (2, 4, 8, ...)
      BMEM_ITEMS     : integer := 1024;
      -- maximal number of blocks in BlockRAM memory
      BMEM_MAX_BLOCKS: integer := 32;
      -- number of items in Control memory
      CTRL_MEM_ITEMS : integer := 32;
      -- reserved space in packet memory before the payload (in Bytes)
      CONTROL_SIZE   : integer := 2;
      -- header is present in payload
      HEADER         : boolean := true;
      -- footer is present in payload
      FOOTER         : boolean := false
   ); 
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;
      -- Internal Bus: Read Interface
      RD             : inout t_ibmi_read64s;
      -- input FrameLink interface
      RX             : inout t_fl64;
      -- remove header before storing frame into memory
      RX_SKIP_HEADER : in  std_logic;
      -- Control bus interface
      -- User Component Upstream Interface
      UPS_FL         : inout t_fl16;
      -- User Component Downstream Interface
      DNS_FL         : inout t_fl16
   );
end entity sw_rxbuf_fl64;

architecture full of sw_rxbuf_fl64 is

   -- ------------------ Signals declaration ----------------------------------
   -- SW_RXBUF Control Bus signals
   signal cb_ctrl_offset      : std_logic_vector(19 downto 0);
   signal cb_ctrl_length      : std_logic_vector(11 downto 0);
   signal cb_ctrl_ifc         : std_logic_vector(3 downto 0);
   signal cb_info_ready       : std_logic_vector(log2(1) downto 0);
   signal cb_ack              : std_logic_vector(log2(1) downto 0);
   signal cb_free_packet      : std_logic_vector(log2(1) downto 0);
   
begin

   SW_RXBUF_FL64_I: entity work.sw_rxbuf(full)
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
         RD_REQ         => RD.REQ,
         RD_ARDY        => RD.ARDY,
         RD_SOF_IN      => RD.SOF_IN,
         RD_EOF_IN      => RD.EOF_IN,
         -- Output Interface
         RD_DATA        => RD.DATA,
         RD_SRC_RDY     => RD.SRC_RDY,
         RD_DST_RDY     => RD.DST_RDY,
   
         -- input FrameLink interface
         RX_SOF_N       => RX.SOF_N,
         RX_SOP_N       => RX.SOP_N,
         RX_EOP_N       => RX.EOP_N,
         RX_EOF_N       => RX.EOF_N,
         RX_SRC_RDY_N   => RX.SRC_RDY_N,
         RX_DST_RDY_N   => RX.DST_RDY_N,
         RX_DATA        => RX.DATA,
         RX_REM         => RX.DREM,

         -- remove header before storing frame into memory
         RX_SKIP_HEADER => RX_SKIP_HEADER,
   
         -- control bus interface
         CTRL_OFFSET    => cb_ctrl_offset,
         CTRL_LENGTH    => cb_ctrl_length,
         CTRL_IFC       => cb_ctrl_ifc,
         INFO_READY     => cb_info_ready(0),
         ACK            => cb_ack(0),
         FREE_PACKET    => cb_free_packet(0)
      ); 

   SWR_CB_MGMT_I : entity work.SWR_CB_MGMT_FL16
      generic map(
         COUNT          => 1
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

