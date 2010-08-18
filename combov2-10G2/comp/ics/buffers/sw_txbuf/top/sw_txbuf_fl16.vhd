-- sw_txbuf_fl16.vhd: SW TXBuffer cover
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
entity SW_TXBUF_FL16 is
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
      -- constant HW header data in Bytes (maximaly 8 Bytes)
      CONSTANT_HW_HEADER_DATA : std_logic_vector(63 downto 0) 
                     := X"0000000000000000"
   ); 
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;
      -- input interface
      TX             : inout t_fl16;
      -- Internal Bus: Write Interface
      WR             : inout t_ibmi_write64;
      -- Internal Bus: Read Interface
      RD             : inout t_ibmi_read64s;
      -- Control bus interface
      -- User Component Upstream Interface
      UPS_FL         : inout t_fl16;
      -- User Component Downstream Interface
      DNS_FL         : inout t_fl16
   );
end entity SW_TXBUF_FL16;

architecture full of SW_TXBUF_FL16 is
   
   -- ------------------ Signals declaration ----------------------------------
   signal cb_diff             : std_logic_vector(
                                log2(CTRL_MEM_ITEMS) downto 0);
   signal cb_ready            : std_logic_vector(log2(1) downto 0);
   signal cb_ack              : std_logic_vector(log2(1) downto 0);
   signal cb_ctrl_offset      : std_logic_vector(19 downto 0);
   signal cb_ctrl_length      : std_logic_vector(11 downto 0);
   signal cb_ctrl_ready       : std_logic_vector(log2(1) downto 0);
   signal cb_ctrl_write       : std_logic_vector(log2(1) downto 0);

begin

   SW_TXBUF_FL64_I: entity work.sw_txbuf(full)
      generic map(
         DATA_WIDTH          => 64,
         OUTPUT_WIDTH        => 16,
         BMEM_ITEMS          => BMEM_ITEMS,
         CTRL_MEM_ITEMS      => CTRL_MEM_ITEMS,
         CONTROL_DATA_LENGTH => CONTROL_DATA_LENGTH,
         CONSTANT_HW_HEADER_LENGTH => CONSTANT_HW_HEADER_LENGTH,
         CONSTANT_HW_HEADER_DATA => CONSTANT_HW_HEADER_DATA
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
   
         -- Output FrameLink interface
         SOF_N          => TX.SOF_N,
         SOP_N          => TX.SOP_N,
         EOP_N          => TX.EOP_N,
         EOF_N          => TX.EOF_N,
         SRC_RDY_N      => TX.SRC_RDY_N,
         DST_RDY_N      => TX.DST_RDY_N,
         DATA_OUT       => TX.DATA,
         REM_OUT        => TX.DREM,
   
         -- Internal Bus: Write Interface
         WR_ADDR        => WR.ADDR,
         WR_DATA        => WR.DATA,
         WR_BE          => WR.BE,
         WR_REQ         => WR.REQ,
         WR_RDY         => WR.RDY,
         WR_LENGTH      => WR.LENGTH,
         WR_SOF         => WR.SOF,
         WR_EOF         => WR.EOF,
         -- Internal Bus: Read Interface
         -- Input Interface
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
   
         -- control bus interface
         DIFF           => cb_diff,
         READY          => cb_ready(0),
         ACK            => cb_ack(0),
         CTRL_OFFSET    => cb_ctrl_offset,
         CTRL_LENGTH    => cb_ctrl_length,
         CTRL_READY     => cb_ctrl_ready(0),
         CTRL_WRITE     => cb_ctrl_write(0)
      );

   SWT_CB_MGMT_I : entity work.SWT_CB_MGMT_FL16
      generic map(
         COUNT          => 1,
         CTRL_MEM_ITEMS => CTRL_MEM_ITEMS
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- Control Bus interface
         -- User Component Upstream Interface
         UPS_FL         => UPS_FL,
         -- User Component Downstream Interface
         DNS_FL         => DNS_FL,
         -- SW_TXBUF Control Bus interface
         DIFF           => cb_diff,
         READY          => cb_ready,
         ACK            => cb_ack,
         CTRL_OFFSET    => cb_ctrl_offset,
         CTRL_LENGTH    => cb_ctrl_length,
         CTRL_READY     => cb_ctrl_ready,
         CTRL_WRITE     => cb_ctrl_write
      );

end architecture full; 

