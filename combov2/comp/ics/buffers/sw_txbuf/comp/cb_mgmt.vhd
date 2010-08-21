-- swt_cb_mgmt.vhd: Control Bus management unit
-- Copyright (C) 2006 CESNET
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
entity SWT_CB_MGMT is
   generic (
      -- number of connected SW_TXBUFs
      COUNT          : integer;
      -- number of items in SW_TXBUF Control memory
      CTRL_MEM_ITEMS : integer := 16
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;
      
      -- Control Bus interface
      -- User Component Upstream Interface
      UPS_DATA       : out std_logic_vector(15 downto 0);
      UPS_SOP        : out std_logic;
      UPS_EOP        : out std_logic;
      UPS_SRC_RDY    : out std_logic;
      UPS_DST_RDY    : in  std_logic;
      -- User Component Downstream Interface
      DNS_DATA       : in  std_logic_vector(15 downto 0);
      DNS_SOP        : in  std_logic;
      DNS_EOP        : in  std_logic;
      DNS_SRC_RDY    : in  std_logic;
      DNS_DST_RDY    : out std_logic;

      -- SW_RTBUF Control Bus interface
      DIFF           : in  std_logic_vector(COUNT*(log2(CTRL_MEM_ITEMS)+1)-1 
                       downto 0);
      READY          : in  std_logic_vector(COUNT-1 downto 0);
      ACK            : out std_logic_vector(COUNT-1 downto 0);
      CTRL_OFFSET    : out std_logic_vector(19 downto 0);
      CTRL_LENGTH    : out std_logic_vector(11 downto 0);
      CTRL_READY     : in  std_logic_vector(COUNT-1 downto 0);
      CTRL_WRITE     : out std_logic_vector(COUNT-1 downto 0)
   );
end entity SWT_CB_MGMT;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of SWT_CB_MGMT is

   -- ------------------ Constants declaration --------------------------------
   constant OFFSET_WIDTH   : integer := 20;
   constant LENGTH_WIDTH   : integer := 12;
   constant IFC_WIDTH      : integer := 4;
   constant FIFO_WIDTH     : integer := IFC_WIDTH + OFFSET_WIDTH + 
                                        LENGTH_WIDTH;
   constant CMP_MSG        : std_logic_vector(1 downto 0) := "11";

   -- ------------------ Signals declaration ----------------------------------
   -- counters
   signal cnt_device       : std_logic_vector(abs(log2(COUNT)-1) downto 0);
   signal cnt_msg          : std_logic_vector(1 downto 0);
   signal cnt_msg_ce       : std_logic;
   
   -- registers
   signal reg_length       : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal reg_length_we    : std_logic;
   signal reg_offset1      : std_logic_vector(15 downto 0);
   signal reg_offset1_we   : std_logic;
   signal reg_offset2      : std_logic_vector(3 downto 0);
   signal reg_offset2_we   : std_logic;
   signal reg_ifc          : std_logic_vector(IFC_WIDTH-1 downto 0);
   signal reg_ifc_we       : std_logic;
   signal reg_fifo_do      : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal reg_write        : std_logic;
   
   -- (de)multiplexers
   signal dmx_reg_we       : std_logic_vector(3 downto 0);
   signal dmx_reg_we_in    : std_logic_vector(log2(1) downto 0);
   signal dmx_ctrl_write   : std_logic_vector(COUNT-1 downto 0);
   signal dmx_ctrl_write_in : std_logic_vector(log2(1) downto 0);
   signal mx_ctrl_ready    : std_logic_vector(log2(1) downto 0);
   signal mx_ready         : std_logic_vector(log2(1) downto 0);
   signal dmx_ack          : std_logic_vector(COUNT-1 downto 0);
   signal dmx_ack_in       : std_logic_vector(log2(1) downto 0);

   -- FIFO signals
   -- input FIFO for Control memory records
   signal fifo_di          : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal fifo_full        : std_logic;
   signal fifo_do          : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal fifo_empty       : std_logic;
   signal fifo_rrq         : std_logic;
   signal fifo_wrq         : std_logic;
   -- output FIFO (for IFC_IDs)
   signal fifo2_di         : std_logic_vector(IFC_WIDTH-1 downto 0);
   signal fifo2_full       : std_logic;
   signal fifo2_do         : std_logic_vector(IFC_WIDTH-1 downto 0);
   signal fifo2_empty      : std_logic;
   signal fifo2_rrq        : std_logic;
   signal fifo2_wrq        : std_logic;

   -- others
   signal cnt_msg_max      : std_logic;
   signal dns_dst_rdy_i    : std_logic;
   signal ifc_id           : std_logic_vector(abs(log2(COUNT)-1) downto 0);
   signal output_data      : std_logic_vector(15 downto 0);
   signal dns_eop_valid    : std_logic;

   -- aliases
   alias fifo_do_ifc       : std_logic_vector(IFC_WIDTH-1 downto 0) is
                           reg_fifo_do(IFC_WIDTH-1 downto 0);
   alias fifo_do_offset    : std_logic_vector(OFFSET_WIDTH-1 downto 0) is
                           reg_fifo_do(IFC_WIDTH+OFFSET_WIDTH-1 downto IFC_WIDTH);
   alias fifo_do_length    : std_logic_vector(LENGTH_WIDTH-1 downto 0) is
                           reg_fifo_do(FIFO_WIDTH-1 downto IFC_WIDTH+OFFSET_WIDTH);
begin
   -- directly mapped signals -------------------------------------------------
   dns_dst_rdy_i        <= not fifo_full;
   dmx_reg_we_in(0)     <= (DNS_SRC_RDY and dns_dst_rdy_i) or cnt_msg_max;
   dmx_ctrl_write_in(0) <= (not fifo_empty) and mx_ctrl_ready(0) 
                           and (not reg_write);
   dmx_ack_in(0)        <= not fifo2_full;
   dns_eop_valid        <= (DNS_SRC_RDY and dns_dst_rdy_i) and DNS_EOP;
   
   -- mapping output data
   output_data(7 downto 0)  <= X"00";     -- reserved
   output_data(11 downto 8) <= fifo2_do;  -- flags (ifc id)
   output_data(15 downto 12) <= X"0";     -- type = 0
   
   -- FIFO control signals
   fifo_di(IFC_WIDTH-1 downto 0)  <= reg_ifc;
   fifo_di(IFC_WIDTH+OFFSET_WIDTH-1 downto IFC_WIDTH)  
                                  <= reg_offset2 & reg_offset1;
   fifo_di(FIFO_WIDTH-1 downto IFC_WIDTH+OFFSET_WIDTH) <= reg_length;
   
   fifo_wrq       <= dmx_reg_we(3);
   fifo_rrq       <= mx_ctrl_ready(0) and (not reg_write);
   fifo2_wrq      <= mx_ready(0);
   fifo2_rrq      <= UPS_DST_RDY;
   
   -- registers' control signals
   reg_length_we  <= dmx_reg_we(0);
   reg_ifc_we     <= dmx_reg_we(1);
   reg_offset2_we <= dmx_reg_we(1);
   reg_offset1_we <= dmx_reg_we(2);

   -- counters' control signals
   cnt_msg_ce     <= (DNS_SRC_RDY and dns_dst_rdy_i) or cnt_msg_max;
   
   -- output interface signals mapping
   DNS_DST_RDY    <= dns_dst_rdy_i;

   UPS_DATA       <= output_data;
   UPS_SOP        <= '1';
   UPS_EOP        <= '1';
   UPS_SRC_RDY    <= not fifo2_empty;

   CTRL_OFFSET    <= fifo_do_offset;
   CTRL_LENGTH    <= fifo_do_length;
   CTRL_WRITE     <= dmx_ctrl_write;

   ACK            <= dmx_ack;
   
   -- ------------------ comparator cnt_msg_max -------------------------------
   cnt_msg_maxp: process (cnt_msg, dns_eop_valid)
   begin
      if cnt_msg = "11" or dns_eop_valid = '1' then 
         cnt_msg_max  <= '1';
      else
         cnt_msg_max  <= '0';
      end if;
   end process;
   
   -- gen signals when COUNT > 1 ----------------------------------------------
   GEN_FULL_UNIT : if (COUNT > 1) generate
      fifo2_di(log2(COUNT)-1 downto 0) <= cnt_device;
      fifo2_di(IFC_WIDTH-1 downto log2(COUNT)) <= (others => '0');
	  ifc_id               <= fifo_do_ifc(log2(COUNT)-1 downto 0);
      
      -- ------------------ counter cnt_device --------------------------------
      cnt_devicep: process (CLK)
      begin
         if CLK='1' and CLK'event then
            if RESET = '1' then 
               cnt_device <= (others => '0');
            else
               cnt_device <= cnt_device + 1;
            end if;
         end if;
      end process;
      
      -- output (de)multiplexers ----------------------------------------------
      -- dmx_ctrl_write_we demultiplexer
      DMX_CTRL_WRITE_I: entity work.GEN_DEMUX
      generic map(
         DATA_WIDTH  => 1,
         DEMUX_WIDTH => COUNT
      )
      port map(
         DATA_IN(0) => reg_write,
         SEL      => ifc_id,
         DATA_OUT => dmx_ctrl_write
      );

      -- ctrl_ready multiplexer
      MX_CTRL_READY_I: entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => 1,
         MUX_WIDTH   => COUNT
      )
      port map(
         DATA_IN  => CTRL_READY,
         SEL      => ifc_id,
         DATA_OUT => mx_ctrl_ready
      );
      
      -- input (de)multiplexers -----------------------------------------------
      -- ready multiplexer
      MX_READY_I: entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => 1,
         MUX_WIDTH   => COUNT
      )
      port map(
         DATA_IN  => READY,
         SEL      => cnt_device,
         DATA_OUT => mx_ready
      );

      -- ACK demultiplexer
      DMX_ACK_I: entity work.GEN_DEMUX
      generic map(
         DATA_WIDTH  => 1,
         DEMUX_WIDTH => COUNT
      )
      port map(
         DATA_IN  => dmx_ack_in,
         SEL      => cnt_device,
         DATA_OUT => dmx_ack
      );

   end generate;

   -- gen signals when COUNT = 1 ----------------------------------------------
   GEN_REDUCED_UNIT : if (COUNT = 1) generate
      fifo2_di(IFC_WIDTH-1 downto 0) <= "0000";
      dmx_ctrl_write(0) <= reg_write;
      mx_ctrl_ready  <= CTRL_READY;
      mx_ready       <= READY;
      dmx_ack        <= dmx_ack_in;
   end generate;

   -- register reg_length -----------------------------------------------------
   reg_lengthp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (reg_length_we = '1') then
            reg_length <= DNS_DATA(11 downto 0);
         end if;
      end if;
   end process;

   -- register reg_ifc --------------------------------------------------------
   reg_ifcp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (reg_ifc_we = '1') then
            reg_ifc <= DNS_DATA(15 downto 12);
         end if;
      end if;
   end process;

   -- register reg_offset1 ----------------------------------------------------
   reg_offset1p: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (reg_offset1_we = '1') then
            reg_offset1 <= DNS_DATA(15 downto 0);
         end if;
      end if;
   end process;

   -- register reg_offset2 ----------------------------------------------------
   reg_offset2p: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (reg_offset2_we = '1') then
            reg_offset2 <= DNS_DATA(3 downto 0);
         end if;
      end if;
   end process;

   -- register reg_fifo_do ----------------------------------------------------
   reg_fifo_dop: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg_fifo_do <= fifo_do;
      end if;
   end process;

   -- register reg_write ------------------------------------------------------
   reg_writep: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_write <= '0';
         else
            reg_write <= dmx_ctrl_write_in(0);
         end if;
      end if;
   end process;

   -- dmx_reg_we demultiplexer
   DMX_REG_WE_I: entity work.GEN_DEMUX
   generic map(
      DATA_WIDTH  => 1,
      DEMUX_WIDTH => 4
   )
   port map(
      DATA_IN  => dmx_reg_we_in,
      SEL      => cnt_msg,
      DATA_OUT => dmx_reg_we
   );

   -- ------------------ counter cnt_msg --------------------------------------
   cnt_msgp: process (CLK) 
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' then 
            cnt_msg <= (others => '0');
         elsif cnt_msg_ce = '1' then
            cnt_msg <= cnt_msg + 1;
         end if;
      end if;
   end process;
   
   -- input FIFO buffer mapping -----------------------------------------------
   INPUT_BUFFER : entity work.FIFO
      generic map (
         DATA_WIDTH     => FIFO_WIDTH,
         DISTMEM_TYPE   => 16,
         ITEMS          => 16,
         BLOCK_SIZE     => 0
      )
      port map(
         RESET          => RESET,
         CLK            => CLK,
         -- Write interface
         DATA_IN        => fifo_di,
         WRITE_REQ      => fifo_wrq,
         FULL           => fifo_full,
         LSTBLK         => open,
         -- Read interface
         DATA_OUT       => fifo_do,
         READ_REQ       => fifo_rrq,
         EMPTY          => fifo_empty
      );

   -- output FIFO buffer mapping ----------------------------------------------
   OUTPUT_BUFFER : entity work.FIFO
      generic map (
         DATA_WIDTH     => IFC_WIDTH,
         DISTMEM_TYPE   => 16,
         ITEMS          => 16,
         BLOCK_SIZE     => 0
      )
      port map(
         RESET          => RESET,
         CLK            => CLK,
         -- Write interface
         DATA_IN        => fifo2_di,
         WRITE_REQ      => fifo2_wrq,
         FULL           => fifo2_full,
         LSTBLK         => open,
         -- Read interface
         DATA_OUT       => fifo2_do,
         READ_REQ       => fifo2_rrq,
         EMPTY          => fifo2_empty
      );

end architecture full;
