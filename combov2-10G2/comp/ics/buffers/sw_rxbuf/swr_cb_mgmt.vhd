-- swr_cb_mgmt.vhd: Control Bus management unit
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
entity SWR_CB_MGMT is
   generic (
      COUNT          : integer;     -- number of connected SW_RXBUFs
      RX_ADDR_WIDTH  : integer := 21 -- SW_RXBUF address width
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

      -- SW_RXBUF Control Bus interface
      CTRL_OFFSET    : in  std_logic_vector(COUNT*20-1 downto 0);
      CTRL_LENGTH    : in  std_logic_vector(COUNT*12-1 downto 0);
      CTRL_IFC       : in  std_logic_vector(3 downto 0);
      INFO_READY     : in  std_logic_vector(COUNT-1 downto 0);
      ACK            : out std_logic_vector(COUNT-1 downto 0);
      FREE_PACKET    : out std_logic_vector(COUNT-1 downto 0)
   );
end entity SWR_CB_MGMT;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of SWR_CB_MGMT is

   -- ------------------ Constants declaration --------------------------------
   constant OFFSET_WIDTH   : integer := 28;
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
   signal cnt_msg_rst      : std_logic;
   
   -- registers
   
   -- (de)multiplexers
   signal mx_length        : std_logic_vector(LENGTH_WIDTH-1 downto 0);
   signal mx_offset        : std_logic_vector(20-1 downto 0);
   signal mx_ifc           : std_logic_vector(IFC_WIDTH-1 downto 0);
   signal mx_info_ready    : std_logic_vector(log2(1) downto 0);
   signal mx_data          : std_logic_vector(15 downto 0);
   signal dmx_ack          : std_logic_vector(COUNT-1 downto 0);
   signal dmx_free_packet  : std_logic_vector(COUNT-1 downto 0);
   signal dmx_free_packet_sel : std_logic_vector(abs(log2(COUNT)-1) downto 0);
   signal dmx_free_packet_in : std_logic_vector(log2(1) downto 0);
   signal dmx_ack_in       : std_logic_vector(log2(1) downto 0);
   
   -- FIFO signals
   signal fifo_di          : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal fifo_full        : std_logic;
   signal fifo_do          : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal fifo_empty       : std_logic;
   signal fifo_rrq         : std_logic;
   signal fifo_wrq         : std_logic;

   -- prepared data
   signal data0            : std_logic_vector(15 downto 0);
   signal data1            : std_logic_vector(15 downto 0);
   signal data2            : std_logic_vector(15 downto 0);
  
   -- others
   signal cnt_msg_max      : std_logic;
   signal cmp_dns_type     : std_logic;
   signal free_packet_i    : std_logic;

   -- aliases
   alias fifo_do_ifc       : std_logic_vector(IFC_WIDTH-1 downto 0) is
                           fifo_do(IFC_WIDTH-1 downto 0);
   alias fifo_do_offset    : std_logic_vector(OFFSET_WIDTH-1 downto 0) is
                           fifo_do(IFC_WIDTH+OFFSET_WIDTH-1 downto IFC_WIDTH);
   alias fifo_do_length    : std_logic_vector(LENGTH_WIDTH-1 downto 0) is
                           fifo_do(FIFO_WIDTH-1 downto IFC_WIDTH+OFFSET_WIDTH);
begin
   -- directly mapped signals -------------------------------------------------
   dmx_ack_in(0)  <= not fifo_full;
   dmx_free_packet_in(0) <= free_packet_i;
   fifo_wrq       <= mx_info_ready(0);
   
   fifo_rrq       <= (cnt_msg(1) and (not cnt_msg(0))) and UPS_DST_RDY;
   cnt_msg_ce     <= (UPS_DST_RDY and (not fifo_empty)) or cnt_msg_max;
   cnt_msg_max    <= cnt_msg(1) and cnt_msg(0);
   free_packet_i  <= DNS_SRC_RDY and cmp_dns_type;
   
   -- output interface signals mapping
   ACK            <= dmx_ack;
   FREE_PACKET    <= dmx_free_packet;
   UPS_DATA       <= mx_data;
   UPS_SRC_RDY    <= not fifo_empty;
   UPS_SOP        <= cnt_msg(1) nor cnt_msg(0);       -- cnt_msg == "00"
   UPS_EOP        <= cnt_msg(1) and (not cnt_msg(0)); -- cnt_msg == "10"
   DNS_DST_RDY    <= '1';

   -- FIFO input
   fifo_di(IFC_WIDTH-1 downto 0)  <= mx_ifc;                         -- IFC
   fifo_di(FIFO_WIDTH-1 downto IFC_WIDTH+OFFSET_WIDTH) <= mx_length; -- LENGTH

   -- generate offset for one attached SW_RXBUF
   GEN_FIFO_DI1: if COUNT = 1 generate
      fifo_di(IFC_WIDTH+20-1 downto IFC_WIDTH)  <= mx_offset;
      fifo_di(IFC_WIDTH+OFFSET_WIDTH-1 downto IFC_WIDTH+20) <= (others => '0');
   end generate;
   
   -- generate offset for more attached SW_RXBUFs
   GEN_FIFO_DI2: if COUNT > 1 generate
      fifo_di(IFC_WIDTH+20-1 downto IFC_WIDTH)  <= mx_offset;
      fifo_di(IFC_WIDTH+RX_ADDR_WIDTH-1 downto IFC_WIDTH+20)  <= (others => '0');
      fifo_di(IFC_WIDTH+RX_ADDR_WIDTH+log2(COUNT)-1 
         downto IFC_WIDTH+RX_ADDR_WIDTH) <= cnt_device;
      fifo_di(IFC_WIDTH+OFFSET_WIDTH-1 
         downto IFC_WIDTH+RX_ADDR_WIDTH+log2(COUNT)) <= (others => '0');
   end generate;

   -- forming output data into correct sequence
   -- 0 : 11..0  : length
   --     15..12 : type
   data0(11 downto 0)   <= fifo_do_length;
   data0(15 downto 12)  <= "0000";
   -- 1 : 11..0 : offset(27..16)
   --      3..0 : flags (IFC ID)
   data1(11 downto 0)   <= fifo_do_offset(27 downto 16);
   data1(15 downto 12)  <= fifo_do_ifc;
   -- 2 : 15..0 : offset(15..0)
   data2(15 downto 0)   <= fifo_do_offset(15 downto 0);

   -- ------------------ comparator cmp_dns_type ------------------------------
   cmp_dns_typep: process (DNS_DATA)
   begin
      if DNS_DATA(15 downto 12) = "0000" then 
         cmp_dns_type  <= '1';
      else
         cmp_dns_type  <= '0';
      end if;
   end process;
   
   -- Output data multiplexer -------------------------------------------------
   mx_datap: process( cnt_msg, data0, data1, data2 )
   begin
      case cnt_msg is
         when "00"  => mx_data <= data0;
         when "01"  => mx_data <= data1;
         when "10"  => mx_data <= data2;
         when others => mx_data <= (others => '0');
      end case;
   end process;

   -- gen signals when COUNT > 1 ----------------------------------------------
   GEN_FULL_UNIT : if (COUNT > 1) generate
      
      dmx_free_packet_sel <= DNS_DATA(8+log2(COUNT)-1 downto 8);
      
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
   
      -- input multiplexers ---------------------------------------------------
      -- offset multiplexer
      MX_OFFSET_I: entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => 20,
         MUX_WIDTH   => COUNT
      )
      port map(
         DATA_IN  => CTRL_OFFSET,
         SEL      => cnt_device,
         DATA_OUT => mx_offset
      );

      -- length multiplexer
      MX_LENGTH_I: entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => LENGTH_WIDTH,
         MUX_WIDTH   => COUNT
      )
      port map(
         DATA_IN  => CTRL_LENGTH,
         SEL      => cnt_device,
         DATA_OUT => mx_length
      );

      -- ifc multiplexer
      MX_IFC_I: entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => IFC_WIDTH,
         MUX_WIDTH   => COUNT
      )
      port map(
         DATA_IN  => CTRL_IFC,
         SEL      => cnt_device,
         DATA_OUT => mx_ifc
      );

      -- info_ready multiplexer
      MX_INFO_READY_I: entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => 1,
         MUX_WIDTH   => COUNT
      )
      port map(
         DATA_IN  => INFO_READY,
         SEL      => cnt_device,
         DATA_OUT => mx_info_ready
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

      -- free_packet demultiplexer
      DMX_FREE_PACKET_I: entity work.GEN_DEMUX
      generic map(
         DATA_WIDTH  => 1,
         DEMUX_WIDTH => COUNT
      )
      port map(
         DATA_IN  => dmx_free_packet_in,
         SEL      => dmx_free_packet_sel,
         DATA_OUT => dmx_free_packet
      );

   end generate;

   -- gen signals when COUNT = 1 ----------------------------------------------
   GEN_REDUCED_UNIT : if (COUNT = 1) generate
      mx_offset      <= CTRL_OFFSET;
      mx_length      <= CTRL_LENGTH;
      mx_ifc         <= CTRL_IFC;
      mx_info_ready  <= INFO_READY;
      dmx_ack        <= dmx_ack_in;
      dmx_free_packet<= dmx_free_packet_in;
   end generate;

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

end architecture full;
