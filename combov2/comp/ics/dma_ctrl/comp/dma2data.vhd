-- dma2data.vhd: Convertor from DMA interface to simple data output
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity DMA2DATA is
   generic(
      -- frame data width in bits
      DMA_DATA_WIDTH : integer
      -- number of DMA2FL units in cover to determine number of bits in 
      -- DMA_TAG, that identify correct DMA2FL
--       DMA_COUNT      : integer
      -- this tag ID is compared with log2(DMA_COUNT) highest bits in
      -- DMA_TAG
--       DMA_TAG_ID     : std_logic;
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interface
      DMA_ADDR       : out std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
      DMA_DOUT       : in  std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
      DMA_REQ        : in  std_logic;
      DMA_ACK        : out std_logic;
      DMA_DONE       : out std_logic;
      DMA_TAG        : out std_logic_vector(15 downto 0);

      -- output interface
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_DATA        : out std_logic_vector(DMA_DATA_WIDTH-1 downto 0);

      -- output tag interface
      TX_DMA_DONE    : in  std_logic;
      TX_DMA_TAG     : in  std_logic_vector(15 downto 0)
   );
end entity DMA2DATA;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of DMA2DATA is

   -- ------------------ Constants declaration --------------------------------
   constant CNT_ADDR_WIDTH       : integer := log2(128/DMA_DATA_WIDTH);
   constant CNT_ADDR_MAX         : std_logic_vector(CNT_ADDR_WIDTH-1 downto 0)
                                 := (others => '1');

   -- ------------------ Signals declaration ----------------------------------
   -- registers
   signal reg_send_packet        : std_logic;
   signal reg_send_packet_we     : std_logic;
   signal reg_packet_sent        : std_logic;
   signal reg_dma_req            : std_logic;

   -- multiplexers

   -- counters
   signal cnt_addr               : std_logic_vector(CNT_ADDR_WIDTH-1 downto 0);
   signal cnt_addr_ce            : std_logic;
   signal cnt_addr_clr           : std_logic;

   -- others
   signal cmp_last_word          : std_logic;
   signal sending_last_word      : std_logic;

begin
   -- ------------------ Directly mapped signals ------------------------------
   cnt_addr_clr      <= '0';
   cnt_addr_ce       <= reg_send_packet and (not TX_DST_RDY_N);
   
   reg_send_packet_we <= DMA_REQ or sending_last_word;
   sending_last_word  <= cmp_last_word and (not TX_DST_RDY_N);

   -- output port mapping
   DMA_ADDR         <= cnt_addr;
   DMA_ACK          <= reg_packet_sent;
   DMA_DONE         <= TX_DMA_DONE;
   DMA_TAG          <= TX_DMA_TAG;
   
   TX_SRC_RDY_N      <= not reg_send_packet;
   TX_DATA           <= DMA_DOUT;

   -- counter cnt_addr 
   cnt_addrp: process(CLK) 
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' or cnt_addr_clr = '1' then
            cnt_addr <= (others => '0');
         elsif cnt_addr_ce = '1' then
            cnt_addr <= cnt_addr + 1;
         end if;
      end if;
   end process;

--    GEN_DMA_WIDTH_LTE_32 : if DMA_DATA_WIDTH <= 8 generate -- dma width is lower then or equals 32
--    -- mux; insert DMA_TAG ID into correct position in data stream
--    dma_tag_insp: process(DMA_DOUT, cnt_addr)
--    begin
--       TX_DATA <= DMA_DOUT;
--       if (((conv_integer(cnt_addr)+1)*DMA_DATA_WIDTH) = 24) then
--          TX_DATA(DMA_DATA_WIDTH) <= DMA_TAG_ID;
--       end if;
--    end process;
-- 
--    end generate;
-- 
-- 
--    GEN_DMA_WIDTH_E_64 : if DMA_DATA_WIDTH = 16 generate -- dma width equals 16
--    -- mux; insert DMA_TAG ID into correct position in data stream
--    dma_tag_insp: process(DMA_DOUT, cnt_addr_ce)
--    begin
--       TX_DATA <= DMA_DOUT;
--       if (conv_integer(cnt_addr) = 1) then
--          TX_DATA(7) <= DMA_TAG_ID;
--       end if;
--    end process;
-- 
--    end generate;
-- 
-- 
--    GEN_DMA_WIDTH_E_64 : if DMA_DATA_WIDTH = 64  or DMA_DATA_WIDTH = 32 generate -- dma width 32, 64
--    -- mux; insert DMA_TAG ID into correct position in data stream
--    dma_tag_insp: process(DMA_DOUT, cnt_addr_ce, cmp_last_word)
--    begin
--       TX_DATA <= DMA_DOUT;
--       if (conv_integer(cnt_addr) = 0) then
--          TX_DATA(23) <= DMA_TAG_ID;
--       end if;
--    end process;
-- 
--    end generate;
-- 

   -- register reg_send_packet - set to '1' when new FrameLink packet should
   -- be created
   reg_send_packetp:process (CLK)
   begin
      if CLK'event and CLK='1' then  
         if RESET='1' then   
            reg_send_packet <= '0';
         elsif (reg_send_packet_we = '1') then
            reg_send_packet <= DMA_REQ and (not sending_last_word);
         end if;
      end if;
   end process;

   -- register reg_packet_sent - set to '1' when new packet has been sent
   reg_packet_sentp:process (CLK)
   begin
      if CLK'event and CLK='1' then  
         reg_packet_sent <= sending_last_word;
      end if;
   end process;

   -- comparator cmp_last_word
   cmp_last_wordp : process (cnt_addr)
   begin
      if (cnt_addr = CNT_ADDR_MAX) then
         cmp_last_word <= '1';
      else
         cmp_last_word <= '0';
      end if;
   end process;

   -- registered DMA_REQ
   reg_dma_reqp: process(CLK, RESET)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reg_dma_req <= '0';
         else
            reg_dma_req <= DMA_REQ;
         end if;
      end if;
   end process;

end architecture full;

