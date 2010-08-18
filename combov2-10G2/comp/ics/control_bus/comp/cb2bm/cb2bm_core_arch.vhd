--
-- cb2bm_core_arch.vhd: CB2BM component CORE architecture
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


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of CB2BM_CORE is

   -- ------------------ Constants declaration --------------------------------
   constant OFFSET_WIDTH   : integer := 20;
   constant LENGTH_WIDTH   : integer := 12;
   constant IFC_WIDTH      : integer := 4;
   constant FIFO_WIDTH     : integer := IFC_WIDTH + OFFSET_WIDTH + 
                                        LENGTH_WIDTH;
   constant CMP_MSG        : std_logic_vector(1 downto 0) := "11";                                        
  
   -- ------------------ Components declaration -------------------------------
   component FIFO is
      generic (
         -- Set data width here
         DATA_WIDTH     : integer;

         -- Distributed RAM type, only 16, 32, 64 bits
         DISTMEM_TYPE   : integer := 16;

         -- Set number of items in FIFO here
         ITEMS          : integer;

         -- for last block identification
         BLOCK_SIZE     : integer := 0
      );
      port(
         RESET    : in std_logic;  -- Global reset signal
         CLK      : in std_logic;  -- Global clock signal

         -- Write interface
         DATA_IN  : in std_logic_vector((DATA_WIDTH-1) downto 0);
         WRITE_REQ: in std_logic;  -- Write request
         FULL     : out std_logic; -- FIFO is full
         LSTBLK   : out std_logic; -- Last block identifier
   
         -- Read interface
         DATA_OUT : out std_logic_vector((DATA_WIDTH-1) downto 0);
         READ_REQ : in std_logic;  -- Read request
         EMPTY    : out std_logic  -- FIFO is empty
      );
   end component FIFO;

   -- ------------------ Signals declaration ----------------------------------
   -- counters
   signal cnt_msg          : std_logic_vector(2 downto 0);
   signal cnt_msg_ce       : std_logic;
   signal cnt_msg_max      : std_logic;
   signal cnt_requests     : std_logic_vector(3 downto 0);
   signal cnt_requests_ce  : std_logic;
   signal cnt_requests_dir : std_logic;
   signal cnt_requests_max : std_logic;
   signal cnt_requests_min : std_logic;

   -- registers
   signal reg_req_rdy      : std_logic;
   signal reg_req_rdy_we   : std_logic;
   signal reg_tag          : std_logic_vector(11 downto 0);
   signal reg_tag_we       : std_logic;
   signal reg_type         : std_logic_vector(3 downto 0);
   signal reg_type_we      : std_logic;
   signal reg_length       : std_logic_vector(11 downto 0);
   signal reg_length_we    : std_logic;
   signal reg_laddr0       : std_logic_vector(15 downto 0);
   signal reg_laddr0_we    : std_logic;
   signal reg_laddr1       : std_logic_vector(15 downto 0);
   signal reg_laddr1_we    : std_logic;
   signal reg_gaddr0       : std_logic_vector(15 downto 0);
   signal reg_gaddr0_we    : std_logic;
   signal reg_gaddr1       : std_logic_vector(15 downto 0);
   signal reg_gaddr1_we    : std_logic;
   signal reg_gaddr2       : std_logic_vector(15 downto 0);
   signal reg_gaddr2_we    : std_logic;
   signal reg_gaddr3       : std_logic_vector(15 downto 0);
   signal reg_gaddr3_we    : std_logic;

   -- (de)multiplexers
   signal dmx_reg_we       : std_logic_vector(7 downto 0);
   signal dmx_reg_we_in    : std_logic_vector(log2(1) downto 0);

   -- FIFO signals
   signal fifo_di          : std_logic_vector(15 downto 0);
   signal fifo_do          : std_logic_vector(15 downto 0);
   signal fifo_empty       : std_logic;
   signal fifo_rrq         : std_logic;
   signal fifo_wrq         : std_logic;

   -- others
   signal dns_dst_rdy_i    : std_logic;
   signal output_data      : std_logic_vector(15 downto 0);
   signal req_sent         : std_logic;
   signal req_done         : std_logic;

begin
   -- directly mapped signals -------------------------------------------------
   dns_dst_rdy_i        <= not (cnt_requests_max or reg_req_rdy);
   dmx_reg_we_in(0)     <= DNS_SRC_RDY and dns_dst_rdy_i;
   req_sent       <= cnt_msg_max and cnt_msg_ce;
   req_done       <= OP_DONE;

   -- mapping output data
   output_data    <= fifo_do;
   
   -- FIFO control signals
   fifo_rrq       <= UPS_DST_RDY;
   fifo_wrq       <= OP_DONE;
   fifo_di        <= OP_TAG;
   
   -- registers' control signals
   reg_req_rdy_we <= (DNS_SRC_RDY and (not reg_req_rdy)) or ACK;
   reg_tag_we     <= dmx_reg_we(0);
   reg_type_we    <= dmx_reg_we(0);
   reg_length_we  <= dmx_reg_we(1);
   reg_laddr0_we  <= dmx_reg_we(2);
   reg_laddr1_we  <= dmx_reg_we(3);
   reg_gaddr0_we  <= dmx_reg_we(4);
   reg_gaddr1_we  <= dmx_reg_we(5);
   reg_gaddr2_we  <= dmx_reg_we(6);
   reg_gaddr3_we  <= dmx_reg_we(7);

   -- counters' control signals
   cnt_msg_ce     <= DNS_SRC_RDY and dns_dst_rdy_i;
   cnt_msg_max    <= '1' when cnt_msg = "111" else '0';
   cnt_requests_ce  <= (req_sent xor req_done) and 
                       not (cnt_requests_min and req_done);
   cnt_requests_dir <= req_sent;
   cnt_requests_max <= '1' when cnt_requests = "1111" else '0';
   cnt_requests_min <= '1' when cnt_requests = "0000" else '0';
   
   -- output interface signals
   UPS_DATA       <= output_data;
   UPS_SOP        <= '1';
   UPS_EOP        <= '1';
   UPS_SRC_RDY    <= not fifo_empty;
   
   DNS_DST_RDY    <= dns_dst_rdy_i;

   GLOBAL_ADDR    <= reg_gaddr3 & reg_gaddr2 & reg_gaddr1 & reg_gaddr0;
   LOCAL_ADDR     <= reg_laddr1 & reg_laddr0;
   LENGTH         <= reg_length;
   TAG            <= reg_type & reg_tag;
   -- -------------------------------
   -- DIR            <= reg_type(1);
   TRANS_TYPE(0)  <= reg_type(1);
   TRANS_TYPE(1)  <= '0'; -- TODO: nahradit signalem co prijde po kontrolni  sbernici
   -- -------------------------------
   REQ            <= reg_req_rdy;

   -- dmx_ctrl_write_we demultiplexer
   DMX_REG_WE_I: entity work.GEN_DEMUX
   generic map(
      DATA_WIDTH  => 1,
      DEMUX_WIDTH => 8
   )
   port map(
      DATA_IN  => dmx_reg_we_in,
      SEL      => cnt_msg,
      DATA_OUT => dmx_reg_we
   );

   -- register reg_req_rdy ----------------------------------------------------
   reg_req_rdyp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_req_rdy <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (reg_req_rdy_we = '1') then
            reg_req_rdy <= (cnt_msg_max and cnt_msg_ce) and 
                           not (reg_req_rdy and ACK);
         end if;
      end if;
   end process;

   -- ------------------ counter cnt_msg --------------------------------------
   cnt_msgp: process (CLK, RESET) 
   begin
      if RESET = '1' then 
         cnt_msg <= (others => '0');
      elsif CLK='1' and CLK'event then
         if cnt_msg_ce = '1' then
            cnt_msg <= cnt_msg + 1;
         end if;
      end if;
   end process;
   
   -- ------------------ counter cnt_requests ---------------------------------
   cnt_requestsp: process (CLK, RESET) 
   begin
      if RESET = '1' then 
         cnt_requests <= (others => '0');
      elsif CLK='1' and CLK'event then
         if cnt_requests_ce = '1' then
            if cnt_requests_dir = '1' then  
               cnt_requests <= cnt_requests + 1;
            else
               cnt_requests <= cnt_requests - 1;
            end if;
         end if;
      end if;
   end process;

   -- BM request register field -----------------------------------------------
   -- tag register
   reg_tagp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_tag <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (reg_tag_we = '1') then
            reg_tag <= DNS_DATA(11 downto 0);
         end if;
      end if;
   end process;
   
   -- type register
   reg_typep: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_type <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (reg_type_we = '1') then
            reg_type <= DNS_DATA(15 downto 12);
         end if;
      end if;
   end process;

   -- length register
   reg_lengthp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_length <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (reg_length_we = '1') then
            reg_length <= DNS_DATA(11 downto 0);
         end if;
      end if;
   end process;

   -- local address 0 register
   reg_laddr0p: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_laddr0 <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (reg_laddr0_we = '1') then
            reg_laddr0 <= DNS_DATA;
         end if;
      end if;
   end process;

   -- local address 1 register
   reg_laddr1p: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_laddr1 <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (reg_laddr1_we = '1') then
            reg_laddr1 <= DNS_DATA;
         end if;
      end if;
   end process;

   -- global address 0 register
   reg_gaddr0p: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_gaddr0 <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (reg_gaddr0_we = '1') then
            reg_gaddr0 <= DNS_DATA;
         end if;
      end if;
   end process;

   -- global address 1 register
   reg_gaddr1p: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_gaddr1 <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (reg_gaddr1_we = '1') then
            reg_gaddr1 <= DNS_DATA;
         end if;
      end if;
   end process;

   -- global address 2 register
   reg_gaddr2p: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_gaddr2 <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (reg_gaddr2_we = '1') then
            reg_gaddr2 <= DNS_DATA;
         end if;
      end if;
   end process;

   -- global address 3 register
   reg_gaddr3p: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_gaddr3 <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (reg_gaddr3_we = '1') then
            reg_gaddr3 <= DNS_DATA;
         end if;
      end if;
   end process;


   -- output FIFO buffer mapping ----------------------------------------------
   OUTPUT_BUFFER : FIFO
      generic map (
         DATA_WIDTH     => 16,
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
         FULL           => open,
         LSTBLK         => open,
         -- Read interface
         DATA_OUT       => fifo_do,
         READ_REQ       => fifo_rrq,
         EMPTY          => fifo_empty
      );

end architecture full;
