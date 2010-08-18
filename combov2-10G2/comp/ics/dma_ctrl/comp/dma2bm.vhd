-- dma2bm.vhd: Convertor from dma data interface to Bus master interface
-- Warning !!! : this component is intended for simulation purposes only 
-- It may have several serious issues !
-- Copyright (C) 2008 CESNET
-- Author(s): Petr Kastovsky <kastovsky@liberouter.org>
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
-- 
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity DMA2BM is
   generic (
      DMA_DATA_WIDTH       : integer := 16
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- Memory interface
      DMA_ADDR        : out std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
      DMA_DOUT        : in  std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
      DMA_REQ         : in  std_logic;
      DMA_ACK         : out  std_logic;
      DMA_DONE        : out  std_logic;
      DMA_TAG         : out  std_logic_vector(15 downto 0);

      -- Bus master interface
      BM_GLOBAL_ADDR : out std_logic_vector(63 downto 0);  -- Global address
      BM_LOCAL_ADDR  : out std_logic_vector(31 downto 0);  -- Local address
      BM_LENGTH      : out std_logic_vector(11 downto 0);  -- Length
      BM_TAG         : out std_logic_vector(15 downto 0);  -- Operation tag
      BM_TRANS_TYPE  : out std_logic_vector(1 downto 0);   -- Transaction type
      BM_REQ         : out std_logic;                      -- Request
      BM_ACK         : in std_logic;                       -- Ack
      -- Output
      BM_OP_TAG      : in std_logic_vector(15 downto 0);   -- Operation tag
      BM_OP_DONE     : in std_logic                        -- Acknowledge
   );
end entity DMA2BM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of DMA2BM is

   -- ------------------ Signals declaration ----------------------------------
   -- registers
   signal reg_global_addr        : std_logic_vector(63 downto 0);
   signal reg_global_addr_we     : std_logic;
   signal reg_local_addr         : std_logic_vector(31 downto 0);
   signal reg_local_addr_we      : std_logic;
   signal reg_length             : std_logic_vector(11 downto 0);
   signal reg_length_we          : std_logic;
   signal reg_tag                : std_logic_vector(15 downto 0);
   signal reg_tag_we             : std_logic;
   signal reg_trans_type         : std_logic_vector(1 downto 0);
   signal reg_trans_type_we      : std_logic;

   signal reg_bm_request         : std_logic_vector(127 downto 0);
   signal reg_bm_request_we      : std_logic;
   signal cnt_dma_addr           : std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
   signal cnt_dma_addr_ce        : std_logic;
   signal reg_cnt_ce             : std_logic;
   signal reg_cnt_ce_we          : std_logic;
   signal reg_we                 : std_logic;
   signal reg_ready              : std_logic;

   constant ones : std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0) := (others => '1');

begin

   -- input TAG interface
   DMA_TAG     <= BM_OP_TAG;
   DMA_DONE    <= BM_OP_DONE;
   DMA_ACK     <= reg_we;
   -- Bus master interface
   BM_GLOBAL_ADDR <= reg_global_addr;
   BM_LOCAL_ADDR  <= reg_local_addr;
   BM_LENGTH      <= reg_length;
   BM_TAG         <= reg_tag;
   BM_TRANS_TYPE  <= reg_trans_type;
   BM_REQ         <= reg_ready;

   reg_global_addr_we   <= reg_we;
   reg_local_addr_we    <= reg_we;
   reg_length_we        <= reg_we;
   reg_tag_we           <= reg_we;
   reg_trans_type_we    <= reg_we;


   -- register reg_ready ------------------------------------------------------
   reg_readyp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_ready <= '0';
         elsif (reg_we = '1') then
            reg_ready <= '1';
         elsif (BM_ACK = '1') then
            reg_ready <= '0';
         end if;
      end if;
   end process;

   -- register reg_global_addr
   reg_global_addrp: process (CLK)
   begin
      if CLK'event and CLK='1' then
         if (reg_global_addr_we = '1') then
--             reg_global_addr <= X"0000" & X"0000" & X"CCCC" & X"D000";
            reg_global_addr <= reg_bm_request(127 downto 64);
         end if;
      end if;
   end process;
   
   -- register reg_local_addr
   reg_local_addrp:process (CLK)
   begin
      if CLK'event and CLK='1' then
         if (reg_local_addr_we = '1') then
--             reg_local_addr <= X"0020" & X"0000"; -- reg_bm_request(63 downto 32);
            reg_local_addr <= reg_bm_request(63 downto 32);
         end if;
      end if;
   end process;
   
   -- register reg_length
   reg_lengthp:process (CLK)
   begin
      if CLK'event and CLK='1' then
         if (reg_length_we = '1') then
--             reg_length <= X"080"; -- reg_bm_request(15 downto 4);
            reg_length <= reg_bm_request(15 downto 4);
         end if;
      end if;
   end process;
   
   -- register reg_tag
   reg_tagp:process (CLK)
   begin
      if CLK'event and CLK='1' then
         if (reg_tag_we = '1') then
--             reg_tag <= X"0000"; -- reg_bm_request(31 downto 16);
            reg_tag <= reg_bm_request(31 downto 16);
         end if;
      end if;
   end process;

   -- register reg_trans_type
   reg_trans_typep:process (CLK)
   begin
      if CLK'event and CLK='1' then
         if (reg_trans_type_we = '1') then
--             reg_trans_type <= "00"; -- reg_bm_request(1 downto 0);
            reg_trans_type <= reg_bm_request(1 downto 0);
         end if;
      end if;
   end process;


   cnt_dma_addr_ce <= reg_cnt_ce;
   -- cnt_dma_addr counter
   cnt_dma_addrp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_dma_addr <= (others => '0');
         elsif (cnt_dma_addr_ce = '1') then
            cnt_dma_addr <= cnt_dma_addr + 1;
         end if;
      end if;
   end process;


   reg_cnt_ce_we <= DMA_REQ;
   -- register reg_cnt_ce ------------------------------------------------------
   reg_cnt_cep: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_cnt_ce <= '0';
            reg_we <= '0';
         elsif (reg_cnt_ce_we = '1') then
            reg_cnt_ce <= '1';
            reg_we <= '0';
         elsif (cnt_dma_addr = ones) then
            reg_cnt_ce <= '0';
            reg_we <= '1';
         else
            reg_we <= '0';
         end if;
      end if;
   end process;

   DMA_ADDR <= cnt_dma_addr;
   reg_bm_request_we <= cnt_dma_addr_ce;
   -- register reg_bm_request ------------------------------------------------------
   reg_bm_requestp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_bm_request <= (others => '0');
         elsif (reg_bm_request_we = '1') then
            reg_bm_request(127 - DMA_DATA_WIDTH downto 0) <= reg_bm_request(127 downto DMA_DATA_WIDTH);
            reg_bm_request(127 downto 128 - DMA_DATA_WIDTH) <= DMA_DOUT;
         end if;
      end if;
   end process;

end architecture full;

