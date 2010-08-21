-- fl2bm.vhd: Convertor from FrameLink interface to Bus master interface
-- Copyright (C) 2007 CESNET
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

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL2BM is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- input interface
      RX_SOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_DATA        : in  std_logic_vector(127 downto 0);
      RX_REM         : in  std_logic_vector(log2(128/8)-1 downto 0);
      -- input TAG interface
      RX_DMA_TAG     : out std_logic_vector(15 downto 0);
      RX_DMA_DONE    : out std_logic;

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
end entity FL2BM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL2BM is

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
   signal reg_ready              : std_logic;
   signal reg_ready_we           : std_logic;

   -- others
   signal new_request            : std_logic;

begin
   -- ------------------ Directly mapped signals ------------------------------
   new_request    <= not (reg_ready or RX_SRC_RDY_N);
   
   -- register controls
   reg_ready_we   <= new_request or BM_ACK;

   reg_global_addr_we   <= new_request;
   reg_local_addr_we    <= new_request;
   reg_length_we        <= new_request;
   reg_tag_we           <= new_request;
   reg_trans_type_we    <= new_request;

   -- output port mapping
   RX_DST_RDY_N   <= reg_ready;
   -- input TAG interface
   RX_DMA_TAG     <= BM_OP_TAG;
   RX_DMA_DONE    <= BM_OP_DONE;
   -- Bus master interface
   BM_GLOBAL_ADDR <= reg_global_addr;
   BM_LOCAL_ADDR  <= reg_local_addr;
   BM_LENGTH      <= reg_length;
   BM_TAG         <= reg_tag;
   BM_TRANS_TYPE  <= reg_trans_type;
   BM_REQ         <= reg_ready;

   -- register reg_global_addr
   reg_global_addrp: process (CLK)
   begin
      if CLK'event and CLK='1' then
         if (reg_global_addr_we = '1') then
            reg_global_addr <= RX_DATA(127 downto 64);
         end if;
      end if;
   end process;
   
   -- register reg_local_addr
   reg_local_addrp:process (CLK)
   begin
      if CLK'event and CLK='1' then
         if (reg_local_addr_we = '1') then
            reg_local_addr <= RX_DATA(63 downto 32);
         end if;
      end if;
   end process;
   
   -- register reg_length
   reg_lengthp:process (CLK)
   begin
      if CLK'event and CLK='1' then
         if (reg_length_we = '1') then
            reg_length <= RX_DATA(15 downto 4);
         end if;
      end if;
   end process;
   
   -- register reg_tag
   reg_tagp:process (CLK)
   begin
      if CLK'event and CLK='1' then
         if (reg_tag_we = '1') then
            reg_tag <= RX_DATA(31 downto 16);
         end if;
      end if;
   end process;

   -- register reg_trans_type
   reg_trans_typep:process (CLK)
   begin
      if CLK'event and CLK='1' then
         if (reg_trans_type_we = '1') then
            reg_trans_type <= RX_DATA(1 downto 0);
         end if;
      end if;
   end process;

   -- register reg_ready
   reg_readyp:process (CLK)
   begin
      if CLK'event and CLK='1' then  
         if RESET='1' then   
            reg_ready <= '0';
         elsif (reg_ready_we = '1') then
            reg_ready <= new_request and (not BM_ACK);
         end if;
      end if;
   end process;

end architecture full;

