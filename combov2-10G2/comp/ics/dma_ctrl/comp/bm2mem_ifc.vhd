--
-- bm2mem_ifcvhd : interface adapter
-- Copyright (C) 2008 CESNET
-- Author(s): Petr Kastovsky <kastosvky@liberouter.org>
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
-- TODO:
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity bm2mem is
   generic(
      DMA_DATA_WIDTH       : integer := 16
   );
   port(
      -- Common interface
      CLK   : in std_logic;
      RESET : in std_logic;

      -- Busmaster interface
      BM_GLOBAL_ADDR : in std_logic_vector(63 downto 0);  -- Global address
      BM_LOCAL_ADDR  : in std_logic_vector(31 downto 0);  -- Local address
      BM_LENGTH      : in std_logic_vector(11 downto 0);  -- Length
      BM_TAG         : in std_logic_vector(15 downto 0);  -- Operation tag
      BM_TRANS_TYPE  : in std_logic_vector(3 downto 0);   -- Transaction type
      BM_REQ         : in std_logic;                      -- Request

      BM_ACK         : out std_logic;                       -- Ack
      BM_OP_TAG      : out std_logic_vector(15 downto 0);   -- Operation tag
      BM_OP_DONE     : out std_logic;                       -- Acknowledge

      -- Memory interface
      DMA_ADDR        : in  std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
      DMA_DOUT        : out std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
      DMA_REQ         : out std_logic;
      DMA_ACK         : in  std_logic;
      DMA_DONE        : in  std_logic;
      DMA_TAG         : in  std_logic_vector(15 downto 0)
   );
end entity bm2mem;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture bm2mem_arch of bm2mem is

   signal mem_out         : std_logic_vector(127 downto 0);
   signal mem_in          : std_logic_vector(127 downto 0);
   signal reg_bm_req      : std_logic;

begin

   MEM_DMA_REQUEST: entity work.sp_distmem(behavioral)
      generic map (
         -- Data Width
         DATA_WIDTH  => 128,
         -- Item in memory needed, one item size is DATA_WIDTH
         ITEMS  => 2,
         -- Distributed Ram Type(capacity) only 16, 32, 64 bits
         DISTMEM_TYPE => 16,
         -- debug prints
         DEBUG   => false
      )
      port map (
         -- Common interface
         RESET  => RESET,
         -- R/W Port
         DI     => mem_in,
         WE     => BM_REQ,
         WCLK   => CLK,
         ADDR   => "0",
         DO     => mem_out
      );

   mem_in <= BM_GLOBAL_ADDR(63 downto 0) & 
             BM_LOCAL_ADDR(31 downto 0) &
             "0000" & -- reserved bits
             BM_TAG(11 downto 0) & 
             BM_LENGTH(11 downto 0) & 
             BM_TRANS_TYPE(3 downto 0);


   GEN_MUX_I : entity work.GEN_MUX
      generic map (
         DATA_WIDTH  => DMA_DATA_WIDTH,
         MUX_WIDTH   => 128/DMA_DATA_WIDTH
      )
      port map(
         DATA_IN     => mem_out,
         SEL         => DMA_ADDR,
         DATA_OUT    => DMA_DOUT
      );

   BM_ACK      <= DMA_ACK;
   BM_OP_TAG   <= DMA_TAG;
   BM_OP_DONE  <= DMA_DONE;


   -- register reg_bm_req ---------------------------------------------------
   reg_bm_reqp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg_bm_req <= BM_REQ;
      end if;
   end process;

   DMA_REQ     <= reg_bm_req;

end architecture bm2mem_arch;

