-- swt_bmem_ctrl.vhd: BMEM control 
-- Copyright (C) 2003 CESNET
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
entity SWR_BMEM_CTRL is
   generic (
      DATA_WIDTH     : integer;
      BMEM_ITEMS     : integer;
      BFIFO_ITEMS    : integer;  -- number of block FIFO items
      RESERVED_ITEMS : integer   -- number of items to reserve for control data
   );
   port(
      CLK         : in  std_logic;
      RESET       : in  std_logic;
      
      -- Write interface
      DATA_IN     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      WE          : in  std_logic;
      IS_DATA     : in  std_logic;  -- 1: data; 0: control data
      EOF         : in  std_logic;
      FREE_BLOCK  : in  std_logic;
      FULL        : out std_logic;
      READY       : out std_logic;
      OFFSET      : out std_logic_vector(log2(BMEM_ITEMS)-1 downto 0);

      -- BlockRAM interface
      BMEM_DATA   : out std_logic_vector(DATA_WIDTH-1 downto 0);
      BMEM_ADDR   : out std_logic_vector(log2(BMEM_ITEMS)-1 downto 0);
      BMEM_WE     : out std_logic
   );
end entity SWR_BMEM_CTRL;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of SWR_BMEM_CTRL is

   -- ------------------ Constants declaration --------------------------------
   constant BMEM_ADDR_W       : integer := log2(BMEM_ITEMS);
   constant BLOCK_WIDTH       : integer := log2(RESERVED_ITEMS - 1) + 1;
   
   -- ------------------ Signals declaration ----------------------------------
   -- counters
   signal cnt_data            : std_logic_vector(BMEM_ADDR_W downto 0);
   signal cnt_data_ce         : std_logic;
   signal cnt_data_load       : std_logic;
   signal cnt_cdata           : std_logic_vector(BMEM_ADDR_W-1 downto 0);
   signal cnt_cdata_ce        : std_logic;
   signal cnt_cdata_load      : std_logic;
   
   -- registers
   signal reg_load            : std_logic;
   signal reg_full            : std_logic;
   signal reg_border          : std_logic_vector(BMEM_ADDR_W downto 0);
   signal reg_border_we       : std_logic;
   signal reg_block_freed     : std_logic;

   -- (de)multiplexers
   signal dmx_cnt_ce          : std_logic_vector(1 downto 0);
   signal mx_bmem_addr        : std_logic_vector(BMEM_ADDR_W-1 downto 0);

   --others
   signal full_int            : std_logic;
   signal cnt_data_adder      : std_logic_vector(BMEM_ADDR_W downto 0);
   signal bfifo_full          : std_logic;
   signal bfifo_empty         : std_logic;
   signal bfifo_dout          : std_logic_vector(BMEM_ADDR_W downto 0);
   signal write_allow         : std_logic;
   
   
begin
   -- directly mapped signals -------------------------------------------------
   write_allow       <= (not reg_full) and WE;
   reg_border_we     <= FREE_BLOCK and (not bfifo_empty);
   
   -- counters' control logic
   cnt_data_load     <= reg_load;
   cnt_cdata_load    <= reg_load;
   cnt_data_ce       <= dmx_cnt_ce(1);
   cnt_cdata_ce      <= dmx_cnt_ce(0);
   cnt_data_adder    <= cnt_data + RESERVED_ITEMS;

   -- empty, full logic
   process(reg_border, cnt_data, write_allow)
   begin
      if (
         (reg_border(BMEM_ADDR_W-1 downto BLOCK_WIDTH) = 
            cnt_data(BMEM_ADDR_W-1 downto BLOCK_WIDTH))
         and (reg_border(BMEM_ADDR_W) /= cnt_data(BMEM_ADDR_W))
         and (write_allow = '1')) 
      then
   		full_int <= '1';
   	else
   		full_int <= '0';
   	end if;
   end process;

   -- output interface signals mapping
   FULL              <= reg_full;
   BMEM_DATA         <= DATA_IN;
   BMEM_ADDR         <= mx_bmem_addr;
   BMEM_WE           <= write_allow;
   READY             <= (not reg_load) and (not bfifo_full);
   OFFSET            <= cnt_cdata(BMEM_ADDR_W-1 downto 0);

   -- ------------------ counter cnt_data -------------------------------------
   cnt_datap: process (CLK) 
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' then 
            cnt_data <= conv_std_logic_vector(RESERVED_ITEMS, BMEM_ADDR_W+1);
         elsif cnt_data_load = '1' then
            cnt_data <= cnt_data_adder;
         else
            if cnt_data_ce = '1' then
               cnt_data <= cnt_data + 1;
            end if;
         end if;
      end if;
   end process;

   -- ------------------ counter cnt_cdata ------------------------------------
   cnt_cdatap: process (CLK) 
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' then 
            cnt_cdata <= (others => '0');
         elsif cnt_cdata_load = '1' then
            cnt_cdata <= cnt_data(BMEM_ADDR_W-1 downto 0);
         else
            if cnt_cdata_ce = '1' then
               cnt_cdata <= cnt_cdata + 1;
            end if;
         end if;
      end if;
   end process;

   -- ------------------ register reg_load ------------------------------------
   reg_loadp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_load <= '0';
         else
            reg_load <= EOF;
         end if;
      end if;
   end process;

   -- ------------------ register reg_block_freed -----------------------------
   reg_block_freedp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_block_freed <= '0';
         else
            reg_block_freed <= FREE_BLOCK;
         end if;
      end if;
   end process;

   -- ------------------ register reg_border ----------------------------------
   reg_borderp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_border <= (others => '1');
         elsif (reg_border_we = '1') then
            reg_border <= bfifo_dout - 1;
         end if;
      end if;
   end process;

   -- ------------------ register reg_full ------------------------------------
   reg_fullp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_full <= '0';
         elsif (write_allow = '1' or reg_block_freed = '1') then
            reg_full <= full_int;
         end if;
      end if;
   end process;

   -- ------------------ Multiplexer ------------------------------------------
   mx_bmem_addrp: process( IS_DATA, cnt_data, cnt_cdata )
   begin
      case IS_DATA is
         when '0'  => mx_bmem_addr <= cnt_cdata(BMEM_ADDR_W-1 downto 0);
         when '1'  => mx_bmem_addr <= cnt_data(BMEM_ADDR_W-1 downto 0);
         when others => null;
      end case;
   end process;

   -- ------------------ Demultiplexer ----------------------------------------
   dmx_cnt_cep: process (IS_DATA, write_allow)
   begin
      dmx_cnt_ce <= (others => '0');
      case IS_DATA is
         when '0' => dmx_cnt_ce(0) <= write_allow;
         when '1' => dmx_cnt_ce(1) <= write_allow;
         when others => null;
      end case;
   end process;

   blocks_fifo: entity work.fifo
      generic map (
         -- Set data width here
         DATA_WIDTH     => BMEM_ADDR_W + 1,
   
         -- Distributed RAM type, only 16, 32, 64 bits
         DISTMEM_TYPE   => 16,
   
         -- Set number of items in FIFO here
         ITEMS          => BFIFO_ITEMS,
   
         -- for last block identification
         BLOCK_SIZE     => 0
      )
      port map (
         RESET       => RESET,
         CLK         => CLK,
   
         -- Write interface
         DATA_IN     => cnt_data,
         WRITE_REQ   => reg_load,
         FULL        => bfifo_full,
         LSTBLK      => open,
   
         -- Read interface
         DATA_OUT    => bfifo_dout,
         READ_REQ    => FREE_BLOCK,
         EMPTY       => bfifo_empty
      );

end architecture full;
