--
-- unpck_hbuf.vhd : IB Endpoint Read Controller Unpacked Header Buffer
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
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
--

library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

use work.math_pack.all;
use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 
use work.ib_endpoint_pkg.all;

-- ----------------------------------------------------------------------------
--     ENTITY DECLARATION -- IB Endpoint Read Ctrl Unpacked Header Buffer    --
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_READ_CTRL_UNPCK_HBUF is 
   generic(
      -- Data Width (1-128)
      DATA_WIDTH    : integer := 64;
      -- The number of items to be stored
      ITEMS         : integer :=  1
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK           : in std_logic;  
      RESET         : in std_logic;  

      -- Input interface ------------------------------------------------------
      IN_COUNT      : in  std_logic_vector(13-log2(DATA_WIDTH/8)-1 downto 0);
      IN_LEN_ALIGN  : in std_logic_vector(align_width(DATA_WIDTH)-1 downto 0);
      IN_SRC_ALIGN  : in std_logic_vector(align_width(DATA_WIDTH)-1 downto 0); 
      IN_DST_ALIGN  : in std_logic_vector(align_width(DATA_WIDTH)-1 downto 0); 
      IN_TAG        : in std_logic_vector(7 downto 0);
      IN_DONE_FLAG  : in std_logic; 
      
      IN_WE         : in  std_logic;
      IN_FULL       : out std_logic; 

      -- Output interface -----------------------------------------------------
      OUT_COUNT     : out std_logic_vector(13-log2(DATA_WIDTH/8)-1 downto 0);
      OUT_LEN_ALIGN : out std_logic_vector(align_width(DATA_WIDTH)-1 downto 0);
      OUT_SRC_ALIGN : out std_logic_vector(align_width(DATA_WIDTH)-1 downto 0); 
      OUT_DST_ALIGN : out std_logic_vector(align_width(DATA_WIDTH)-1 downto 0); 
      OUT_TAG       : out std_logic_vector(7 downto 0);
      OUT_DONE_FLAG : out std_logic;       
      
      OUT_RE        : in  std_logic
   );
end IB_ENDPOINT_READ_CTRL_UNPCK_HBUF;

-- ----------------------------------------------------------------------------
--  ARCHITECTURE DECLARATION -- IB Endpoint Read Ctrl Unpacked Header Buffer --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_read_ctrl_unpck_hbuf_arch of IB_ENDPOINT_READ_CTRL_UNPCK_HBUF is

   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------

   constant COUNT_WIDTH : integer := 13-log2(DATA_WIDTH/8);
   constant ALIGN_WIDTH : integer := align_width(DATA_WIDTH);
   constant TAG_WIDTH   : integer := 8;
   constant ITEM_WIDTH  : integer := (3*ALIGN_WIDTH)+COUNT_WIDTH+TAG_WIDTH+1;
   
   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal data_in   : std_logic_vector(ITEM_WIDTH-1 downto 0);
   signal data_out  : std_logic_vector(ITEM_WIDTH-1 downto 0);
   signal reg_full  : std_logic;

begin

   -- -------------------------------------------------------------------------
   --                        INPUT/OUTPUT DATA INTERFACE                     --
   -- -------------------------------------------------------------------------

   data_in <= IN_DONE_FLAG&IN_TAG&IN_DST_ALIGN&IN_SRC_ALIGN&IN_LEN_ALIGN&IN_COUNT;

   OUT_COUNT     <= data_out(COUNT_WIDTH-1 downto 0);
   OUT_LEN_ALIGN <= data_out(COUNT_WIDTH+ALIGN_WIDTH-1 downto COUNT_WIDTH);
   OUT_SRC_ALIGN <= data_out(COUNT_WIDTH+(2*ALIGN_WIDTH)-1 downto COUNT_WIDTH+ALIGN_WIDTH);
   OUT_DST_ALIGN <= data_out(COUNT_WIDTH+(3*ALIGN_WIDTH)-1 downto COUNT_WIDTH+(2*ALIGN_WIDTH));
   OUT_TAG       <= data_out(COUNT_WIDTH+(3*ALIGN_WIDTH)+TAG_WIDTH-1 downto COUNT_WIDTH+(3*ALIGN_WIDTH));
   OUT_DONE_FLAG <= data_out(ITEM_WIDTH-1);
   
   -- -------------------------------------------------------------------------
   --               THE NUMBER OF HEADERS TO BE STORED == 1                  --
   -- -------------------------------------------------------------------------
   
   HEADER_NUM_EQ_1: if (ITEMS = 1) generate

      data_outp : process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (IN_WE = '1') then
               data_out  <= data_in;
            end if;
         end if;
      end process;
      
      reg_fullp: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               reg_full <= '0';
            elsif (IN_WE = '1') then
               reg_full <= '1';
            elsif (OUT_RE = '1') then
               reg_full <= '0';
            end if;
         end if;
      end process;
      
      IN_FULL <= reg_full and not OUT_RE;
      
   end generate;

   -- -------------------------------------------------------------------------
   --               THE NUMBER OF HEADERS TO BE STORED > 1                   --
   -- -------------------------------------------------------------------------

   HEADER_NUM_GT_1: if (ITEMS > 1) generate

      -- REQUEST BUFFER -------------------------------------------------------
      U_ib_endpoint_unpck_hbuf_sh_fifo: entity work.SH_FIFO
      generic map (
         FIFO_WIDTH     => ITEM_WIDTH,
         FIFO_DEPTH     => ITEMS,
         USE_INREG      => false, 
         USE_OUTREG     => false  
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,
         -- write interface
         DIN            => data_in,
         WE             => IN_WE,
         FULL           => IN_FULL,
         -- read interface
         DOUT           => data_out,
         RE             => OUT_RE,
         EMPTY          => open,
         -- status
         STATUS         => open
      );

   end generate; 
   
end ib_endpoint_read_ctrl_unpck_hbuf_arch;


