--
-- input_port.vhd : IB Switch Input port
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

use work.math_pack.all;
use work.ib_switch_pkg.all;

-- ----------------------------------------------------------------------------
--                 ENTITY DECLARATION -- IB Switch Input port                --
-- ----------------------------------------------------------------------------

entity IB_SWITCH_INPUT_PORT is 
   generic(
      -- Data Width (1-128)
      DATA_WIDTH   : integer:= 64;
      -- Port number (0/1/2)
      PORT_NUM     : integer:=  0;
      -- Port 1 Address Space
      PORT1_BASE   : std_logic_vector(31 downto 0) := X"11111111";
      PORT1_LIMIT  : std_logic_vector(31 downto 0) := X"11111111";
      -- Port 2 Address Space
      PORT2_BASE   : std_logic_vector(31 downto 0) := X"22222222";
      PORT2_LIMIT  : std_logic_vector(31 downto 0) := X"22222222"
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK          : in std_logic;  
      RESET        : in std_logic;  

      -- Input interface ------------------------------------------------------
      IN_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_SOF_N     : in  std_logic;
      IN_EOF_N     : in  std_logic;
      IN_SRC_RDY_N : in  std_logic;
      IN_DST_RDY_N : out std_logic;

      -- Output interface -----------------------------------------------------
      OUT_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_SOF_N    : out std_logic;
      OUT_EOF_N    : out std_logic;
      OUT_WR       : out std_logic;
      OUT_FULL     : in  std_logic;      

      OUT_REQ_VEC  : out std_logic_vector(2 downto 0);
      OUT_REQ_WE   : out std_logic      
   );
end IB_SWITCH_INPUT_PORT;

-- ----------------------------------------------------------------------------
--              ARCHITECTURE DECLARATION  --  IB Switch Input port           --
-- ----------------------------------------------------------------------------

architecture ib_switch_input_port_arch of IB_SWITCH_INPUT_PORT is

   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------

   constant CMP_LIMIT  : integer := 16;
   constant CMP_WIDTH  : integer := addr_comparison_width(DATA_WIDTH, CMP_LIMIT);
   constant ADDR_WIDTH : integer := addr_input_width(DATA_WIDTH);

   constant ZEROES     : std_logic_vector(128-DATA_WIDTH-1 downto 0) := (others => '0');
   
   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   -- auxiliary signals --
   signal addrpart_we       : std_logic;
   signal addr_we           : std_logic;
   signal addr_aux          : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal addr_mx           : std_logic_vector(max(log2(addr_input_width(DATA_WIDTH)/CMP_WIDTH),1)-1 downto 0);
   signal addr              : std_logic_vector(CMP_WIDTH-1 downto 0);
   signal addr_next         : std_logic;
   signal transfer          : std_logic;
   signal eof               : std_logic;
   signal pause_transfer    : std_logic;
   signal type_lg_we        : std_logic;
   signal type_lg           : std_logic;
   
   -- const signals --
   signal const_port1_base  : std_logic_vector(CMP_WIDTH-1 downto 0);
   signal const_port2_base  : std_logic_vector(CMP_WIDTH-1 downto 0);
   signal const_port1_high  : std_logic_vector(CMP_WIDTH-1 downto 0);
   signal const_port2_high  : std_logic_vector(CMP_WIDTH-1 downto 0);

   -- hit signals --
   signal hit_port1_base    : std_logic;
   signal hit_port2_base    : std_logic;
   signal hit_port1_high    : std_logic;
   signal hit_port2_high    : std_logic;
   
begin

   -- -------------------------------------------------------------------------
   --                           ADDRESS SPLITTER                             --
   -- -------------------------------------------------------------------------

   -- with address splitter ---------------------------------------------------
   ADDR_SPLITTER_YES: if (address_splitter_enable(DATA_WIDTH,CMP_LIMIT)) generate
      U_addr_splitter: entity work.ADDR_SPLITTER
      generic map (
         INPUT_WIDTH  => ADDR_WIDTH,
         OUTPUT_WIDTH => CMP_WIDTH
      ) 
      port map (
         -- Common interface ------------------------------
         CLK          => CLK,
         
         -- Input interface -------------------------------
         ADDR_IN      => addr_aux,
         ADDR_WE      => addr_we,
         ADDR_MX      => addr_mx,

         -- Output interface ------------------------------
         ADDR_OUT     => addr
      );
   end generate;

   addr_aux <= addr_extracted_from_data(ZEROES&IN_DATA, DATA_WIDTH).VEC(ADDR_WIDTH-1 downto 0);

   -- without address splitter ------------------------------------------------
   ADDR_SPLITTER_NO: if (not address_splitter_enable(DATA_WIDTH,CMP_LIMIT)) generate
      addr <= addr_extracted_from_data(ZEROES&IN_DATA, DATA_WIDTH).VEC(CMP_WIDTH-1 downto 0);
   end generate;

   -- -------------------------------------------------------------------------
   --                           ADDRESS CONSTANTS                            --
   -- -------------------------------------------------------------------------

   -- port1 constants ---------------------------------------------------------
   PORT1_CONSTS: if ((PORT_NUM = 0) or (PORT_NUM = 2)) generate
      U_addr_const_port1_base: entity work.ADDR_CONST
      generic map (
         ADDR      => PORT1_BASE,
         WIDTH     => CMP_WIDTH
      ) 
      port map (
         CLK       => CLK,
         RESET     => RESET,
         NEXT_PART => addrpart_we,
         CONST     => const_port1_base
      );

      U_addr_const_port1_high: entity work.ADDR_CONST
      generic map (
         ADDR      => PORT1_BASE+PORT1_LIMIT,
         WIDTH     => CMP_WIDTH
      ) 
      port map (
         CLK       => CLK,
         RESET     => RESET,
         NEXT_PART => addrpart_we,
         CONST     => const_port1_high
      );
   end generate;

   -- port2 constants ---------------------------------------------------------
   PORT2_CONSTS: if ((PORT_NUM = 0) or (PORT_NUM = 1)) generate
      U_addr_const_port2_base: entity work.ADDR_CONST
      generic map (
         ADDR      => PORT2_BASE,
         WIDTH     => CMP_WIDTH
      ) 
      port map (
         CLK       => CLK,
         RESET     => RESET,
         NEXT_PART => addrpart_we,
         CONST     => const_port2_base
      );

      U_addr_const_port2_high: entity work.ADDR_CONST
      generic map (
         ADDR      => PORT2_BASE+PORT2_LIMIT,
         WIDTH     => CMP_WIDTH
      ) 
      port map (
         CLK       => CLK,
         RESET     => RESET,
         NEXT_PART => addrpart_we,
         CONST     => const_port2_high
      );
   end generate;

   -- -------------------------------------------------------------------------
   --                          ADDRESS COMPARATORS                           --
   -- -------------------------------------------------------------------------

   -- port1 comparators -------------------------------------------------------
   PORT1_CMPS: if ((PORT_NUM = 0) or (PORT_NUM = 2)) generate
      U_addr_cmp_port1_base: entity work.ADDR_CMP
      generic map (
         WIDTH     => CMP_WIDTH,
         CMP_TYPE  => "GT_EQ"
      )
      port map (
         CLK       => CLK,
         RESET     => RESET,
      
         CONST     => const_port1_base,
         ADDR      => addr,
         ADDR_WE   => addrpart_we,
         ADDR_NEXT => addr_next,
         
         HIT       => hit_port1_base
      );

      U_addr_cmp_port1_high: entity work.ADDR_CMP
      generic map (
         WIDTH     => CMP_WIDTH, 
         CMP_TYPE  => "LT"
      )
      port map (
         CLK       => CLK,
         RESET     => RESET,
         
         CONST     => const_port1_high,
         ADDR      => addr,
         ADDR_WE   => addrpart_we,
         ADDR_NEXT => addr_next,
         
         HIT       => hit_port1_high
      );
   end generate;

   -- port2 comparators -------------------------------------------------------
   PORT2_CMPS: if ((PORT_NUM = 0) or (PORT_NUM = 1)) generate
      U_addr_cmp_port2_base: entity work.ADDR_CMP
      generic map (
         WIDTH     => CMP_WIDTH,
         CMP_TYPE  => "GT_EQ"
      ) 
      port map (
         CLK       => CLK,
         RESET     => RESET,
         
         CONST     => const_port2_base,
         ADDR      => addr,
         ADDR_WE   => addrpart_we,
         ADDR_NEXT => addr_next,
         
         HIT       => hit_port2_base
      );

      U_addr_cmp_port2_high: entity work.ADDR_CMP
      generic map (
         WIDTH     => CMP_WIDTH, 
         CMP_TYPE  => "LT"
      )
      port map (
         CLK       => CLK,
         RESET     => RESET,

         CONST     => const_port2_high,
         ADDR      => addr,
         ADDR_WE   => addrpart_we,
         ADDR_NEXT => addr_next,
         
         HIT       => hit_port2_high
      );
   end generate;

   -- -------------------------------------------------------------------------
   --                             TYPE REGISTER                              --
   -- -------------------------------------------------------------------------

   -- with type register ------------------------------------------------------
   TYPE_REGISTER_YES: if ( not ((CMP_WIDTH = 32) and ((DATA_WIDTH = 64) or (DATA_WIDTH = 128))) ) generate
      type_lgp: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (type_lg_we = '1') then
               type_lg <= type_lg_extracted_from_data(ZEROES&IN_DATA, DATA_WIDTH);
            end if;
         end if;
      end process;
   end generate;

   -- without type register ---------------------------------------------------
   TYPE_REGISTER_NO: if ( ((CMP_WIDTH = 32) and ((DATA_WIDTH = 64) or (DATA_WIDTH = 128))) ) generate
      type_lg <= type_lg_extracted_from_data(ZEROES&IN_DATA, DATA_WIDTH);
   end generate;

   -- -------------------------------------------------------------------------
   --                             ROUTING RULES                              --
   -- -------------------------------------------------------------------------
   
   U_ib_switch_routing_rules: entity work.IB_SWITCH_ROUTING_RULES
   generic map (
      -- Port number (0/1/2)
      PORT_NUM        => PORT_NUM
   )
   port map (
      -- Input interface ----------------------------------
      HIT_PORT1_BASE  => hit_port1_base,
      HIT_PORT1_HIGH  => hit_port1_high,
      HIT_PORT2_BASE  => hit_port2_base,
      HIT_PORT2_HIGH  => hit_port2_high,
      
      HIT_GLOBAL      => type_lg,

      -- Output interface ---------------------------------
      REQUEST_VECTOR  => OUT_REQ_VEC
   );

   -- -------------------------------------------------------------------------
   --                              DATA PATH                                 --
   -- -------------------------------------------------------------------------

   OUT_DATA     <= IN_DATA;
   OUT_SOF_N    <= IN_SOF_N;
   OUT_EOF_N    <= IN_EOF_N;
   OUT_WR       <= (not OUT_FULL) and (not IN_SRC_RDY_N) and (not pause_transfer);

   IN_DST_RDY_N <= OUT_FULL or pause_transfer or RESET;

   transfer <= (not OUT_FULL) and (not IN_SRC_RDY_N);
   eof      <=  not IN_EOF_N;

   -- -------------------------------------------------------------------------
   --                             FETCH MARKER                               --
   -- -------------------------------------------------------------------------

   U_ib_switch_fetch_marker: entity work.ADDR_DEC_FETCH_MARKER
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH        => DATA_WIDTH,
      -- Compare Width (1-32)
      CMP_WIDTH         => CMP_WIDTH
   )
   port map (
      -- Input interface ----------------------------------
      CLK               => CLK,
      RESET             => RESET,
      
      -- Input interface ----------------------------------
      TRANSFER          => transfer,
      EOF               => eof,

      -- Output interface ---------------------------------
      REQUEST_VECTOR_WE => OUT_REQ_WE,
      PAUSE_TRANSFER    => pause_transfer,
      ADDR_NEXT         => addr_next,
      ADDR_MX           => addr_mx,
      ADDR_WE           => addr_we,
      ADDRPART_WE       => addrpart_we,
      TYPE_LG_WE        => type_lg_we
   );
  
end ib_switch_input_port_arch;


