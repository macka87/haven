--
-- addr_dec.vhd : IB Endpoint Address Decoder
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
--             ENTITY DECLARATION -- IB Endpoint Address Decoder             -- 
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_ADDR_DEC is 
   generic(
      -- Data Width (8-128)
      DATA_WIDTH   : integer:= 64;
      -- Endpoint Address Space 
      ENDPOINT_BASE  : std_logic_vector(31 downto 0) := X"11111111";
      ENDPOINT_LIMIT : std_logic_vector(31 downto 0) := X"44444444"
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK           : in std_logic;  
      RESET         : in std_logic;  

      -- Input interface ------------------------------------------------------
      IN_DATA       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_SOF_N      : in  std_logic;
      IN_EOF_N      : in  std_logic;
      IN_SRC_RDY_N  : in  std_logic;
      IN_DST_RDY_N  : out std_logic;

      -- Output interface -----------------------------------------------------
      OUT_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_SOF_N     : out std_logic;
      OUT_EOF_N     : out std_logic;
      OUT_SRC_RDY_N : out std_logic;
      OUT_DST_RDY_N : in  std_logic;      

      OUT_REQ       : out std_logic;
      OUT_DROP      : out std_logic;
      OUT_ACK       : in  std_logic      
   );
end IB_ENDPOINT_ADDR_DEC;

-- ----------------------------------------------------------------------------
--              ARCHITECTURE DECLARATION  --  IB Endpoint Address Decoder    --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_addr_dec_arch of IB_ENDPOINT_ADDR_DEC is

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
   signal addr_mx           : std_logic_vector(max(log2(ADDR_WIDTH/CMP_WIDTH),1)-1 downto 0);
   signal addr              : std_logic_vector(CMP_WIDTH-1 downto 0);                              
   signal addr_next         : std_logic;
   signal transfer          : std_logic;
   signal eof               : std_logic;
   signal pause_transfer    : std_logic;
   signal req               : std_logic;
   signal req_we            : std_logic;

   signal bufin_DATA        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal bufin_SOF_N       : std_logic;
   signal bufin_EOF_N       : std_logic;
   signal bufin_SRC_RDY_N   : std_logic;
   signal bufin_DST_RDY_N   : std_logic;
                             
   -- const signals --                          
   signal const_base        : std_logic_vector(CMP_WIDTH-1 downto 0);                              
   signal const_high        : std_logic_vector(CMP_WIDTH-1 downto 0);                              

   -- hit signals --
   signal hit_base          : std_logic;                              
   signal hit_high          : std_logic;  
                                                                                                   
begin

   -- -------------------------------------------------------------------------
   --                           ADDRESS SPLITTER                             --
   -- -------------------------------------------------------------------------

   -- with address splitter ---------------------------------------------------
   ADDR_SPLITTER_YES: if (DATA_WIDTH > CMP_LIMIT) generate
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

   addr_aux <= addr32_extracted_from_data(ZEROES&IN_DATA, DATA_WIDTH).VEC(ADDR_WIDTH-1 downto 0);

   -- without address splitter ------------------------------------------------
   ADDR_SPLITTER_NO: if (DATA_WIDTH <= CMP_LIMIT) generate
      addr <= addr32_extracted_from_data(ZEROES&IN_DATA, DATA_WIDTH).VEC(CMP_WIDTH-1 downto 0);
   end generate;   

   -- -------------------------------------------------------------------------
   --                           ADDRESS CONSTANTS                            --
   -- -------------------------------------------------------------------------

   -- base constants --------------------------------------
   U_addr_const_base: entity work.ADDR_CONST
   generic map (
      ADDR      => ENDPOINT_BASE,
      WIDTH     => CMP_WIDTH  
   ) 
   port map (
      CLK       => CLK,  
      RESET     => RESET,
      NEXT_PART => addrpart_we,
      CONST     => const_base
   );

   -- high constants --------------------------------------
   U_addr_const_limit: entity work.ADDR_CONST
   generic map (
      ADDR      => ENDPOINT_BASE+ENDPOINT_LIMIT,
      WIDTH     => CMP_WIDTH  
   ) 
   port map (
      CLK       => CLK,
      RESET     => RESET,
      NEXT_PART => addrpart_we,
      CONST     => const_high
   );            

   -- -------------------------------------------------------------------------
   --                          ADDRESS COMPARATORS                           --
   -- -------------------------------------------------------------------------

   -- base comparator -------------------------------------
   U_addr_cmp_base: entity work.ADDR_CMP
   generic map (
      WIDTH     => CMP_WIDTH, 
      CMP_TYPE  => "GT_EQ"
   )
   port map (
      CLK       => CLK,
      RESET     => RESET,
   
      CONST     => const_base,
      ADDR      => addr,
      ADDR_WE   => addrpart_we,
      ADDR_NEXT => addr_next,
      
      HIT       => hit_base
   );

   -- high comparator -------------------------------------
   U_addr_cmp_high: entity work.ADDR_CMP
   generic map (
      WIDTH     => CMP_WIDTH, 
      CMP_TYPE  => "LT"
   )
   port map (
      CLK       => CLK,
      RESET     => RESET,

      CONST     => const_high,
      ADDR      => addr,
      ADDR_WE   => addrpart_we,
      ADDR_NEXT => addr_next,
      
      HIT       => hit_high
   );            

   -- -------------------------------------------------------------------------
   --                           RESOLUTION LOGIC                             --
   -- -------------------------------------------------------------------------   
   
   req <= hit_base and hit_high;   

   -- -------------------------------------------------------------------------
   --                             FETCH MARKER                               --
   -- ------------------------------------------------------------------------- 

   U_ib_endpoint_addr_dec_fetch_marker: entity work.ADDR_DEC_FETCH_MARKER
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
      REQUEST_VECTOR_WE => req_we,
      PAUSE_TRANSFER    => pause_transfer,
      ADDR_NEXT         => addr_next,
      ADDR_MX           => addr_mx,
      ADDR_WE           => addr_we,
      ADDRPART_WE       => addrpart_we,
      TYPE_LG_WE        => open
   );

   -- -------------------------------------------------------------------------
   --               DATA PATH BETWEEN INPUT AND DATA BUFFER                  --
   -- -------------------------------------------------------------------------

   bufin_DATA      <= IN_DATA;
   bufin_SOF_N     <= IN_SOF_N;
   bufin_EOF_N     <= IN_EOF_N;
   bufin_SRC_RDY_N <= IN_SRC_RDY_N or pause_transfer;

   IN_DST_RDY_N    <= bufin_DST_RDY_N or pause_transfer;

   transfer        <= (not bufin_DST_RDY_N) and (not IN_SRC_RDY_N);
   eof             <=  not IN_EOF_N;   
  
   -- -------------------------------------------------------------------------
   --                             DATA BUFFER                                --
   -- -------------------------------------------------------------------------   

   U_ib_buffer_sh: entity work.IB_BUFFER_SH
   generic map (
      DATA_WIDTH    => DATA_WIDTH,
      ITEMS         => ib_endpoint_addr_dec_buffer_data_depth(1, DATA_WIDTH)
   ) 
   port map (
      -- Common interface -----------------------------------------------------
      CLK           => CLK,
      RESET         => RESET,

      -- Input interface ------------------------------------------------------
      IN_DATA       => bufin_DATA,     
      IN_SOF_N      => bufin_SOF_N,    
      IN_EOF_N      => bufin_EOF_N,    
      IN_SRC_RDY_N  => bufin_SRC_RDY_N,
      IN_DST_RDY_N  => bufin_DST_RDY_N,

      -- Output interface -----------------------------------------------------
      OUT_DATA      => OUT_DATA,     
      OUT_SOF_N     => OUT_SOF_N,    
      OUT_EOF_N     => OUT_EOF_N,    
      OUT_SRC_RDY_N => OUT_SRC_RDY_N,
      OUT_DST_RDY_N => OUT_DST_RDY_N
   );               

   -- -------------------------------------------------------------------------
   --                            REQUEST BUFFER                              --
   -- -------------------------------------------------------------------------   

   U_ib_endpoint_addr_dec_req_buf: entity work.IB_ENDPOINT_ADDR_DEC_REQUEST_BUFFER
   generic map(
      -- The number of items to be stored
      ITEMS        => ib_endpoint_addr_dec_buffer_req_depth(1, DATA_WIDTH)
   ) 
   port map (
      -- Common interface ---------------------------------
      CLK          => CLK,
      RESET        => RESET,

      -- Input interface ----------------------------------
      IN_REQ       => req,
      IN_REQ_WE    => req_we,
      
      -- Output interface ---------------------------------
      OUT_REQ      => OUT_REQ,
      OUT_DROP     => OUT_DROP,
      OUT_ACK      => OUT_ACK
   );
     
end ib_endpoint_addr_dec_arch;

                     

