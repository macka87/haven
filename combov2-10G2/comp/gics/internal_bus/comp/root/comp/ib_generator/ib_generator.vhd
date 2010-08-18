 --
-- pcie_ib_generator.vhd : PCI-e Internal Bus Generator
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kobierský <kobierskyk@liberouter.org>
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

-- -------------------------
-- Interface to IB_GENERATOR
----------------------------
--             32   31   28     26   18           15      14     12     0
-- -----------------------------------------------------------------------
-- | LOCAL_ADDR | R | TC | ATTR | TAG | LOWER_ADDR | LAST  | TYPE | LEN  |
-- |            |   |    |      |     |            | COMPL |      |      |
-- -----------------------------------------------------------------------
-- | R | REQ_ID |            BRIDGE ADDRESS                              |
-- -----------------------------------------------------------------------
-- |   DATA1    |                      DATA0                             |
-- -----------------------------------------------------------------------

-- LEN:           Length in bytes, 12 bits
-- TYPE:          "01" - Read
--                "00" - Write
--                "11" - Completition
-- LAST_COMPL:    1 - When last completition
-- LOWER_ADDR:    (3bit) Lower address  - Valid for completitions
-- TAG:           Transaction TAG, 8 bit
-- ATTR:          Atribut
-- TC:            Traffic class
-- REQ_ID:        Read request ID


--   constant C_IB_L2LW_TRANSACTION          : std_logic_vector(2 downto 0) := "000"
--   constant C_IB_L2LR_TRANSACTION          : std_logic_vector(2 downto 0) := "001";
--   constant C_IB_L2GW_TRANSACTION          : std_logic_vector(2 downto 0) := "010";
--   constant C_IB_G2LR_TRANSACTION          : std_logic_vector(2 downto 0) := "011";
--   constant C_IB_WR_COMPL_TRANSACTION      : std_logic_vector(2 downto 0) := "100";
--   constant C_IB_RD_COMPL_TRANSACTION      : std_logic_vector(2 downto 0) := "101";


library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity PCIE_IB_GENERATOR is
  generic (
      INPUT_PIPE	      : boolean := false;
      OUTPUT_PIPE	      : boolean := true;
      ENABLE_ALIGN_UNIT : boolean := true  
  );
  port (
    -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N           : in  std_logic; 
      TRN_CLK               : in  std_logic;

      -- RX Decoder interface ---------------------------------------------
      DEC_DATA              : in  std_logic_vector( 63 downto 0 ); -- Data or Header
      DEC_SOP_N             : in  std_logic;                       -- Start of Packet
      DEC_EOP_N             : in  std_logic;                       -- End of Packet
      DEC_SRC_RDY_N         : in  std_logic;                       -- Source Ready
      DEC_DST_RDY_N         : out std_logic;                       -- Destination Ready
--       DEC_READ_TRANS_EN_N   : out std_logic;                       -- Enable Read transaction receiving

	  -- Write interface ------------------------------------------------------
	   LCB_TAG               : out std_logic_vector( 7 downto 0); 		-- Transaction Tag
	   LCB_WR_0	             : out std_logic;								   -- Write Request 0
	   LCB_REQ_ID	          : out std_logic_vector(15 downto 0);		-- Requester ID (BUS, DEVICE, FUNCTION)
	   LCB_WR_1		          : out std_logic;								   -- Write Request 1
      LCB_ALLOW		       :  in std_logic;								   -- Allow to write
	   LCB_LOCAL_TAG         :  in std_logic_vector( 7 downto 0);     -- Local Tag
	   --LCB_FULL		          :  in std_logic;								   -- Local Buffer Full
--       LCB_TRANS_EN_N        :  in std_logic;                         -- Enable transactions  
      
	   -- Read Interface -------------------------------------------------------
      GCB_LOCAL_ADDR        :  in std_logic_vector(31 downto 0); 		-- Local Address     
      GCB_LOCAL_TAG         :  in std_logic_vector( 7 downto 0); 	   -- Local Tag     
      GCB_RD     	          : out std_logic;  								-- Read Request
      GCB_GLOBAL_TAG        : out std_logic_vector( 7 downto 0);     -- Read Address
	   GCB_LAST_CPL	       : out std_logic;									-- Last Completion
	   GCB_LEN_CPL	          : out std_logic_vector(11 downto 0);		-- Completion Length
   
      -- Output interface -------------------------------------------------
      DATA                  : out std_logic_vector( 63 downto 0 ); -- Data or Header
      SOP_N                 : out std_logic;                       -- Start of Packet
      EOP_N                 : out std_logic;                       -- End of Packet
      SRC_RDY_N             : out std_logic;                       -- Source Ready
      DST_RDY_N             : in  std_logic                        -- Destination Ready
  );
end PCIE_IB_GENERATOR;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of PCIE_IB_GENERATOR is

   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------


   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
   signal trn_reset       : std_logic;

   signal hdr0_low        : std_logic_vector(31 downto 0);
   signal hdr0_high       : std_logic_vector(31 downto 0);
   signal hdr1            : std_logic_vector(63 downto 0);

   signal in_length       : std_logic_vector(11 downto 0);
   signal in_tag          : std_logic_vector(7  downto 0);
   signal in_local_addr   : std_logic_vector(31 downto 0);
   signal in_return_addr  : std_logic_vector(31 downto 0);
   signal in_request_id   : std_logic_vector(15 downto 0);
   signal in_type         : std_logic_vector( 1 downto 0);
   signal in_last         : std_logic;


   signal dec_sop_n_pipe  : std_logic;
   signal output_mux_sel  : std_logic_vector(1 downto 0);

   signal in_data         : std_logic_vector( 63 downto 0 );  -- Data or Header
   signal in_sop_n        : std_logic;                        -- Start of Packet
   signal in_eop_n        : std_logic;                        -- End of Packet
   signal in_src_rdy_n    : std_logic;                        -- Source Ready
   signal in_dst_rdy_n    : std_logic;                        -- Destination Ready

   signal out_data        : std_logic_vector( 63 downto 0 ); -- Data or Header
   signal out_sop_n       : std_logic;                       -- Start of Packet
   signal out_eop_n       : std_logic;                       -- End of Packet
   signal out_src_rdy_n   : std_logic;                       -- Source Ready
   signal out_dst_rdy_n   : std_logic;                       -- Destination Ready
   signal tag_mux         : std_logic_vector(7 downto 0);
   signal tag_mux_sel     : std_logic;
   signal first_hdr_vld   : std_logic;
   signal second_hdr_vld  : std_logic;
   signal type_dec_reg    : std_logic_vector(1 downto 0);

   -- align unit interface
   signal in_lower_addr       : std_logic_vector(2 downto 0);
   signal align_unit_data     : std_logic_vector(63 downto 0);
   signal align_unit_sop_n    : std_logic;
   signal align_unit_eop_n    : std_logic;
   signal align_unit_src_rdy_n: std_logic;
   signal align_unit_dst_rdy_n: std_logic;
   

begin

-- DEC_READ_TRANS_EN_N <= LCB_TRANS_EN_N;
trn_reset           <= not TRN_RESET_N;

-- -------------------------------------------------------------------------
-- -- Input Pipeline
-- -------------------------------------------------------------------------
GEN_INPUT_PIPE : if (INPUT_PIPE) generate
IN_IB_PIPE_U : entity work.IB_PIPE
   generic map (
      DATA_WIDTH     => 64
   )   
   port map (
      -- Common interface --------------------------------------------------
      CLK            => TRN_CLK,
      RESET          => trn_reset,
      -- Input interface ---------------------------------------------------
      IN_DATA        => DEC_DATA,
      IN_SOF_N       => DEC_SOP_N,
      IN_EOF_N       => DEC_EOP_N,
      IN_SRC_RDY_N   => DEC_SRC_RDY_N,
      IN_DST_RDY_N   => DEC_DST_RDY_N,
      -- Output interface --------------------------------------------------
      OUT_DATA       => in_data,
      OUT_SOF_N      => in_sop_n,
      OUT_EOF_N      => in_eop_n,
      OUT_SRC_RDY_N  => in_src_rdy_n,
      OUT_DST_RDY_N  => in_dst_rdy_n
   );
end generate;

GEN_NO_INPUT_PIPE : if (not INPUT_PIPE) generate
   in_data       <= DEC_DATA;
   in_sop_n      <= DEC_SOP_N;
   in_eop_n      <= DEC_EOP_N;
   in_src_rdy_n  <= DEC_SRC_RDY_N;
   DEC_DST_RDY_N <= in_dst_rdy_n;
end generate;

-- -------------------------------------------------------------------------
-- -- Align Unit
-- -------------------------------------------------------------------------
   GEN_ALIGN_UNIT : if (ENABLE_ALIGN_UNIT) generate
      RX_ALIGN_UNIT_U : entity work.RX_ALIGN_UNIT
         port map(
            -- Common interface ---------------------------
            CLK                   => TRN_CLK,
            RESET                 => trn_reset,
            -- Input interface ----------------------------
            IN_DATA               => out_data,
            IN_SOP_N              => out_sop_n,
            IN_EOP_N              => out_eop_n,
            IN_SRC_RDY_N          => out_src_rdy_n,
            IN_DST_RDY_N          => out_dst_rdy_n,
            IN_SRC_ADDR           => in_lower_addr,
            -- Output interface ---------------------------
            OUT_DATA              => align_unit_data,
            OUT_SOP_N             => align_unit_sop_n,
            OUT_EOP_N             => align_unit_eop_n,
            OUT_SRC_RDY_N         => align_unit_src_rdy_n,
            OUT_DST_RDY_N         => align_unit_dst_rdy_n
         );
   end generate;

   GEN_NO_ALIGN_UNIT : if (not ENABLE_ALIGN_UNIT) generate
      align_unit_data         <= out_data;
      align_unit_sop_n        <= out_sop_n;
      align_unit_eop_n        <= out_eop_n;
      align_unit_src_rdy_n    <= out_src_rdy_n;
      out_dst_rdy_n           <= align_unit_dst_rdy_n;
   end generate;
   
-- -------------------------------------------------------------------------
-- -- Output Pipeline
-- -------------------------------------------------------------------------
   GEN_OUTPUT_PIPE : if (OUTPUT_PIPE) generate
      OUT_IB_PIPE_U : entity work.IB_PIPE
         generic map (
            DATA_WIDTH     => 64
         )  
         port map (
            -- Common interface ---------------------------
            CLK            => TRN_CLK,
            RESET          => trn_reset,
            -- Input interface ----------------------------
            IN_DATA        => align_unit_data,
            IN_SOF_N       => align_unit_sop_n,
            IN_EOF_N       => align_unit_eop_n,
            IN_SRC_RDY_N   => align_unit_src_rdy_n,
            IN_DST_RDY_N   => align_unit_dst_rdy_n,
            -- Output interface ---------------------------
            OUT_DATA       => DATA,
            OUT_SOF_N      => SOP_N,
            OUT_EOF_N      => EOP_N,
            OUT_SRC_RDY_N  => SRC_RDY_N,
            OUT_DST_RDY_N  => DST_RDY_N
         );
   end generate;
   
   GEN_NO_OUTPUT_PIPE : if (not OUTPUT_PIPE) generate
         DATA                 <= align_unit_data;
         SOP_N                <= align_unit_sop_n;
         EOP_N                <= align_unit_eop_n;
         SRC_RDY_N            <= align_unit_src_rdy_n;
         align_unit_dst_rdy_n <= DST_RDY_N;
   end generate;

-- -------------------------------------------------------------------------
-- -- Data to fields mapping
-- -------------------------------------------------------------------------
  in_length      <= in_data(11 downto 0);
  in_type        <= in_data(13 downto 12);
  in_last        <= in_data(14) when (in_type="11") else '0';
  in_tag         <= in_data(25 downto 18);
  in_local_addr  <= in_data(63 downto 32);
  in_lower_addr  <= '0' & in_data(16 downto 15); 
  in_return_addr <= in_data(31 downto 0);
  in_request_id  <= in_data(47 downto 32);

  first_hdr_vld <= not in_src_rdy_n and not in_sop_n;
  second_hdr_vld <= not dec_sop_n_pipe and not in_src_rdy_n;

  ---------------------------------------------------------------------------------
  -- HEADERS REMAPING
  ---------------------------------------------------------------------------------
  hdr1      <= X"00000000" & in_return_addr;
  hdr0_low  <=  X"00" & tag_mux & in_last & in_type(1) & '0' & in_type(0) & in_length;
  hdr0_high <= GCB_LOCAL_ADDR when (in_type(1) = '1') else in_local_addr;

  ---------------------------------------------------------------------------------
  -- Global buffer mapping
  ---------------------------------------------------------------------------------      
  GCB_RD     	         <= '1' when (first_hdr_vld='1' and out_dst_rdy_n='0' and in_type = "11") else '0'; -- Read Request
  GCB_GLOBAL_TAG        <= in_tag;
  GCB_LAST_CPL	         <= in_last;          						  -- Last Completion
  GCB_LEN_CPL	         <= in_length;                        	  -- Completion Length

  ---------------------------------------------------------------------------------
  -- Local buffer mapping
  ---------------------------------------------------------------------------------
  LCB_TAG               <= in_tag;
  LCB_WR_0	            <= '1' when (LCB_ALLOW='1' and first_hdr_vld='1' and out_dst_rdy_n='0' and in_type = "01")
                           else '0';
  LCB_REQ_ID	         <= in_request_id;
  LCB_WR_1		         <= '1' when (second_hdr_vld='1' and out_dst_rdy_n='0' and type_dec_reg = "01") -- Don't need allow
                           else '0';	
  ---------------------------------------------------------------------------------
  -- SOP_PIPE
  ---------------------------------------------------------------------------------
  -- register dec_sop_n_pipe ------------------------------------------------------
  dec_sop_n_pipep: process(TRN_RESET_N, TRN_CLK)
  begin
    if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
        dec_sop_n_pipe <= '1';
      elsif ( in_src_rdy_n = '0' and in_dst_rdy_n = '0') then
        dec_sop_n_pipe <= in_sop_n;
      end if;
    end if;
  end process;

  -- register type_dec_reg ------------------------------------------------------
  type_dec_regp: process(TRN_RESET_N, TRN_CLK)
  begin
    if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
        type_dec_reg <= (others => '0');
      elsif (first_hdr_vld='1') then
        type_dec_reg <= in_type;
      end if;
    end if;
  end process;


tag_mux_sel <= '0' when in_type = "01" else '1'; -- 0 when read request
--multiplexor tag_mux------------------------------------------------------
tag_muxp: process(tag_mux_sel, LCB_LOCAL_TAG, GCB_LOCAL_TAG)
begin
   case tag_mux_sel is
      when '0' => tag_mux <= LCB_LOCAL_TAG;
      when '1' => tag_mux <= GCB_LOCAL_TAG;
      when others => tag_mux <= (others => 'X');
   end case;
end process;

  ---------------------------------------------------------------------------------
  -- Header and data mapping
  ---------------------------------------------------------------------------------
  output_mux_sel <= in_sop_n & dec_sop_n_pipe;

  output_mux: process(output_mux_sel, hdr0_low, hdr0_high, hdr1, in_data)
    begin
      case output_mux_sel is
        when "01" =>  out_data  <= hdr0_high & hdr0_low;
        when "10" =>  out_data  <= hdr1;
       when others => out_data  <= in_data;
      end case;
    end process;

  out_sop_n      <= in_sop_n;
  out_eop_n      <= in_eop_n;
  out_src_rdy_n  <= '1' when (in_src_rdy_n='1' or (in_type = "01" and LCB_ALLOW='0' and first_hdr_vld='1'))  else '0';
  in_dst_rdy_n   <= '1' when (out_dst_rdy_n='1' or (in_type = "01" and LCB_ALLOW='0' and first_hdr_vld='1')) else '0';


end architecture FULL;

