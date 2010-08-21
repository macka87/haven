 --
-- pcie_ib_generator.vhd : PCI-e Internal Bus Generator
-- Copyright (C) 2008 CESNET
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
-- Interface from IB_DECODER
----------------------------
--                          25         22   14        2       0
-- ------------------------------------------------------------
-- |          RESERVED        | FIRST_BE | TAG  | LEN |  TYPE |
-- |                          | SRC_ADDR | G2LR |     |       |
-- ------------------------------------------------------------
-- |     ADDR_HIGH/RESERVED   |         ADDR_LOW              |
-- |                          | LOWER_ADDR | REQ_ID | CPL_TAG |
-- ------------------------------------------------------------
-- |            DATA1         |           DATA0               |
-- ------------------------------------------------------------

-- TYPE:          "00"  - Read
--                "10"  - Write
--                "11"  - Completition
-- LEN:           Length in bytes, 12 bits
-- TAG:           Transaction TAG, 8 bit (G2LR Tag, or CPL Tag)
-- FIRST_BE:      (Valid for Write and Completitions)
--                "000" - 1st byte valid 
--                "001" - 2th byte valid
--                "010" - 3th byte valid
--                "011" - 4th byte valid
--                "100" - 5th byte valid
--                     .
--                     .
-- SRC_ADDR:     (Valid for Reads)
-- ADDR_LOW:     Low Write address (32 bit)  - Valid for Read and Write
-- ADDR_HIGH:    High write address (32 bit) - Valid for Read and Write
-- REQUESTER_ID: Requester ID (16 bitu)   - Valid for Completitions
-- LOWER_ADDR:   (7bit) Lower address       - Valid for completitions
-- DATAx:        Data a) First valid byte is denoted by FIST_BE for
--               (Write and Completitions)


library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.ib_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_DECODER is
  generic (
      INPUT_PIPE	                  : boolean := false;
      DISCARD_UNSUPPORTED_IB_TRANS  : boolean := false
  );
  port (
    -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N              : in  std_logic; 
      TRN_CLK                  : in  std_logic;

    -- ----------- Internal Bus RX interface ---------------------------------
      RX_DATA                  : in  std_logic_vector( 63 downto 0 ); -- Data or Header
      RX_SOP_N                 : in  std_logic;                       -- Start of Packet
      RX_EOP_N                 : in  std_logic;                       -- End of Packet
      RX_SRC_RDY_N             : in  std_logic;                       -- Source Ready
      RX_DST_RDY_N             : out std_logic;                       -- Destination Ready

    -- ----------- PCIe Generator interface ----------------------------------
      GEN_DATA                 : out std_logic_vector( 63 downto 0 ); -- Data or Header
      GEN_SOP_N                : out std_logic;                       -- Start of Packet
      GEN_EOP_N                : out std_logic;                       -- End of Packet
      GEN_SRC_RDY_N            : out std_logic;                       -- Source Ready
      GEN_DST_RDY_N            : in  std_logic;                       -- Destination Ready
      GEN_DW4                  : out std_logic;
      GEN_DW4_VLD              : out std_logic;

    -- Local Completition Buffer Interface -----------------------------------
      LCB_TAG                  :  in std_logic_vector( 7 downto 0); 	 -- Transaction Tag     
      LCB_REQ_ID               :  in std_logic_vector(15 downto 0); 	 -- Requester ID (BUS, DEVICE, FUNCTION)
      LCB_RD                   : out std_logic;  						    -- Read Request
      LCB_RTAG                 : out std_logic_vector(7 downto 0);    -- Read Address

    -- Global Completition Buffer Interface ----------------------------------
      GCB_LOCAL_ADDR           : out std_logic_vector(31 downto 0); 	 -- Local Address
      GCB_LOCAL_TAG            : out std_logic_vector(7 downto 0);    -- Local Tag
	   GCB_WR		             : out std_logic;								 -- Write Request
      GCB_WR_ALLOW             : in  std_logic;                       -- Write Allow
	   GCB_RTAG 		          : in  std_logic_vector(7 downto 0)     -- Global Tag
  );
end IB_DECODER;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of IB_DECODER is

   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------
   constant T_READ         : std_logic_vector(1 downto 0) := "00";
   constant T_WRITE        : std_logic_vector(1 downto 0) := "10";
   constant T_COMPL        : std_logic_vector(1 downto 0) := "11";
   constant T_UNSUPPORTED  : std_logic_vector(1 downto 0) := "01";

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
   signal trn_reset             : std_logic;

   -- Re-maped Input
   signal in_rx_data            : std_logic_vector( 63 downto 0 );
   signal in_rx_sop_n           : std_logic;
   signal in_rx_eop_n           : std_logic;
   signal in_rx_src_rdy_n       : std_logic;
   signal in_rx_dst_rdy_n       : std_logic;

   -- Re-maped output
   signal out_gen_data          : std_logic_vector( 63 downto 0 );
   signal out_gen_sop_n         : std_logic;
   signal out_gen_eop_n         : std_logic;
   signal out_gen_src_rdy_n     : std_logic;
   signal out_gen_dst_rdy_n     : std_logic;

   -- First and Second word valid
   signal first_hdr_vld         : std_logic;
   signal second_hdr_vld        : std_logic;


   -- Multiplexors and registers
   signal data_low_mux          : std_logic_vector(31 downto 0);
   signal data_low_mux_sel      : std_logic_vector(1 downto 0);
   signal addr_low_reg          : std_logic_vector(31 downto 0);
   signal lower_addr            : std_logic_vector(6 downto 0);
   signal type_dec              : std_logic_vector(1 downto 0);
   signal type_dec_in           : std_logic_vector(2 downto 0);
   signal sop_n_reg             : std_logic;
   signal compl_reg             : std_logic;
   signal data_low_mux_dec_in   : std_logic_vector(2 downto 0);
   signal local_tag_reg         : std_logic_vector(7 downto 0);
   signal type_dec_reg          : std_logic_vector(1 downto 0);
   signal out_gen_dw4           : std_logic;
   signal discarding            : std_logic; -- when bad transaction type from IB

begin

trn_reset <= not TRN_RESET_N;

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
      IN_DATA        => RX_DATA,
      IN_SOF_N       => RX_SOP_N,
      IN_EOF_N       => RX_EOP_N,
      IN_SRC_RDY_N   => RX_SRC_RDY_N,
      IN_DST_RDY_N   => RX_DST_RDY_N,
      -- Output interface --------------------------------------------------
      OUT_DATA       => in_rx_data,
      OUT_SOF_N      => in_rx_sop_n,
      OUT_EOF_N      => in_rx_eop_n,
      OUT_SRC_RDY_N  => in_rx_src_rdy_n,
      OUT_DST_RDY_N  => in_rx_dst_rdy_n
   );
end generate;

GEN_NO_INPUT_PIPE : if (not INPUT_PIPE) generate
   in_rx_data      <= RX_DATA;
   in_rx_sop_n     <= RX_SOP_N;
   in_rx_eop_n     <= RX_EOP_N;
   in_rx_src_rdy_n <= RX_SRC_RDY_N;
   RX_DST_RDY_N    <= in_rx_dst_rdy_n;
end generate;

-- -------------------------------------------------------------------------
-- -- Output Pipeline
-- -------------------------------------------------------------------------
OUT_DW4_PIPE_U : entity work.DW4_PIPE
   generic map (
      DATA_WIDTH     => 64
   )  
   port map (
      -- Common interface --------------------------------------------------
      CLK            => TRN_CLK,
      RESET          => trn_reset,
      -- Input interface ---------------------------------------------------
      IN_DATA        => out_gen_data,
      IN_SOF_N       => out_gen_sop_n,
      IN_EOF_N       => out_gen_eop_n,
      IN_SRC_RDY_N   => out_gen_src_rdy_n,
      IN_DST_RDY_N   => out_gen_dst_rdy_n,
      IN_DW4         => out_gen_dw4,
      -- Output interface --------------------------------------------------
      OUT_DATA       => GEN_DATA,
      OUT_SOF_N      => GEN_SOP_N,
      OUT_EOF_N      => GEN_EOP_N,
      OUT_SRC_RDY_N  => GEN_SRC_RDY_N,
      OUT_DST_RDY_N  => GEN_DST_RDY_N,
      OUT_DW4        => GEN_DW4,
      OUT_DW4_VLD    => GEN_DW4_VLD

   );


--                             26         23   15     2      0
-- -------------------------------------------------------------
-- |          RESERVED           | FIRST_BE | TAG | LEN | TYPE |
-- |                             | SRC_ADDR |     |     |      |
-- -------------------------------------------------------------
-- |     ADDR_HIGH/RESERVED      |         ADDR_LOW            |
-- |                             | LOWER_ADDR | REQUESTER_ID   |
-- -------------------------------------------------------------


first_hdr_vld  <= not in_rx_sop_n and not in_rx_src_rdy_n;
second_hdr_vld <= not sop_n_reg and not in_rx_src_rdy_n;

-- register sop_n_reg ------------------------------------------------------
sop_n_regp: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
        sop_n_reg <= '1';
      elsif (in_rx_src_rdy_n = '0' and in_rx_dst_rdy_n = '0') then
        sop_n_reg <= in_rx_sop_n;
      end if;
   end if;
end process;

-- discarding state --------------------------------------------------------
DISCARD_STATE_GEN : if (DISCARD_UNSUPPORTED_IB_TRANS) generate
   discardingp : process(TRN_RESET_N, TRN_CLK)
   begin
      if(TRN_CLK'event AND TRN_CLK = '1') then
         if(TRN_RESET_N = '0') then
            discarding <= '0';
         elsif(first_hdr_vld = '1' and (type_dec = T_UNSUPPORTED)) then -- set
            discarding <= '1';
         elsif(in_rx_eop_n = '0' and in_rx_src_rdy_n = '0') then -- clr
            discarding <= '0';
         end if;
      end if;
   end process;
end generate;

-- -------------------------------------------------------------------------
-- -- Output interface mapping
-- -------------------------------------------------------------------------
out_gen_data       <= in_rx_data(63 downto 32) & data_low_mux;
out_gen_sop_n      <= in_rx_sop_n;
out_gen_eop_n      <= in_rx_eop_n;

DISCARD_RDY_GEN : if (DISCARD_UNSUPPORTED_IB_TRANS) generate

out_gen_src_rdy_n  <= '0' when (first_hdr_vld  = '1'  and      type_dec     = T_READ  and GCB_WR_ALLOW='1') or
                               (first_hdr_vld  = '1'  and not (type_dec     = T_READ) and not (type_dec = T_UNSUPPORTED)) or 
                               (second_hdr_vld = '1'  and      type_dec_reg = T_READ  and GCB_WR_ALLOW='1') or
                               (second_hdr_vld = '1'  and not (type_dec_reg = T_READ) and not (type_dec_reg = T_UNSUPPORTED)) or 
                               (in_rx_sop_n = '1' and sop_n_reg = '1' and in_rx_src_rdy_n = '0' and discarding = '0')
                         else '1';

in_rx_dst_rdy_n    <= '0' when (discarding = '1' or (first_hdr_vld = '1' and type_dec = T_UNSUPPORTED)) or
                              (
                                (out_gen_dst_rdy_n='0' and
                                not (first_hdr_vld = '1' and type_dec = T_READ and GCB_WR_ALLOW='0') and
                                not (second_hdr_vld = '1' and type_dec_reg = T_READ and GCB_WR_ALLOW='0'))
                              )
                          else '1';
end generate;

NOT_DISCARD_RDY_GEN : if (not DISCARD_UNSUPPORTED_IB_TRANS) generate

out_gen_src_rdy_n  <= '0' when (first_hdr_vld  = '1'  and      type_dec     = T_READ  and GCB_WR_ALLOW='1') or
                               (first_hdr_vld  = '1'  and not (type_dec     = T_READ)) or
                               (second_hdr_vld = '1'  and      type_dec_reg = T_READ  and GCB_WR_ALLOW='1') or
                               (second_hdr_vld = '1'  and not (type_dec_reg = T_READ)) or
                               (in_rx_sop_n = '1' and sop_n_reg = '1' and in_rx_src_rdy_n = '0')
                          else '1';

in_rx_dst_rdy_n    <= '0' when (out_gen_dst_rdy_n='0' and
                                 not (first_hdr_vld = '1' and type_dec = T_READ and GCB_WR_ALLOW='0') and
                                 not (second_hdr_vld = '1' and type_dec_reg = T_READ and GCB_WR_ALLOW='0'))
                          else '1';
end generate;

-- -------------------------------------------------------------------------
--                          DW4 VLD COMPUTATION                           --
-- -------------------------------------------------------------------------
out_gen_dw4 <= '0' when (in_rx_data(63 downto 32) =  0 or  -- High Address Is Zero
                         compl_reg = '1') else '1';        -- Completition


-- -------------------------------------------------------------------------
-- -- Local and global buffer signal mapping
-- -------------------------------------------------------------------------
LCB_RTAG       <= local_tag_reg;
LCB_RD         <= '1' when (second_hdr_vld = '1' and out_gen_dst_rdy_n='0' and type_dec_reg = T_COMPL) else '0';

GCB_LOCAL_TAG  <= local_tag_reg;
GCB_LOCAL_ADDR <= in_rx_data(31 downto 0);
GCB_WR		   <= '1' when (second_hdr_vld='1' and out_gen_dst_rdy_n='0' and type_dec_reg = T_READ and GCB_WR_ALLOW='1') else '0';


-- data_low_mux_dec -----------------------------------------------------------
data_low_mux_dec_in <= first_hdr_vld & sop_n_reg & compl_reg;

data_low_mux_dec_inp: process(data_low_mux_dec_in)
begin
   case data_low_mux_dec_in is
      when "010"  => data_low_mux_sel <= "00"; -- DATA
      when "011"  => data_low_mux_sel <= "00"; -- DATA
      when "110"  => data_low_mux_sel <= "01"; -- HDR0
      when "111"  => data_low_mux_sel <= "01"; -- HDR0
      when "000"  => data_low_mux_sel <= "10"; -- HDR1 (RD,WR)
      when "001"  => data_low_mux_sel <= "11"; -- HDR1 (CMPL)
      when others => data_low_mux_sel <= "XX"; -- Unknown transaction
   end case;
end process;

--multiplexor data_out_mux------------------------------------------------------
data_out_muxp: process(data_low_mux_sel, in_rx_data, type_dec, addr_low_reg, GCB_RTAG, LCB_REQ_ID, LCB_TAG, lower_addr)
begin
   case data_low_mux_sel is
                                   -- Data out
      when "00" => data_low_mux    <= in_rx_data(31 downto 0);
                                   -- FIRST_BE(src_addr), TAG, LEN, Type
      when "01" => data_low_mux    <= "0000000" & in_rx_data(34 downto 32) &
                                      GCB_RTAG & in_rx_data(11 downto 0) & type_dec;
                                   -- ADDR_LOW
      when "10" => data_low_mux    <= addr_low_reg;
                                   -- LOWER_ADDR | REQUESTER_ID | CPL_TAG
      when "11" => data_low_mux    <= "0" & lower_addr & LCB_REQ_ID & LCB_TAG;
      when others => data_low_mux <= (others => 'X');
   end case;
end process;

-- Address bits from requests + lower bits from destination address (byte enables)
lower_addr <= in_rx_data(6 downto 2) & addr_low_reg(1 downto 0);

-- type decoder ---------------------------------------------------------------
type_dec_in <= in_rx_data(14 downto 12);

DISCARD_DEC : if (DISCARD_UNSUPPORTED_IB_TRANS) generate
   typedecp: process(type_dec_in)
   begin
      case type_dec_in is
         when C_IB_G2LR_TRANSACTION     => type_dec <= T_READ;  -- Read transaction
         when C_IB_L2GW_TRANSACTION     => type_dec <= T_WRITE; -- Write transaction
         when C_IB_RD_COMPL_TRANSACTION => type_dec <= T_COMPL; -- Completition
         when C_IB_L2LW_TRANSACTION     => type_dec <= T_UNSUPPORTED; -- Discard
         when C_IB_L2LR_TRANSACTION     => type_dec <= T_UNSUPPORTED; -- Discard
         when others                    => type_dec <= "XX";   -- Unknown/Bad transaction
      end case;
   end process;
end generate;

NOT_DISCARD_DEC : if (not DISCARD_UNSUPPORTED_IB_TRANS) generate
   typedecpp: process(type_dec_in)
   begin
      case type_dec_in is
         when C_IB_G2LR_TRANSACTION     => type_dec <= T_READ;  -- Read transaction
         when C_IB_L2GW_TRANSACTION     => type_dec <= T_WRITE; -- Write transaction
         when C_IB_RD_COMPL_TRANSACTION => type_dec <= T_COMPL; -- Completition
         when others                    => type_dec <= "XX";   
      end case;
   end process;
end generate;

-- register compl_reg ------------------------------------------------------
compl_regp: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
        compl_reg <= '0';
      elsif (first_hdr_vld='1') then
         if (type_dec = T_COMPL) then
           compl_reg <= '1';
         else
           compl_reg <= '0';
         end if;
      end if;
   end if;
end process;

-- register type_dec_reg ------------------------------------------------------
type_dec_regp: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
      --   type_dec_reg <= (others => '0');
      elsif (first_hdr_vld='1') then
         type_dec_reg <= type_dec;
      end if;
   end if;
end process;


-- register addr_low_reg ------------------------------------------------------
addr_low_regp: process(TRN_CLK, TRN_RESET_N)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
    --     addr_low_reg <= (others => '0');
      elsif (first_hdr_vld='1') then
         addr_low_reg <= in_rx_data(63 downto 32);
      end if;
   end if;
end process;

-- register local_tag_reg ------------------------------------------------------
local_tag_regp: process(TRN_CLK, TRN_RESET_N)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
      --   local_tag_reg <= (others => '0');
      elsif (first_hdr_vld='1') then
         local_tag_reg <= in_rx_data(23 downto 16);
      end if;
   end if;
end process;

end architecture FULL;

