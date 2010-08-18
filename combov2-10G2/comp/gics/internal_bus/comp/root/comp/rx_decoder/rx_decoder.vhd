 --
-- pcie_rx_decoder.vhd : PCIE RX decoder
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

library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity PCIE_RX_DECODER is
   generic(
      INPUT_REG_EN     : boolean := false;
      OUTPUT_REG_EN    : boolean := false;
      -- BAR base addresses
      BRIDGE_BASE_ADDR : std_logic_vector(31 downto 0) := X"FFFFFFF0"; -- IB Base Address
      BAR0_REMAP       : std_logic_vector(31 downto 0) := X"01000000"; -- BAR0 base address for PCIE->IB transalation
      BAR1_REMAP       : std_logic_vector(31 downto 0) := X"02000000"; -- BAR1 base address for PCIE->IB transalation
      BAR2_REMAP       : std_logic_vector(31 downto 0) := X"03000000"; -- BAR2 base address for PCIE->IB transalation
      BAR3_REMAP       : std_logic_vector(31 downto 0) := X"04000000"; -- BAR3 base address for PCIE->IB transalation
      BAR4_REMAP       : std_logic_vector(31 downto 0) := X"06000000"; -- BAR4 base address for PCIE->IB transalation
      BAR5_REMAP       : std_logic_vector(31 downto 0) := X"08000000"; -- BAR5 base address for PCIE->IB transalation       
      EXP_ROM_REMAP    : std_logic_vector(31 downto 0) := X"0A000000"; -- ROM  base address for PCIE->IB transalation
      -- BAR base addresses masks
      BAR0_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR0 mask for PCIE->IB transalation
      BAR1_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR1 mask for PCIE->IB transalation
      BAR2_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR2 mask for PCIE->IB transalation
      BAR3_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR3 mask for PCIE->IB transalation
      BAR4_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR4 mask for PCIE->IB transalation
      BAR5_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR5 mask for PCIE->IB transalation       
      EXP_ROM_MASK     : std_logic_vector(31 downto 0) := X"01FFFFFF"  -- ROM  mask for PCIE->IB transalation             
   ); 
  port (
    -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N           : in  std_logic; 
      TRN_CLK               : in  std_logic; 
   
    -- PCI Express RX interface ---------------------------------------------
      -- Basic signals
      TRN_RBAR_HIT_N        : in  std_logic_vector( 6 downto 0 );  -- BAR Hit ([0] -BAR0, [6] - Expansion ROM Address
      TRN_RSOF_N            : in  std_logic;                       -- Start-of-Frame (SOF)
      TRN_REOF_N            : in  std_logic;                       -- End-of-Frame (EOF)
      TRN_RD                : in  std_logic_vector( 63 downto 0 ); -- Data
      TRN_RREM_N            : in  std_logic_vector( 7 downto 0 );  -- Data Remainder (only 00000000 (valid on [63:0]) or 00001111 (valid on [63:32])
      TRN_RSRC_RDY_N        : in  std_logic;                       -- Source Ready
      TRN_RDST_RDY_N        : out std_logic;                       -- Destination Ready
      -- Error and advanced signals
      TRN_RERRFWD_N         : in  std_logic;                       -- Error Forward (Asserted by the core for entire packet - remove packet)
--       TRN_RNP_OK_N          : out std_logic;                       -- Receive Non-Posted OK (Set by IB generator)

    -- IB Generator interface ---------------------------------------------
      -- Data and header interface
      DATA                  : out std_logic_vector( 63 downto 0 ); -- Data or Header
      SOP_N                 : out std_logic;                       -- Start of Packet
      EOP_N                 : out std_logic;                       -- End of Packet
      SRC_RDY_N             : out std_logic;                       -- Source Ready
      DST_RDY_N             : in  std_logic                       -- Destination Ready
--       READ_TRANS_EN_N       : in  std_logic                       -- Enable Read transaction receiving
  );
end PCIE_RX_DECODER;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of PCIE_RX_DECODER is


   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------

   constant TRN_READ  : std_logic_vector(1 downto 0) := "01";
   constant TRN_WRITE : std_logic_vector(1 downto 0) := "00";
   constant TRN_COMPL : std_logic_vector(1 downto 0) := "11";
   constant TRN_UNK   : std_logic_vector(1 downto 0) := "10";


   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   -- Input pipeline register
   signal in_trn_rbar_hit_n   : std_logic_vector( 6 downto 0 );
   signal in_trn_rsof_n       : std_logic;
   signal in_trn_reof_n       : std_logic;
   signal in_trn_rd           : std_logic_vector( 63 downto 0 );
   signal in_trn_rrem_n       : std_logic_vector( 7 downto 0 );
   signal in_trn_rsrc_rdy_n   : std_logic;
   signal in_trn_rdst_rdy_n   : std_logic;
   signal in_trn_rerrfwd_n    : std_logic;

   -- Output pipeline register
   signal out_data            : std_logic_vector( 63 downto 0 ); 
   signal out_sop_n           : std_logic;                      
   signal out_eop_n           : std_logic;                   
   signal out_src_rdy_n       : std_logic;                     
   signal out_dst_rdy_n       : std_logic;                    

   -- Header 0 signals   
   signal trn_fmt             : std_logic_vector( 1 downto 0);
   signal trn_type            : std_logic_vector( 4 downto 0);
   signal trn_tc              : std_logic_vector( 2 downto 0);
   signal trn_attr            : std_logic_vector( 1 downto 0);
   signal trn_length          : std_logic_vector( 9 downto 0);

   -- Header 1 signals 
   signal trn_first_be        : std_logic_vector( 3 downto 0);
   signal trn_last_be         : std_logic_vector( 3 downto 0);
   signal trn_request_id      : std_logic_vector(15 downto 0);
   signal trn_tag             : std_logic_vector( 7 downto 0);
   signal trn_byte_count      : std_logic_vector(11 downto 0);
   signal trn_byte_count_zero : std_logic;

   -- Header 3 signals
   signal trn_compl_tag       : std_logic_vector( 7 downto 0);
   signal trn_lower_address   : std_logic_vector(2 downto 0); -- Only 3 bits
   signal trn_low_address32   : std_logic_vector(29 downto 0);

   -- Header 4 signals
   signal trn_low_address64   : std_logic_vector(29 downto 0);

   -- Generated header signals
   signal hdr0                : std_logic_vector(63 downto 0);
   signal hdr1                : std_logic_vector(63 downto 0);

   -- Command decoder signals
   signal command_dec_in      : std_logic_vector(6 downto 0);
   signal command_dec_out     : std_logic_vector(1 downto 0);

   -- Length decoder signals  
   signal aux_len_dec_in      : std_logic_vector(7  downto 0);
   signal aux_len_dec_out     : std_logic_vector(2  downto 0);
   signal rw_len_dec_out      : std_logic_vector(11 downto 0);
   signal cmpl_len_mux_in0    : std_logic_vector(11 downto 0);
   signal cmpl_len_mux_in1    : std_logic_vector(11 downto 0);
   signal cmpl_len_dec_out    : std_logic_vector(11 downto 0);
   signal len_dec_out         : std_logic_vector(11 downto 0);

   -- Last CPL decoder
   signal cpl_last_dec        : std_logic;
   -- Tag decoder
   signal tag_mux             : std_logic_vector(7 downto 0);

   -- Local address decoder
   signal bar_base            : std_logic_vector(31 downto 0); 
   signal bar_mask            : std_logic_vector(31 downto 0);
   signal low_addr_32_64_mux  : std_logic_vector(29 downto 0);
   signal local_addr          : std_logic_vector(31 downto 0);
   signal local_addr_low_bits : std_logic_vector( 1 downto 0);

   -- Data realign and multiplexor
   signal data_core           : std_logic_vector(31 downto 0);
   signal data_pipe           : std_logic_vector(63 downto 0);

   signal hdr_data_mux        : std_logic_vector(63 downto 0);
   signal hdr_data_mux_sel    : std_logic_vector(1 downto 0);

   signal pipe_reg            : std_logic_vector(63 downto 0);
   signal pipe_reg_we         : std_logic;
 
   signal reg_no_data         : std_logic;
   signal reg_3dw             : std_logic;

   signal pipe_trn_reof_n     : std_logic;
   signal unsupported         : std_logic;
   signal fsm_control_we      : std_logic;
   signal trn_rem             : std_logic;
   signal shift_32            : std_logic;
   signal reg_shift_32        : std_logic;
   signal hdr_data_mux_sel_in : std_logic_vector(3 downto 0);
   signal gen_hdr0            : std_logic;
   signal gen_hdr1            : std_logic;
   signal last_data           : std_logic;
   signal data_vld            : std_logic;
   signal pipe_trn_rsrc_rdy_n : std_logic;
   signal trn_request_id_reg  : std_logic_vector(15 downto 0);
   signal data_input_pipe_out : std_logic_vector(79 downto 0);
   signal data_input_pipe_in  : std_logic_vector(79 downto 0);
   signal trn_reset           : std_logic;
  
begin

-------------------------------------------------------------------------------
-- Empty and other signal mapping (START)
-------------------------------------------------------------------------------
   
--    TRN_RNP_OK_N         <= READ_TRANS_EN_N;
   trn_reset            <= not TRN_RESET_N;

-------------------------------------------------------------------------------
-- Empty and other signal mapping (END)
-------------------------------------------------------------------------------


-------------------------------------------------------------------------------
-- Input pipeline (START)                                                               
-------------------------------------------------------------------------------
  GEN_INPUT_REG : if (INPUT_REG_EN) generate

   data_input_pipe_in <= TRN_RD & TRN_RBAR_HIT_N & TRN_RREM_N & TRN_RERRFWD_N;

   IN_IB_PIPE_U : entity work.IB_PIPE
   generic map (
      DATA_WIDTH     => 80
      )   
   port map (
      -- Common interface --------------------------------------------------
      CLK            => TRN_CLK,
      RESET          => trn_reset,
      -- Input interface ---------------------------------------------------
      IN_DATA        => data_input_pipe_in,
      IN_SOF_N       => TRN_RSOF_N,
      IN_EOF_N       => TRN_REOF_N,
      IN_SRC_RDY_N   => TRN_RSRC_RDY_N,
      IN_DST_RDY_N   => TRN_RDST_RDY_N,
      -- Output interface --------------------------------------------------
      OUT_DATA       => data_input_pipe_out,
      OUT_SOF_N      => in_trn_rsof_n,
      OUT_EOF_N      => in_trn_reof_n,
      OUT_SRC_RDY_N  => in_trn_rsrc_rdy_n,
      OUT_DST_RDY_N  => in_trn_rdst_rdy_n
   );

    in_trn_rd         <= data_input_pipe_out(79 downto 16);
    in_trn_rbar_hit_n <= data_input_pipe_out(15 downto 9);
    in_trn_rrem_n     <= data_input_pipe_out(8 downto 1);
    in_trn_rerrfwd_n  <= data_input_pipe_out(0);
  end generate;

  GEN_NOT_INPUT_REG : if (not INPUT_REG_EN) generate
    in_trn_rbar_hit_n <= TRN_RBAR_HIT_N;
    in_trn_rsof_n     <= TRN_RSOF_N;
    in_trn_reof_n     <= TRN_REOF_N;
    in_trn_rd         <= TRN_RD;
    in_trn_rrem_n     <= TRN_RREM_N;
    in_trn_rsrc_rdy_n <= TRN_RSRC_RDY_N;
    TRN_RDST_RDY_N    <= in_trn_rdst_rdy_n;
    in_trn_rerrfwd_n  <= TRN_RERRFWD_N;
  end generate;
-------------------------------------------------------------------------------
-- Input pipeline (END)                                                               
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Output pipeline (START)
-------------------------------------------------------------------------------
  GEN_OUTPUT_REG : if (OUTPUT_REG_EN) generate
    out_pipep: process(TRN_RESET_N, TRN_CLK)
    begin
      if (TRN_CLK'event AND TRN_CLK = '1') then
        if (TRN_RESET_N = '0') then
          SOP_N     <= '1';
          EOP_N     <= '1';
          SRC_RDY_N <= '1';
        elsif (DST_RDY_N = '0') then
          DATA            <= out_data;
          SOP_N           <= out_sop_n;
          EOP_N           <= out_eop_n;
          SRC_RDY_N       <= out_src_rdy_n;
        end if;
      end if;
    end process;
    out_dst_rdy_n   <= DST_RDY_N;
  end generate;

  GEN_NOT_OUTPUT_REG : if (not OUTPUT_REG_EN) generate
      DATA            <= out_data;
      SOP_N           <= out_sop_n;
      EOP_N           <= out_eop_n;
      SRC_RDY_N       <= out_src_rdy_n;
      out_dst_rdy_n   <= DST_RDY_N;
  end generate;
-------------------------------------------------------------------------------
-- Output pipeline (END)
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Header fields mapping (START)
-------------------------------------------------------------------------------
--  hdr 1
trn_fmt           <= pipe_reg(62 downto 61);
trn_type          <= pipe_reg(60 downto 56);
trn_tc            <= pipe_reg(54 downto 52);
trn_attr          <= pipe_reg(45 downto 44);
trn_length        <= pipe_reg(41 downto 32);

--  hdr 2
trn_first_be      <= pipe_reg( 3 downto  0);
trn_last_be       <= pipe_reg( 7 downto  4);
trn_request_id    <= pipe_reg(31 downto 16);
trn_tag           <= pipe_reg(15 downto  8);
trn_byte_count    <= pipe_reg(11 downto  0);

--  hdr 3
trn_compl_tag        <= in_trn_rd(47 downto 40);
trn_lower_address    <= in_trn_rd(34 downto 32);
trn_low_address32    <= in_trn_rd(63 downto 34);

-- hdr 4
trn_low_address64 <= in_trn_rd(31 downto 2);

-- data mapping
data_core         <= in_trn_rd(39 downto 32) & in_trn_rd(47 downto 40) &
                     in_trn_rd(55 downto 48) & in_trn_rd(63 downto 56);

data_pipe         <= pipe_reg(7 downto 0) & pipe_reg(15 downto 8) & pipe_reg(23 downto 16)
                     & pipe_reg(31 downto 24) & pipe_reg(39 downto 32) & pipe_reg(47 downto 40)
                     & pipe_reg(55 downto 48) & pipe_reg(63 downto 56);

-- rem
trn_rem <= '1' when in_trn_rrem_n ="00000000" else '0';

-------------------------------------------------------------------------------
-- Header fields mapping (END)
-------------------------------------------------------------------------------


-------------------------------------------------------------------------------
-- Data & Control pipeline registers (START)
-------------------------------------------------------------------------------
-- register pipe_reg ------------------------------------------------------
pipe_regp: process(TRN_CLK, TRN_RESET_N)
begin
    if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
         pipe_reg            <= (others => '0');
         pipe_trn_reof_n     <= '1';
         pipe_trn_rsrc_rdy_n <= '1';
      elsif (pipe_reg_we = '1') then
         pipe_reg        <= in_trn_rd;
         pipe_trn_reof_n <= in_trn_reof_n;
         pipe_trn_rsrc_rdy_n <= in_trn_rsrc_rdy_n;
      end if;
   end if;
end process;

-- register no_data -------------------------------------------------------
reg_no_datap: process(TRN_CLK, TRN_RESET_N)
begin
   if (TRN_CLK'event AND TRN_CLK = '1' and fsm_control_we = '1') then
      if (TRN_RESET_N = '0') then
        reg_no_data <= '0';
      elsif (command_dec_out = TRN_READ) then
        reg_no_data <= '1';
      else
        reg_no_data <= '0';
      end if;
   end if;
end process;

-- register 3dw -----------------------------------------------------------
reg_3dwp: process(TRN_CLK, TRN_RESET_N)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
        reg_3dw <= '0';
      elsif (fsm_control_we = '1') then
        reg_3dw <= not trn_fmt(0);
      end if;
   end if;
end process;

shift_32 <= '1' when (low_addr_32_64_mux(0)='1' and (command_dec_out =TRN_WRITE)) else '0';

-- register shift_32 ------------------------------------------------------
reg_shift_32p: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
     if (TRN_RESET_N = '0') then
        reg_shift_32 <= '0';
     elsif (fsm_control_we = '1') then
        reg_shift_32 <= shift_32;
     end if;
   end if;
end process;


-- register trn_request_id_reg --------------------------------------------
trn_request_id_regp: process(TRN_CLK, TRN_RESET_N)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
         -- trn_request_id_reg <= (others => '0');
      elsif (fsm_control_we = '1') then
         trn_request_id_reg <= trn_request_id;
      end if;
   end if;
end process;




-------------------------------------------------------------------------------
-- Data & Control pipeline registers (STOP)
-------------------------------------------------------------------------------

-- ----------------------------------------------------------------------------
-- Command decoder (START)
-------------------------------------------------------------------------------
unsupported <= '1' when not (in_trn_rd(62 downto 56) = "0000000" or
                             in_trn_rd(62 downto 56) = "0100000" or
                             in_trn_rd(62 downto 56) = "1000000" or
                             in_trn_rd(62 downto 56) = "1100000" or
                             in_trn_rd(62 downto 56) = "1001010") else '0';

command_dec_in <= trn_fmt & trn_type;

decp: process(command_dec_in)
begin
   case command_dec_in is
      when "0000000" => command_dec_out <= TRN_READ;  -- Read transaction
      when "0100000" => command_dec_out <= TRN_READ;  -- Read transaction
      when "1000000" => command_dec_out <= TRN_WRITE; -- Write transaction
      when "1100000" => command_dec_out <= TRN_WRITE; -- Write transaction
      when "1001010" => command_dec_out <= TRN_COMPL; -- Completition transaction
      when others    => command_dec_out <= TRN_UNK;   -- Unknown transaction (used for skiping)
   end case;
end process;
-- ----------------------------------------------------------------------------
-- Command decoder (END)
-------------------------------------------------------------------------------


-------------------------------------------------------------------------------
-- Last Completition decoder (START)
-------------------------------------------------------------------------------
trn_byte_count_zero <= '1' when (trn_byte_count = 0) else '0'; -- zero (4kb) cpl


cpl_last_dec <= '1' when (trn_byte_count <= (trn_length & "00" - trn_lower_address(1 downto 0))
                          and tag_mux(4) = '1' and trn_byte_count_zero = '0')  -- Completition for last splited read request
                else '0';
-------------------------------------------------------------------------------
-- Last Completition decoder (END)
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- LEN decoder (START)
-------------------------------------------------------------------------------
len_decoderp: process(command_dec_out, rw_len_dec_out, cmpl_len_dec_out)
begin
   case command_dec_out is
      when TRN_COMPL => len_dec_out <= cmpl_len_dec_out;
      when others    => len_dec_out <= rw_len_dec_out;
   end case;
end process;


-- completition len decoder ---------------------------------------------------
cmpl_len_mux_in0 <= trn_length & "00" - trn_lower_address(1 downto 0);
cmpl_len_mux_in1 <= trn_byte_count;

compl_len_dec_outp: process(cpl_last_dec, cmpl_len_mux_in0, cmpl_len_mux_in1)
begin
   case cpl_last_dec is
      when '0'    => cmpl_len_dec_out <= cmpl_len_mux_in0;
      when '1'    => cmpl_len_dec_out <= cmpl_len_mux_in1;
      when others => cmpl_len_dec_out <= (others => 'X');
   end case;
end process;

-- r/w len decoder ------------------------------------------------------------
rw_len_dec_out   <= trn_length & "00" - aux_len_dec_out;
aux_len_dec_in <= trn_first_be & trn_last_be;

aux_len_decoder: process(aux_len_dec_in)
  begin
    case aux_len_dec_in is
      -- length = 1
      when "00000000" => aux_len_dec_out <= "011";
      when "11110000" => aux_len_dec_out <= "000";          
      when "11100000" => aux_len_dec_out <= "001";                   
      when "11000000" => aux_len_dec_out <= "010";                            
      when "10000000" => aux_len_dec_out <= "011";

      when "01110000" => aux_len_dec_out <= "001";
      when "00110000" => aux_len_dec_out <= "010";          
      when "01100000" => aux_len_dec_out <= "010";                   
      when "01000000" => aux_len_dec_out <= "011";                            
      when "00100000" => aux_len_dec_out <= "011";                            
      when "00010000" => aux_len_dec_out <= "011"; 

      -- length > 1         
      when "11111111" => aux_len_dec_out <= "000";         
      when "11101111" => aux_len_dec_out <= "001";         
      when "11001111" => aux_len_dec_out <= "010";         
      when "10001111" => aux_len_dec_out <= "011";         

      when "11110111" => aux_len_dec_out <= "001";         
      when "11100111" => aux_len_dec_out <= "010";         
      when "11000111" => aux_len_dec_out <= "011";         
      when "10000111" => aux_len_dec_out <= "100";         

      when "11110011" => aux_len_dec_out <= "010";         
      when "11100011" => aux_len_dec_out <= "011";         
      when "11000011" => aux_len_dec_out <= "100";         
      when "10000011" => aux_len_dec_out <= "101";                  

      when "11110001" => aux_len_dec_out <= "011";         
      when "11100001" => aux_len_dec_out <= "100";         
      when "11000001" => aux_len_dec_out <= "101";         
      when "10000001" => aux_len_dec_out <= "110";       
     
      when others     => aux_len_dec_out <= "XXX";   
    end case;
  end process;    
-------------------------------------------------------------------------------
-- LEN decoder (STOP)
-------------------------------------------------------------------------------

-- ----------------------------------------------------------------------------
-- TAG decoder (START)
-- ----------------------------------------------------------------------------
tag_muxp: process(command_dec_out, trn_tag, trn_compl_tag)
begin
   case command_dec_out is
      when TRN_COMPL => tag_mux <= trn_compl_tag;
      when others    => tag_mux <= trn_tag;
   end case;
end process;
-- ----------------------------------------------------------------------------
-- TAG decoder (STOP)
-- ----------------------------------------------------------------------------


-- ----------------------------------------------------------------------------
-- Local Address Decoder (START)
-- ----------------------------------------------------------------------------
-- BAR decoding and logic
bar_base_maskp: process(in_trn_rbar_hit_n)
  begin
    if (in_trn_rbar_hit_n(0) = '0') then
      bar_base  <= BAR0_REMAP;
      bar_mask  <= BAR0_MASK;        
    elsif (in_trn_rbar_hit_n(1) = '0') then
      bar_base  <= BAR1_REMAP;     
      bar_mask  <= BAR1_MASK;        
    elsif (in_trn_rbar_hit_n(2) = '0') then
      bar_base  <= BAR2_REMAP;     
      bar_mask  <= BAR2_MASK;        
    elsif (in_trn_rbar_hit_n(3) = '0') then
      bar_base  <= BAR3_REMAP;     
      bar_mask  <= BAR3_MASK;        
    elsif (in_trn_rbar_hit_n(4) = '0') then
      bar_base  <= BAR4_REMAP;     
      bar_mask  <= BAR4_MASK;        
    elsif (in_trn_rbar_hit_n(5) = '0') then
      bar_base  <= BAR5_REMAP;                     
      bar_mask  <= BAR5_MASK;        
    elsif (in_trn_rbar_hit_n(6) = '0') then
      bar_base  <= EXP_ROM_REMAP;
      bar_mask  <= EXP_ROM_MASK;
    else
      bar_base  <= (others => 'X');
      bar_mask  <= (others => 'X');
    end if;
  end process;


--multiplexor low_addr_32_64_mux------------------------------------------------------
low_addr_32_64_muxp: process(trn_fmt, trn_low_address32, trn_low_address64)
begin
   case trn_fmt(0) is
      when '0' => low_addr_32_64_mux <= trn_low_address32;
      when '1' => low_addr_32_64_mux <= trn_low_address64;
      when others => low_addr_32_64_mux <= (others => '0'); --X
   end case;
end process;


--multiplexor local_addr_low_bits_decoder --------------------------------------------
local_addr_low_bits_decoder: process(trn_first_be)
   begin
      case trn_first_be is
         when "0001" => local_addr_low_bits <= "00";
         when "0011" => local_addr_low_bits <= "00";
         when "0101" => local_addr_low_bits <= "00";
         when "0111" => local_addr_low_bits <= "00";
         when "1001" => local_addr_low_bits <= "00";
         when "1011" => local_addr_low_bits <= "00";
         when "1101" => local_addr_low_bits <= "00";
         when "1111" => local_addr_low_bits <= "00";
         when "0010" => local_addr_low_bits <= "01";          
         when "0110" => local_addr_low_bits <= "01";          
         when "1010" => local_addr_low_bits <= "01";          
         when "1110" => local_addr_low_bits <= "01";          
         when "0100" => local_addr_low_bits <= "10";          
         when "1100" => local_addr_low_bits <= "10";          
         when "1000" => local_addr_low_bits <= "11";
         when others => local_addr_low_bits <= "00"; --XX
      end case;
   end process;      

local_addr <= ((low_addr_32_64_mux & local_addr_low_bits) and bar_mask) + bar_base;

-- ----------------------------------------------------------------------------
-- Local Address Decoder (STOP)
-- ----------------------------------------------------------------------------

-- ----------------------------------------------------------------------------
-- Header generation (START)
-- ----------------------------------------------------------------------------
hdr0 <= local_addr & "0" & trn_tc & trn_attr & tag_mux & trn_lower_address &
        cpl_last_dec & command_dec_out & len_dec_out;
hdr1 <= X"0000" & trn_request_id_reg & BRIDGE_BASE_ADDR;
-- ----------------------------------------------------------------------------
-- Header generation (STOP)
-- ----------------------------------------------------------------------------



-- ----------------------------------------------------------------------------
-- DATA/HDR Multiplexor (START)
-- ----------------------------------------------------------------------------

hdr_data_mux_sel_in <= gen_hdr0 & gen_hdr1 & reg_3dw & reg_shift_32;
--hdr_data_mux sel_decoder -----------------------------------------------------------
hdr_data_mux_sel_decoderp: process(hdr_data_mux_sel_in)
   begin
      case hdr_data_mux_sel_in is
         when "0000" => hdr_data_mux_sel <= "11";
         when "0001" => hdr_data_mux_sel <= "10";
         when "0010" => hdr_data_mux_sel <= "10";
         when "0011" => hdr_data_mux_sel <= "11";
         when "0100" => hdr_data_mux_sel <= "01";
         when "0101" => hdr_data_mux_sel <= "01";
         when "0110" => hdr_data_mux_sel <= "01";
         when "0111" => hdr_data_mux_sel <= "01";
         when "1000" => hdr_data_mux_sel <= "00";
         when "1001" => hdr_data_mux_sel <= "00";
         when "1010" => hdr_data_mux_sel <= "00";
         when "1011" => hdr_data_mux_sel <= "00";
         when "1100" => hdr_data_mux_sel <= "00";
         when "1101" => hdr_data_mux_sel <= "00";
         when "1110" => hdr_data_mux_sel <= "00";
         when "1111" => hdr_data_mux_sel <= "00";
         when others => hdr_data_mux_sel <= "00";
      end case;
   end process; 

--multiplexor hdr_data_mux------------------------------------------------------
hdr_data_muxp: process(hdr_data_mux_sel, hdr0, hdr1, data_pipe, data_core, pipe_reg, in_trn_rd)
begin
   case hdr_data_mux_sel is
      when "00"   => hdr_data_mux <= hdr0;
      when "01"   => hdr_data_mux <= hdr1;
      when "10"   => hdr_data_mux <= data_core & data_pipe(63 downto 32);
      when "11"   => hdr_data_mux <= data_pipe;
      when others => hdr_data_mux <= (others => 'X');
   end case;
end process;


last_data <= (not (reg_3dw xor reg_shift_32) and not pipe_trn_reof_n) or
             (    (reg_3dw xor reg_shift_32) and ((not in_trn_reof_n and not trn_rem and not in_trn_rsrc_rdy_n) or not pipe_trn_reof_n));

data_vld  <= (not reg_3dw and not reg_shift_32 and not pipe_trn_rsrc_rdy_n) or
             ((reg_3dw or reg_shift_32) and ( not pipe_trn_reof_n or (pipe_trn_reof_n and not in_trn_rsrc_rdy_n)));



-- ----------------------------------------------------------------------------
-- DATA/HDR Multiplexor (STOP)
-- ----------------------------------------------------------------------------

-- ----------------------------------------------------------------------------
-- RX DECODER Control FSM
-- ----------------------------------------------------------------------------
PCIE_RX_DECODER_FSM_U: entity work.PCIE_RX_DECODER_FSM
    port map (
      -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N          => TRN_RESET_N,
      TRN_CLK              => TRN_CLK, 
      -- PCI Express RX interface ---------------------------------------------
      TRN_RSOF_N           => in_trn_rsof_n,        -- Start-of-Frame (SOF)
      TRN_REOF_N           => in_trn_reof_n,        -- End-of-Frame (EOF)
      TRN_RSRC_RDY_N       => in_trn_rsrc_rdy_n,    -- Source Ready
      TRN_RDST_RDY_N       => in_trn_rdst_rdy_n,    -- Destination Ready
      TRN_RERRFWD_N        => in_trn_rerrfwd_n,     -- Error Forward (Asserted by the core for entire packet - remove packet)
      
      -- Control signals from datapath ----------------------------------------
      REG_NO_DATA          => reg_no_data,          -- Transaction with no data (read request)
      REG_3DW              => reg_3dw,              -- Transaction in 3DW format
      REG_SHIFT32          => reg_shift_32,
      UNSUPPORTED          => unsupported,          -- Unsuported transaction
      LAST_DATA            => last_data,           
      DATA_VLD             => data_vld,
      -- Control signals for datapath -----------------------------------------
      GEN_HDR0             => gen_hdr0,
      GEN_HDR1             => gen_hdr1,
      FSM_CONTROL_WE       => fsm_control_we,       -- Control signal for storing 3DW and NO_DATA registers
      PIPE_REG_WE          => pipe_reg_we,          -- Enable write to pipeline
      -- Output interface control signals -------------------------------------
      SOP_N                => out_sop_n,                -- Start of Packet
      EOP_N                => out_eop_n,                -- End of Packet
      SRC_RDY_N            => out_src_rdy_n,            -- Source Ready
      DST_RDY_N            => out_dst_rdy_n             -- Destination Ready
      );

out_data <= hdr_data_mux;


end architecture FULL;
