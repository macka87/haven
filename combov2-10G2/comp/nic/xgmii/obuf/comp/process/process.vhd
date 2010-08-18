-- process.vhd: Architecture of XGMII OBUF's Process part
-- Copyright (C) 2008 CESNET
-- Author(s): Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
--            Libor Polcak <polcak_l@liberouter.org>
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
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;


-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture obuf_xgmii_process_arch of obuf_xgmii_process is

   -- ----- Constants definition -----
   -- length of sr_reg
   constant CONST_SH_REG_LEN        : integer := 3;

   -- meaning of bits in shift register
   constant CONST_DATA_MAX_BIT_POS     : integer := 63;
   constant CONST_DATA_MIN_BIT_POS     : integer := 0;
   constant CONST_SOP_POS              : integer := 0;
   constant CONST_EOP_POS              : integer := 1;
   constant CONST_EOP_POS_MAX_BIT_POS  : integer := 4;
   constant CONST_EOP_POS_MIN_BIT_POS  : integer := 2;
   --constant CONST_DV_POS               : integer := 5;
   constant CONST_SH_REG_CTRL_WIDTH    : integer := CONST_EOP_POS_MAX_BIT_POS + 1;

   -- ----- Signals declaration -----
   -- fsmrx outputs
   signal fsmrx_padding    : std_logic;
   signal fsmrx_dst_rdy    : std_logic;
   signal fsmrx_eop        : std_logic;
   signal fsmrx_dv         : std_logic;
   signal fsmrx_cnt_pad_ce : std_logic;
   signal fsmrx_cnt_pad_ld : std_logic;
   
   -- counter
   signal cnt_pad          : std_logic_vector(2 downto 0);
   
   -- select units
   signal select_mx        : std_logic_vector(7 downto 0);
   signal select_eop_pos   : std_logic_vector(2 downto 0);
   
   -- pipeline registers - level 1
   signal reg1_data        : std_logic_vector(63 downto 0);
   signal reg1_mx_select   : std_logic_vector(7 downto 0);
   signal reg1_sop         : std_logic;
   signal reg1_eop         : std_logic;
   signal reg1_dv          : std_logic;
   signal reg1_eop_pos     : std_logic_vector(2 downto 0);
   
   -- zero for padding
   signal mx_zero          : std_logic_vector(63 downto 0);
   
   -- data with padding
   signal mx_data          : std_logic_vector(63 downto 0);

   -- replacing src MAC
   signal reg_sop_delay    : std_logic;
   signal src_mac_mx_sel1  : std_logic;
   signal src_mac_mx_sel2  : std_logic;
   signal src_mac_mx1      : std_logic_vector(15 downto 0);
   signal src_mac_mx2      : std_logic_vector(31 downto 0);
   
   -- pipeline registers - level 2
   signal reg2_data        : std_logic_vector(63 downto 0);
   signal reg2_sop         : std_logic;
   signal reg2_eop         : std_logic;
   signal reg2_dv          : std_logic;
   signal reg2_eop_pos     : std_logic_vector(2 downto 0);
   
   -- Pipeline control signals
   signal pipe_rd          : std_logic;
   signal pipe_rd_n        : std_logic;
   signal rx_pipe_rd       : std_logic;
   signal pipe_ce          : std_logic;

   -- CRC related signals
   signal eop_pos_crc      : std_logic_vector(2 downto 0);
   signal crc_di_dv        : std_logic;
   signal crc_reset        : std_logic;
   signal crc_data         : std_logic_vector (63 downto 0);
   signal crc_mask         : std_logic_vector (2 downto 0);
   signal crc_eop          : std_logic;
   signal reg_crc_eop      : std_logic;
   signal crc_do           : std_logic_vector (31 downto 0);
   signal crc_do_dv        : std_logic;
   signal reg_crc_ready    : std_logic;
   
   -- CRC output transform to NBO (network byte order)
   signal crc_do_nbo       : std_logic_vector (31 downto 0);
   
   -- shift register
   signal sh_reg_data_in   : std_logic_vector(63 downto 0);
   signal sh_reg_data_out  : std_logic_vector(63 downto 0);
   signal sh_reg_ctrl_in   : std_logic_vector(CONST_SH_REG_CTRL_WIDTH-1 downto 0);
   signal sh_reg_ctrl_out  : std_logic_vector(CONST_SH_REG_CTRL_WIDTH-1 downto 0);

   -- Outuput pipe
   signal rx_pipe_data     : std_logic_vector(68 downto 0);
   signal tx_pipe_data     : std_logic_vector(68 downto 0);
   signal rx_pipe_dst_rdy  : std_logic;
   signal tx_pipe_empty    : std_logic;


   signal reg_tx_sop       : std_logic;
   signal reg_tx_eop       : std_logic;
   signal reg_tx_eop_pos   : std_logic_vector(2 downto 0);
   signal reg_tx_dv0       : std_logic;
   signal reg_tx_dv1       : std_logic;
   signal reg_tx_dv2       : std_logic;

begin

   -- -------------------------------------------------------------------------
   --                            FSMRX instantion
   -- -------------------------------------------------------------------------

   fsmrx: entity work.obuf_xgmii_process_fsmrx
   
      port map(
         CLK               => CLK,
         RESET             => RESET,

         -- FSM inputs
         LAST_PAD_WORD     => cnt_pad,
         RX_SOP            => RX_SOP,
         RX_EOP            => RX_EOP,
         RX_DV             => RX_DV,
         PIPE_RD           => rx_pipe_rd,

         -- FSM otputs
         FSMRX_DST_RDY     => fsmrx_dst_rdy,
         FSMRX_PADDING     => fsmrx_padding,
         FSMRX_EOP         => fsmrx_eop,
         FSMRX_DV          => fsmrx_dv,
         FSMRX_CNT_PAD_CE  => fsmrx_cnt_pad_ce,
         FSMRX_CNT_PAD_LD  => fsmrx_cnt_pad_ld
      );

   RX_DST_RDY <= fsmrx_dst_rdy;
   pipe_ce <= rx_pipe_rd;

   -- -------------------------------------------------------------------------
   --                                cnt_pad
   -- -------------------------------------------------------------------------

   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (RESET='1' or fsmrx_cnt_pad_ld='1') then
            cnt_pad <= (others => '0');
         elsif (fsmrx_cnt_pad_ce='1' and cnt_pad<"111") then
            cnt_pad <= cnt_pad + 1;
         end if;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                                Select units
   -- -------------------------------------------------------------------------

   -- MX select
   process (fsmrx_padding, cnt_pad, RX_EOP_POS, RX_EOP, RX_DV)
   begin
      select_mx <= "00000000"; -- implicit is no padding
      if fsmrx_padding = '1' then
         if RX_EOP='1' and RX_DV='1' then
            -- packet shorter than 60b
            case (RX_EOP_POS) is
               when "000" => select_mx <= "11111110";
               when "001" => select_mx <= "11111100";
               when "010" => select_mx <= "11111000";
               when "011" => select_mx <= "11110000";
               when "100" => select_mx <= "11100000";
               when "101" => select_mx <= "11000000";
               when "110" => select_mx <= "10000000";
               when "111" => select_mx <= "00000000";
               when others => select_mx <= (others => '0');
            end case;
         elsif cnt_pad /= "111" then
            select_mx <= "11111111"; -- add whole word as padding
         else
            select_mx <= "00001111"; -- add half word as padding, rest is CRC
         end if;
      end if;
   end process;


   -- eop_pos select
   process (RX_EOP, RX_DV, RX_EOP_POS, fsmrx_padding)
   begin
      select_eop_pos <= RX_EOP_POS; -- EOP_POS is default value
      if fsmrx_padding = '1' then
         if RX_EOP = '1' and RX_DV = '1' then
            if RX_EOP_POS < "011" then
               select_eop_pos <= "011";
            end if;
         else
            select_eop_pos <= "011";
         end if;
      end if;
   end process;
   
   
   -- -------------------------------------------------------------------------
   --                 Generic byte multiplexer instantion
   -- -------------------------------------------------------------------------

   -- signal with padding value
   mx_zero <= (others => '0');

   mux_64: entity work.gen_byte_mx_2
   
      generic map(
         size => 8
      )
      port map(
         -- data inputs
         DATA_IN_1   => reg1_data,
         DATA_IN_2   => mx_zero,
         -- select signal
         SEL         => reg1_mx_select,
         -- data output
         DATA_OUT    => mx_data
      );
      

   -- -------------------------------------------------------------------------
   --                    Pipeline registers - level 1
   -- -------------------------------------------------------------------------
   
   -- reg1_data
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (pipe_ce='1') then
            reg1_data <= RX_DATA;
         end if;
      end if;
   end process;
      
   
   -- reg1_mx_select
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (pipe_ce='1') then
            reg1_mx_select <= select_mx;
         end if;
      end if;
   end process;
   
   
   -- reg1_sop
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (RESET = '1') then
            reg1_sop <= '0';
         elsif (pipe_ce='1') then
            reg1_sop <= RX_SOP and rx_pipe_rd and RX_DV;
         end if;
      end if;
   end process;
   
   
   -- reg1_eop
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (pipe_ce='1') then
            reg1_eop <= fsmrx_eop;
         end if;
      end if;
   end process;
   
   
   -- reg1_dv
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (RESET='1') then
            reg1_dv <= '0';
         elsif (pipe_ce='1') then
            reg1_dv <= fsmrx_dv;
         end if;
      end if;
   end process;
   
   
   -- reg1_eop_pos
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (pipe_ce='1') then
            reg1_eop_pos <= select_eop_pos;
         end if;
      end if;
   end process;
   
   
   -- -------------------------------------------------------------------------
   --                   Source MAC address replacement
   -- -------------------------------------------------------------------------
   
   -- reg_sop_delay
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (pipe_ce='1') then
            reg_sop_delay <= reg1_sop;
         end if;
      end if;
   end process;
   
   
   -- Setting up select signals for multiplexers
   src_mac_mx_sel1 <= SRC_MAC_RPLC and reg1_sop;
   src_mac_mx_sel2 <= SRC_MAC_RPLC and reg_sop_delay;
   
   -- NEXT_SRC_MAC_RPLC = '1' when SRC MAC was replaced
   NEXT_SRC_MAC_RPLC <= reg_sop_delay and reg1_dv and pipe_ce;
   
   
   -- src_mac_mx1
   process (src_mac_mx_sel1, mx_data, REG_MAC_ADDR)
   begin
      case src_mac_mx_sel1 is
         when '1' => src_mac_mx1 <= REG_MAC_ADDR(47 downto 32);
         when '0' => src_mac_mx1 <= mx_data(63 downto 48);
         when others => null;
      end case;
   end process;
   
   
   -- src_mac_mx2
   process (src_mac_mx_sel2, mx_data, REG_MAC_ADDR)
   begin
      case src_mac_mx_sel2 is
         when '1' => src_mac_mx2 <= REG_MAC_ADDR(31 downto 0);
         when '0' => src_mac_mx2 <= mx_data(31 downto 0);
         when others => null;
      end case;
   end process;
   
   
   -- -------------------------------------------------------------------------
   --                    Pipeline registers - level 2
   -- -------------------------------------------------------------------------

   -- reg2_data
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (pipe_ce='1') then
            reg2_data <= src_mac_mx1 & mx_data(47 downto 32) & src_mac_mx2;
         end if;
      end if;
   end process;


   -- reg2_sop
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (pipe_ce='1') then
            reg2_sop <= reg1_sop;
         end if;
      end if;
   end process;


   -- reg2_eop
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (pipe_ce='1') then
            reg2_eop <= reg1_eop;
         end if;
      end if;
   end process;


   -- reg2_dv
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (RESET='1') then
            reg2_dv <= '0';
         elsif (pipe_ce='1') then
            reg2_dv <= reg1_dv;
         end if;
      end if;
   end process;


   -- reg2_eop_pos
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (pipe_ce='1') then
            reg2_eop_pos <= reg1_eop_pos;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                       CRC component connection
   -- -------------------------------------------------------------------------

   -- Multiplexers selector generator
   eop_pos_crc <= reg2_eop_pos;

   -- Mask generation (multiplexer)
   process(crc_eop, eop_pos_crc)
   begin
      if crc_eop = '0' then
         crc_mask <= (others => '1');
      else
         crc_mask <= eop_pos_crc;
      end if;
   end process;

   -- Change endianity to correct one for the CRC module
   crc_data(63 downto 56) <= reg2_data( 7 downto  0);
   crc_data(55 downto 48) <= reg2_data(15 downto  8);
   crc_data(47 downto 40) <= reg2_data(23 downto 16);
   crc_data(39 downto 32) <= reg2_data(31 downto 24);
   crc_data(31 downto 24) <= reg2_data(39 downto 32);
   crc_data(23 downto 16) <= reg2_data(47 downto 40);
   crc_data(15 downto  8) <= reg2_data(55 downto 48);
   crc_data( 7 downto  0) <= reg2_data(63 downto 56);


   crc_di_dv <= reg2_dv and pipe_ce;
   crc_reset <= reg2_sop and pipe_ce;
   crc_eop <= reg2_eop and crc_di_dv;

   -- Register reg_crc_ready
   process(CLK)
   begin
      if (CLK='1' and CLK'event) then
         reg_crc_ready <= not (crc_di_dv and reg2_eop);
      end if;
   end process;

   crc: entity work.v5_crc
      generic map(
         INPUT_PIPE        => false,
         -- output register pipe
         OUTPUT_PIPE       => false,
         -- input CRC32 data width, only 32 or 64
         INPUT_WIDTH       => 64,
         -- CRC module init value
         CRC_INIT          => X"FFFFFFFF"
      )
      port map(
         CLK                => CLK,

         -- CRC inputs
         CRCRESET           => crc_reset,
         DATA_IN            => crc_data,
         DATA_VLD           => crc_di_dv,
         DATA_WIDTH         => crc_mask,

         -- CRC outputs
         CRC_OUT            => crc_do
      );

   reg_crc_eopp: process(CLK, RESET)
   begin
      if (RESET = '1') then
         reg_crc_eop <= '0';
      elsif (CLK'event and CLK = '1') then
         reg_crc_eop <= crc_eop;
      end if;
   end process;

   crc_do_dvp: process(CLK, RESET)
   begin
      if (RESET = '1') then
         crc_do_dv <= '0';
      elsif (CLK'event and CLK = '1') then
         crc_do_dv <= reg_crc_eop;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                        CRC output transform
   -- -------------------------------------------------------------------------

   crc_do_nbo(31 downto 24) <= crc_do(7 downto 0);
   crc_do_nbo(23 downto 16) <= crc_do(15 downto 8);
   crc_do_nbo(15 downto 8) <= crc_do(23 downto 16);
   crc_do_nbo(7 downto 0) <= crc_do(31 downto 24);


   -- -------------------------------------------------------------------------
   --                            Shift register
   -- -------------------------------------------------------------------------

   -- data input signal
   sh_reg_data_in <= reg2_data;
   sh_reg_ctrl_in(CONST_SOP_POS) <= reg2_sop and reg2_dv and pipe_ce;
   sh_reg_ctrl_in(CONST_EOP_POS) <= reg2_eop and reg2_dv and pipe_ce;
   sh_reg_ctrl_in(CONST_EOP_POS_MAX_BIT_POS downto CONST_EOP_POS_MIN_BIT_POS) <= reg2_eop_pos;

   -- Shift register instantion (data)
   sh_reg: entity work.sh_reg_bus
      generic map(
         NUM_BITS       => CONST_SH_REG_LEN,
         DATA_WIDTH     => 64
      )
      port map(
         CLK            => CLK,

         -- sh_reg inputs
         DIN            => sh_reg_data_in,
         CE             => pipe_rd,

         -- sh_reg output
         DOUT           => sh_reg_data_out
      );

   -- Shift register instantion (control signals)
   sh_reg_ctrli: entity work.sh_reg_bus
      generic map(
         NUM_BITS       => CONST_SH_REG_LEN-1,
         DATA_WIDTH     => CONST_SH_REG_CTRL_WIDTH
      )
      port map(
         CLK            => CLK,

         -- sh_reg inputs
         DIN            => sh_reg_ctrl_in,
         CE             => pipe_rd,

         -- sh_reg output
         DOUT           => sh_reg_ctrl_out
      );

   process(CLK)
   begin
      if (CLK'event and CLK='1') then
         if pipe_rd = '1' then
            reg_tx_sop <= sh_reg_ctrl_out(CONST_SOP_POS);
            reg_tx_eop <= sh_reg_ctrl_out(CONST_EOP_POS);
            reg_tx_eop_pos <= sh_reg_ctrl_out(CONST_EOP_POS_MAX_BIT_POS
                                          downto CONST_EOP_POS_MIN_BIT_POS);
         end if;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event and CLK='1') then
         if RESET = '1' then
            reg_tx_dv0 <= '0';
         elsif pipe_rd = '1' then
            reg_tx_dv0 <= reg2_dv and pipe_ce;
         end if;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event and CLK='1') then
         if RESET = '1' then
            reg_tx_dv1 <= '0';
         elsif pipe_rd = '1' then
            reg_tx_dv1 <= reg_tx_dv0 and pipe_rd;
         end if;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event and CLK='1') then
         if RESET = '1' then
            reg_tx_dv2 <= '0';
         elsif pipe_rd = '1' then
            reg_tx_dv2 <= reg_tx_dv1 and pipe_rd;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                           Pipeline control
   -- -------------------------------------------------------------------------

   --pipe_rd <= rx_pipe_dst_rdy or not reg_tx_dv2;
   rx_pipe_rd <= pipe_rd and reg_crc_ready;

   -- -------------------------------------------------------------------------
   --                     Pipeline to allow full speed
   -- -------------------------------------------------------------------------

   rx_pipe_data <= (reg_tx_eop_pos) & -- eop_pos
                   (reg_tx_eop and reg_tx_dv2) & -- eop
                   (reg_tx_sop and reg_tx_dv2) & -- sop
                   sh_reg_data_out; -- data

   tx_fifo: entity work.sh_fifo
      generic map (
         FIFO_WIDTH     => 69,
         FIFO_DEPTH     => 4, -- depth of FIFO >= 2
         USE_INREG      => false, -- use registers on input of write ifc.
         USE_OUTREG     => false  -- use registers on output of read ifc.
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,

         -- write interface
         DIN            => rx_pipe_data,
         WE             => reg_tx_dv2,
         FULL           => pipe_rd_n,

         -- read interface
         DOUT           => tx_pipe_data,
         RE             => TX_DATA_READ,
         EMPTY          => tx_pipe_empty,

         -- status
         STATUS         => open
      );

   pipe_rd <= not pipe_rd_n;
   TX_DV <= not tx_pipe_empty;

   -- -------------------------------------------------------------------------
   --                           Process outputs
   -- -------------------------------------------------------------------------

   TX_DATA           <= tx_pipe_data(63 downto 0);
   TX_SOP            <= tx_pipe_data(64);
   TX_EOP            <= tx_pipe_data(65);
   TX_EOP_POS        <= tx_pipe_data(68 downto 66);
   TX_CRC_DV         <= crc_do_dv;
   TX_CRC            <= crc_do_nbo;

end architecture obuf_xgmii_process_arch;
