--
-- ibuf_gmii_rx.vhd: Input buffer for GMII - receive part
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
--            Jan Pazdera <pazdera@liberouter.org>
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

use work.cnt_types.all;
use work.math_pack.all;
use work.ibuf_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity ibuf_gmii_rx is
   generic(
      -- true: FCS is kept in the frame
      -- false: FCS is cut out during processing
      INBANDFCS   : boolean := false
   );
   port(
      RESET     : in  std_logic;

      -- RX gmii interface
      RXCLK   : in  std_logic;
      RXDV    : in  std_logic;
      RXER    : in  std_logic;
      RXD     : in  std_logic_vector(7 downto 0);

      -- PHY status interface
      LINK_STATUS       : in std_logic; -- 0: link down, 1: link up
      DUPLEX_MODE       : in std_logic; -- 0: half duplex, 1: full duplex
      SPEED             : in std_logic_vector(1 downto 0); -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
      SGMII             : in std_logic; -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
                                        -- 1: SGMII mode active, the PHY status ports are valid
      -- ibuf_gmii_buf interface
      DO      : out std_logic_vector(7 downto 0);
      DO_DV   : out std_logic;
      STAT    : out t_ibuf_rx_stat;
      SOP     : out std_logic;
      EOP     : out std_logic;
      FSM_STATE:out std_logic_vector(2 downto 0)
   );
end entity ibuf_gmii_rx;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ibuf_gmii_rx is

   function get_sh_reg_len(INBANDFCS : boolean) return integer is
   begin
      if INBANDFCS = true then
         return 3;
      else
         return 3+4;
      end if;
   end function;

   constant C_SH_REG_LEN : integer := get_sh_reg_len(INBANDFCS);

   constant C_PREAM_LEN : integer :=  7;

   constant C_PREAM     : std_logic_vector(7 downto 0) := "01010101";
   constant C_SFD       : std_logic_vector(7 downto 0) := "11010101";

   signal pream : std_logic;
   signal sfd   : std_logic;

   signal cnt_pream : std_logic_vector(LOG2(C_PREAM_LEN+2)-1 downto 0);
   signal cnt_pream_ce : std_logic;
   signal cnt_pream_ce_ns : std_logic;
   signal cnt_pream_ovf : std_logic;

   signal init    : std_logic;
   signal err_flag : std_logic;

   signal crc_dv : std_logic;
   signal crc_eop : std_logic;
   signal fsm_crc_eop : std_logic;
   signal crc_res_rdy : std_logic;
   signal reg_crc_dv : std_logic;
   signal reg_crc_dv_i : std_logic;
   signal bad_crc    : std_logic;
   signal reg_bad_crc: std_logic;
   signal crc : std_logic_vector(31 downto 0);
   signal fcs : std_logic_vector(31 downto 0);

   signal reg_rx_data1 : std_logic_vector(7 downto 0);
   signal reg_rx_data2 : std_logic_vector(7 downto 0);
   signal reg_rx_data3 : std_logic_vector(7 downto 0);
   signal reg_rx_data4 : std_logic_vector(7 downto 0);
   signal reg_rx_data5 : std_logic_vector(7 downto 0);
   signal reg_rx_er1 : std_logic;
   signal reg_rx_er2 : std_logic;
   signal reg_rx_er3 : std_logic;
   signal reg_rx_er4 : std_logic;
   signal fsm_rx_er  : std_logic;
   signal reg_rx_dv1 : std_logic;
   signal reg_rx_dv2 : std_logic;
   signal reg_rx_dv3 : std_logic;
   signal reg_rx_dv4 : std_logic;
   signal reg_fcs1 : std_logic_vector(7 downto 0);
   signal reg_fcs2 : std_logic_vector(7 downto 0);
   signal reg_fcs3 : std_logic_vector(7 downto 0);
   signal reg_fcs4 : std_logic_vector(7 downto 0);
   signal reg_fcs_we : std_logic;

   -- Shift registers
   signal shreg_sop     : std_logic;
   signal shreg_eop     : std_logic;
   signal shreg_do_dv   : std_logic_vector(C_SH_REG_LEN-1 downto 0);
   signal reg_stat      : t_ibuf_rx_stat;

   signal pld_end : std_logic;
   signal crc_end : std_logic;

   signal reg_rxd_i  : std_logic_vector(7 downto 0);
   signal reg_rxdv_i : std_logic;
   signal reg_rxer_i : std_logic;
   signal sop_tx_i : std_logic;
   signal eop_tx_i : std_logic;
   signal dv_tx_i : std_logic;
   signal reg_sop_tx : std_logic;

   -- Payload length counter
   signal cnt_frame_len : std_logic_vector(15 downto 0);
   signal cnt_frame_len_load : std_logic;
   signal cnt_frame_len_ce : std_logic;

   -- SGMII logic
   signal sgmii_dv : std_logic;
   signal cnt_sgmii : std_logic_vector(6 downto 0);
   signal cnt_sgmii_load : std_logic;
   signal cnt_sgmii_ce : std_logic;
   signal cnt_sgmii_ovf : std_logic;
   signal cnt_sgmii_ovf_10 : std_logic;
   signal cnt_sgmii_ovf_100 : std_logic;

begin
   -- shift gmii signals 180'
   process (RXCLK, RESET)
   begin
      if (RESET='1') then
         reg_rxdv_i <= '0';
         reg_rxer_i <= '0';
      elsif (RXCLK='1' and RXCLK'event) then
         if (sgmii_dv = '1') then
            reg_rxdv_i <= RXDV;
            reg_rxer_i <= RXER;
         end if;
      end if;
   end process;

   process (RXCLK, RESET)
   begin
      if (RXCLK='1' and RXCLK'event) then
         if (sgmii_dv = '1') then
            reg_rxd_i  <= RXD;
         end if;
      end if;
   end process;

   -- fsm instantination
   RX_FSM_U : entity work.ibuf_gmii_rx_fsm
      generic map(
         INBANDFCS   => INBANDFCS
      )
      port map(
         CLK       => RXCLK,
         RESET     => RESET,
         EN        => sgmii_dv,
   
         RXDV        => reg_rx_dv4,
         RXER        => fsm_rx_er,
         PREAM       => pream,
         PREAM_OVF   => cnt_pream_ovf,
         SFD         => sfd,
         PLD_END     => pld_end,
         CRC_END     => crc_end,
   
         PREAM_CE    => cnt_pream_ce_ns,
         DO_DV       => dv_tx_i,
         CRC_DV      => crc_dv,
         CRC_EOP     => fsm_crc_eop,
         ERR_FLAG    => err_flag,
         INIT        => init,
         SOP         => sop_tx_i,
         EOP         => eop_tx_i,
         REG_CRC_WE  => reg_fcs_we,
         STATE       => FSM_STATE
      );

   fsm_rx_er <= reg_rx_er4 or reg_rxer_i;
   pld_end   <= reg_rx_dv4 and (not reg_rxdv_i);
   crc_end   <= reg_rx_dv4 and (not reg_rx_dv3);


   -- register reg_sop_tx
   reg_sop_txp: process(RESET, RXCLK)
   begin
      if (RXCLK'event AND RXCLK = '1') then
         if (sgmii_dv = '1') then
            reg_sop_tx <= sop_tx_i;
         end if;
      end if;
   end process;

   -- preamble counter --------------------------------------------------------
   cnt_pream_ovf <= '1' when (cnt_pream = conv_std_logic_vector(C_PREAM_LEN, cnt_pream'length))
	          else '0';

   cnt_pream_ce <= cnt_pream_ce_ns and sgmii_dv;
   cnt_pream_u : entity work.cnt
   generic map(
      WIDTH => LOG2(C_PREAM_LEN+2),
      DIR   => up,
      CLEAR => true
   )
   port map(
      RESET => RESET,
      CLK   => RXCLK,
      DO    => cnt_pream,
      CLR   => init,
      CE    => cnt_pream_ce
   );

   -- preamble comparator -----------------------------------------------------
   pream <= '1' when (reg_rx_data4 = C_PREAM) else '0';
   
   -- sfd comparator ----------------------------------------------------------
   sfd <= '1' when (reg_rx_data4 = C_SFD) else '0';

   -- DV and ERR registers ----------------------------------------------------
   reg_p : process(RESET, RXCLK)
   begin
      if (RESET='1') then
         reg_rx_dv1 <= '0';
         reg_rx_dv2 <= '0';
         reg_rx_dv3 <= '0';
         reg_rx_dv4 <= '0';
         reg_rx_er1 <= '0';
         reg_rx_er2 <= '0';
         reg_rx_er3 <= '0';
         reg_rx_er4 <= '0';
      elsif (RXCLK='1' and RXCLK'event) then
         if (sgmii_dv = '1') then
            reg_rx_dv1 <= reg_rxdv_i;
            reg_rx_dv2 <= reg_rx_dv1;
            reg_rx_dv3 <= reg_rx_dv2;
            reg_rx_dv4 <= reg_rx_dv3;
            reg_rx_er1 <= reg_rxer_i;
            reg_rx_er2 <= reg_rx_er1;
            reg_rx_er3 <= reg_rx_er2;
            reg_rx_er4 <= reg_rx_er3;
         end if;
      end if;
   end process;

   -- --------------------------------------------------------------------------
   -- Shift register for data
   process (RXCLK)
   begin
      if (RXCLK='1' and RXCLK'event) then
         if (sgmii_dv = '1') then
            reg_rx_data1 <= reg_rxd_i;
            reg_rx_data2 <= reg_rx_data1;
            reg_rx_data3 <= reg_rx_data2;
            reg_rx_data4 <= reg_rx_data3;
            reg_rx_data5 <= reg_rx_data4;
         end if;
      end if;
   end process;

   -- --------------------------------------------------------------------------
   -- FCS register
   process (RXCLK)
   begin
      if (RXCLK='1' and RXCLK'event) then
         if (sgmii_dv='1' and reg_fcs_we='1') then
            reg_fcs1 <= reg_rxd_i;
            reg_fcs2 <= reg_fcs1;
            reg_fcs3 <= reg_fcs2;
            reg_fcs4 <= reg_fcs3;
         end if;
      end if;
   end process;

   -- --------------------------------------------------------------------------
   -- Payload length counter
   cnt_frame_len_load  <= sop_tx_i and sgmii_dv;
   cnt_frame_len_ce    <= reg_rx_dv4 and sgmii_dv;
   process(RESET, RXCLK)
   begin
      if (RXCLK'event AND RXCLK = '1') then
         if (cnt_frame_len_load = '1') then
            cnt_frame_len <= conv_std_logic_vector(1, cnt_frame_len'length);
         elsif (cnt_frame_len_ce='1') then
            cnt_frame_len <= cnt_frame_len + 1;
         end if;
      end if;
   end process;

   crc_eop <= fsm_crc_eop and sgmii_dv;

   -- crc computation part ----------------------------------------------------
   CRC32_8B_U : entity work.crc32_8b
   port map(
      CLK   => RXCLK,
      RESET => RESET,

      DI    => reg_rx_data5,
      DI_DV => reg_crc_dv,
      EOP   => crc_eop,

      RDY   => open,
      CRC   => crc,
      DO_DV => crc_res_rdy
   );
   reg_crc_dv <= reg_crc_dv_i and sgmii_dv;
   
   process(RESET, RXCLK)
   begin
      if (RESET='1') then
         reg_bad_crc <= '0';
      elsif (RXCLK='1' and RXCLK'event) then
         if (crc_res_rdy='1') then
            reg_bad_crc <= bad_crc;
         end if;
      end if;
   end process;

   reg_crc_p : process(RESET, RXCLK)
   begin
      if (RESET='1') then
         reg_crc_dv_i <= '0';
      elsif (RXCLK='1' and RXCLK'event) then
         if (crc_res_rdy='1') then
            reg_crc_dv_i <= '0';
         elsif (sgmii_dv='1') then
            reg_crc_dv_i <= crc_dv;
         end if;
      end if;
   end process;
   
   fcs <= reg_fcs4 & reg_fcs3 & reg_fcs2 & reg_fcs1;

   -- crc fcs comparator
   bad_crc <= '0' when (crc=fcs) else '1';

   -- Output part -------------------------------------------------------------
   -- Shift registers to synchronise EOP with valid statistic data
   sh_reg_data: entity work.sh_reg_bus
      generic map (
         NUM_BITS    => C_SH_REG_LEN,
         DATA_WIDTH  => 8
      )
      port map (
         CLK      => RXCLK,

         DIN      => reg_rx_data5,
         CE       => sgmii_dv,
         DOUT     => DO
      );

   sh_reg_sop: entity work.sh_reg
      generic map (
         NUM_BITS    => C_SH_REG_LEN
      )
      port map (
         CLK      => RXCLK,

         DIN      => reg_sop_tx,
         CE       => sgmii_dv,
         DOUT     => shreg_sop
      );

   sh_reg_eop: entity work.sh_reg
      generic map (
         NUM_BITS    => C_SH_REG_LEN
      )
      port map (
         CLK      => RXCLK,

         DIN      => eop_tx_i,
         CE       => sgmii_dv,
         DOUT     => shreg_eop
      );

   -- Registers for data valid
   process(RXCLK, RESET)
   begin
      if RESET='1' then
         shreg_do_dv(0) <= '0';
      elsif (RXCLK'event and RXCLK='1') then
         if sgmii_dv = '1' then
            shreg_do_dv(0) <= dv_tx_i;
         end if;
      end if;
   end process;

   shreg_do_dv_gen: for i in 1 to shreg_do_dv'length-1 generate
      process(RXCLK, RESET)
      begin
         if RESET='1' then
            shreg_do_dv(i) <= '0';
         elsif (RXCLK'event and RXCLK='1') then
            if sgmii_dv = '1' then
               shreg_do_dv(i) <= shreg_do_dv(i-1);
            end if;
         end if;
      end process;
   end generate;

   -- Statistic data for packet
   process(RXCLK, RESET)
   begin
      if RESET = '1' then
         reg_stat.GMII_ERROR <= '0';
         reg_stat.CRC_CHECK_FAILED <= '0';
      elsif (RXCLK'event and RXCLK='1') then
         if sgmii_dv = '1' then
            if eop_tx_i = '1' then
               reg_stat.GMII_ERROR <= '0';
               reg_stat.CRC_CHECK_FAILED <= '0';
            else
               reg_stat.GMII_ERROR <= reg_stat.GMII_ERROR or err_flag;
               reg_stat.CRC_CHECK_FAILED <= reg_stat.CRC_CHECK_FAILED or reg_bad_crc or err_flag;
            end if;
            if shreg_do_dv(shreg_do_dv'length-1) = '1' then
               reg_stat.FRAME_LEN <= cnt_frame_len;
            end if;
         end if;
      end if;
   end process;

   -- output signal assignment ------------------------------------------------
   STAT <= reg_stat;
   SOP <= shreg_sop and sgmii_dv;
   EOP <= shreg_eop and sgmii_dv;
   DO_DV <= shreg_do_dv(shreg_do_dv'length-1) and sgmii_dv;

   -- -------------------------------------------------------------
   -- SGMII logic
   -- -------------------------------------------------------------
   sgmii_dv <= '1' when SGMII = '0' else
               cnt_sgmii_ovf;
   
   cnt_sgmii_ovf_10 <= '1' when cnt_sgmii = "1100011" else
                       '0';
   cnt_sgmii_ovf_100 <= '1' when cnt_sgmii = "0001001" else
                        '0';
   cnt_sgmii_ovf <= cnt_sgmii_ovf_10 when SPEED = "00" else
                    cnt_sgmii_ovf_100 when SPEED = "01" else
                    '1'; -- 1000Mb: all data are relevant

-- cnt_sgmii counter : 
cnt_sgmii_ce <= '1';
cnt_sgmii_load <= cnt_sgmii_ovf;
process(RESET, RXCLK)
begin
   if (RESET = '1') then
      cnt_sgmii <= (others => '0');
   elsif (RXCLK'event AND RXCLK = '1') then
      if (cnt_sgmii_load = '1') then
         cnt_sgmii <= "0000000";
      elsif (cnt_sgmii_ce='1') then
         cnt_sgmii <= cnt_sgmii + 1;
      end if;
   end if;
end process;

end architecture full;
