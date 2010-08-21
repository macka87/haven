--
-- obuf_gmii_tx.vhd: Output buffer for GMII - transmit part
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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
--  - interframe is 14 clk periods it must be 12
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use work.math_pack.all;

use work.cnt_types.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_gmii_tx is
   generic(
      -- Is the FCS already present in the frame? If true, the FCS will be
      -- recomputed and will substitute the original one
      INBANDFCS : boolean := false;
      -- Should the FCS computation be skipped?
      SKIP_FCS  : boolean := false
      -- NB: if SKIP_FCS is set to true (i.e. FCS is already present in the
      -- frame), INBANDFCS needs to be set to false, otherwise, the FCS from
      -- the original frame will be cut off
   );
   port(
      RESET : in  std_logic;
      REFCLK   : in  std_logic;

      -- obuf_gmii_buf interface
      DI    : in  std_logic_vector(7 downto 0);
      DI_DV : in  std_logic;
      DI_ER : in  std_logic;
      BUSY  : out std_logic;
      SGMII_DV   : in std_logic;

      -- TX gmii interface
      TXCLK : out std_logic;
      TXD   : out std_logic_vector(7 downto 0);
      TXEN  : out std_logic;
      TXER  : out std_logic

   );
end entity obuf_gmii_tx;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_gmii_tx is

   constant C_IFR_LEN   : integer :=  7; -- must be greater or equal 2
   constant C_PREAM_LEN : integer :=  7;
   constant C_FCS_LEN   : integer :=  4;

   constant C_IDLE      : std_logic_vector(7 downto 0) := X"00";
   constant C_PREAM     : std_logic_vector(7 downto 0) := "01010101";
   constant C_SFD       : std_logic_vector(7 downto 0) := "11010101";

   -- Signals connected to input or FCS remove part
   signal di_i          : std_logic_vector(7 downto 0);
   signal di_dv_i       : std_logic;
   signal di_er_i       : std_logic;
   signal di_dv_4       : std_logic;

   signal cnt_ifr_ce    : std_logic;
   signal cnt_ifr_clr   : std_logic;
   signal cnt_ifr_ovf   : std_logic;
   signal cnt_ifr       : std_logic_vector(LOG2(C_IFR_LEN-1)-1 downto 0);

   signal cnt_pream_ce  : std_logic;
   signal cnt_pream_clr : std_logic;
   signal cnt_pream_ovf : std_logic;
   signal cnt_pream     : std_logic_vector(LOG2(C_PREAM_LEN+1)-1 downto 0);

   signal cnt_fcs_ce    : std_logic;
   signal cnt_fcs_clr   : std_logic;
   signal cnt_fcs_ovf   : std_logic;
   signal cnt_fcs       : std_logic_vector(LOG2(C_FCS_LEN+1)-1 downto 0);

   signal sh_reg_data   : std_logic_vector(7 downto 0);
   signal sh_reg_er     : std_logic;
   signal sh_reg_dv     : std_logic;

   signal reg_di        : std_logic_vector(7 downto 0);
   signal reg_di_dv     : std_logic;
   signal crc_di_dv     : std_logic;
   signal crc           : std_logic_vector(31 downto 0);
   signal crc_lstd      : std_logic;

   signal mux_fcs       : std_logic_vector(7 downto 0);
   signal mux_txd       : std_logic_vector(7 downto 0);
   signal mux_er        : std_logic;

   signal do_dv         : std_logic;
   signal ifr           : std_logic;
   signal sfd           : std_logic;
   signal pream         : std_logic;
   signal data          : std_logic;
   signal fcs           : std_logic;

begin

   -- Frame is not containing FCS ---------------------------------------------
   nofcs_gen: if INBANDFCS = false generate
      di_i    <= DI;
      di_dv_i <= DI_DV;
      di_er_i <= DI_ER;
   end generate;

   -- FCS remove part ---------------------------------------------------------
   fcsremove_part: if INBANDFCS = true generate
      -- data shift register
      SH_REG_DATA_U : entity work.sh_reg_bus
      generic map(
         NUM_BITS   => 4,
         --INIT       => ;
         DATA_WIDTH => 8
      )
      port map(
         CLK      => REFCLK,
         DIN      => DI,
         CE       => SGMII_DV,
         DOUT     => di_i
      );
   
      -- di_er shift register
      SH_REG_ER_U : entity work.sh_reg
      generic map(
         NUM_BITS => 4
      )
      port map(
         CLK      => REFCLK,
         DIN      => DI_ER,
         CE       => SGMII_DV,
         DOUT     => di_er_i
      );

      -- di_dv shift register
      SH_REG_DV_U : entity work.sh_reg
      generic map(
         NUM_BITS => 4
      )
      port map(
         CLK      => REFCLK,
         DIN      => DI_DV,
         CE       => SGMII_DV,
         DOUT     => di_dv_4
      );

      di_dv_i <= di_dv_4 and DI_DV;

   end generate fcsremove_part;

   -- interframe counter ------------------------------------------------------
   cnt_ifr_ce  <= ifr and (not cnt_ifr_ovf) and SGMII_DV;
   cnt_ifr_clr <= pream and SGMII_DV;
   cnt_ifr_ovf <= '1' when (cnt_ifr = conv_std_logic_vector(C_IFR_LEN-2, cnt_ifr'length))
	          else '0';

   cnt_ifr_u : entity work.cnt
   generic map(
      WIDTH => LOG2(C_IFR_LEN-1),
      DIR   => up,
      CLEAR => true
   )
   port map(
      RESET => RESET,
      CLK   => REFCLK,
      DO    => cnt_ifr,
      CLR   => cnt_ifr_clr,
      CE    => cnt_ifr_ce
   );

   -- preamble counter --------------------------------------------------------
   cnt_pream_ce  <= pream and SGMII_DV;
   cnt_pream_clr  <= ifr and SGMII_DV;
   cnt_pream_ovf <= '1' when (cnt_pream = conv_std_logic_vector(C_PREAM_LEN, cnt_pream'length))
	          else '0';

   cnt_pream_u : entity work.cnt
   generic map(
      WIDTH => LOG2(C_PREAM_LEN+1),
      DIR   => up,
      CLEAR => true
   )
   port map(
      RESET => RESET,
      CLK   => REFCLK,
      DO    => cnt_pream,
      CLR   => cnt_pream_clr,
      CE    => cnt_pream_ce
   );

   -- fcs counter -------------------------------------------------------------
   cnt_fcs_ce  <= fcs and SGMII_DV;
   cnt_fcs_clr <= ifr and SGMII_DV;
   cnt_fcs_ovf <= '1' when (cnt_fcs = conv_std_logic_vector(C_FCS_LEN, cnt_fcs'length))
	          else '0';

   cnt_fcs_u : entity work.cnt
   generic map(
      WIDTH => LOG2(C_FCS_LEN+1),
      DIR   => up,
      CLEAR => true
   )
   port map(
      RESET => RESET,
      CLK   => REFCLK,
      DO    => cnt_fcs,
      CLR   => cnt_fcs_clr,
      CE    => cnt_fcs_ce
   );


   -- data shift register -----------------------------------------------------
   SH_REG_DATA_U : entity work.sh_reg_bus
   generic map(
      NUM_BITS   => 8,
      --INIT       => ;
      DATA_WIDTH => 8
   )
   port map(
      CLK      => REFCLK,
      DIN      => di_i,
      CE       => SGMII_DV,
      DOUT     => sh_reg_data
   );

   -- di_er shift register ----------------------------------------------------
   SH_REG_ER_U : entity work.sh_reg
   generic map(
      NUM_BITS => 8
   )
   port map(
      CLK      => REFCLK,
      DIN      => di_er_i,
      CE       => SGMII_DV,
      DOUT     => sh_reg_er
   );

   -- di_dv shift register ----------------------------------------------------
   SH_REG_DV_U : entity work.sh_reg
   generic map(
      NUM_BITS => 8
   )
   port map(
      CLK      => REFCLK,
      DIN      => di_dv_i,
      CE       => SGMII_DV,
      DOUT     => sh_reg_dv
   );

   -- -------------------------------------------------------------------------
   --                       crc computation part
   -- -------------------------------------------------------------------------
   -- registered di and di_dv
   process (REFCLK, RESET)
   begin
      if (RESET='1') then
         reg_di    <= (others=>'0');
         reg_di_dv <= '0';
      elsif (REFCLK='1' and REFCLK'event) then
         if (SGMII_DV = '1') then
            reg_di    <= di_i;
            reg_di_dv <= di_dv_i; -- can be set only if valid data occurs
         end if;
      end if;
   end process;

   crc_lstd <= reg_di_dv and not di_dv_i;

   crc_di_dv <= SGMII_DV and reg_di_dv;
   CRC32_8B_U : entity work.crc32_8b
   port map(
      DI => reg_di,
      CLK => REFCLK,
      RESET => RESET,
      DI_DV => crc_di_dv,
      EOP => crc_lstd,

      RDY => open,
      CRC => crc,
      DO_DV => open
   );

   -- fcs multiplexor ----------------------
   mux_fcs <= crc(7  downto  0) when (cnt_fcs=conv_std_logic_vector(3, cnt_fcs'length)) else
	      crc(15 downto  8) when (cnt_fcs=conv_std_logic_vector(2, cnt_fcs'length)) else
	      crc(23 downto 16) when (cnt_fcs=conv_std_logic_vector(1, cnt_fcs'length)) else
	      crc(31 downto 24);

   -- txd multiplexor ------------------------
   mux_txd <= C_PREAM     when (pream='1') else
	      C_SFD       when (sfd='1')   else
	      sh_reg_data when (data='1')  else
	      mux_fcs     when (fcs='1')   else
	      C_IDLE;

   -- er multiplexer --------------------------
   mux_er <= sh_reg_er when (data='1') else '0';

   -- fsm instantination
   TX_FSM_U : entity work.obuf_gmii_tx_fsm
   generic map(
      SKIP_FCS   => SKIP_FCS
   )
   port map(
      CLK       => REFCLK,
      RESET     => RESET,

      START     => di_dv_i,
      DV        => sh_reg_dv,
      IFR_OVF   => cnt_ifr_ovf,
      PREAM_OVF => cnt_pream_ovf,
      FCS_OVF   => cnt_fcs_ovf,
      SGMII_DV  => SGMII_DV,

      DO_DV     => do_dv,
      IFR       => ifr,
      SFD       => sfd,
      PREAM     => pream,
      DATA      => data,
      FCS       => fcs
   );

   -- output signal mapping ---------------------------------------------------
   reg_out_p: process(RESET, REFCLK)
   begin
      if (RESET='1') then
         TXD  <= (others=>'0');
         TXEN <= '0';
         TXER <= '0';
         BUSY <= '1';
      elsif (REFCLK'event and REFCLK='1') then
         if (SGMII_DV = '1') then
            TXD  <=  mux_txd;
            TXEN <=  do_dv;
            TXER <=  mux_er;
            BUSY <=  not cnt_ifr_ovf;
         end if;
      end if;
   end process;

   TXCLK <= REFCLK;
   
end architecture full;
