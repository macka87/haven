--
-- obuf_xgmii.vhd: XGMII Output Buffer
-- Copyright (C) 2008 CESNET
-- Author(s): Polcak Libor <polcak_l@liberouter.org>
--            Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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

use work.math_pack.all;
use work.xgmii_obuf_pkg.all;
use work.lb_pkg.all;
use work.fifo_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture obuf_xgmii_arch of obuf_xgmii is

   -- internal signals
   signal clk_int          : std_logic;
   signal reset_int        : std_logic;
   signal reset_xgmii      : std_logic;
   signal reset_fl         : std_logic;
   signal reset_mi         : std_logic;
   signal txdcm_lock       : std_logic;

   -- sdr2ddr input signals
   signal txd_int          : std_logic_vector(63 downto 0);
   signal txc_int          : std_logic_vector(7 downto 0);

begin


   -- -----------------------------------------------------------------
   --                           SDR OBUF
   -- -----------------------------------------------------------------

   sdrobufi: entity work.obuf_xgmii_sdr
   generic map(
      CTRL_CMD          => CTRL_CMD,
      FL_WIDTH_RX       => FL_WIDTH_RX,
      DFIFO_SIZE        => DFIFO_SIZE,
      HFIFO_SIZE        => HFIFO_SIZE,
      HFIFO_MEMTYPE     => HFIFO_MEMTYPE
   )
   port map(
      CLK_INT           => clk_int,
      RESET_XGMII       => reset_xgmii,
      XGMII_SDR_TXD     => txd_int,
      XGMII_SDR_TXC     => txc_int,

      RX_SOF_N          => RX_SOF_N,
      RX_SOP_N          => RX_SOP_N,
      RX_EOP_N          => RX_EOP_N,
      RX_EOF_N          => RX_EOF_N,
      RX_SRC_RDY_N      => RX_SRC_RDY_N,
      RX_DST_RDY_N      => RX_DST_RDY_N,
      RX_DATA           => RX_DATA,
      RX_REM            => RX_REM,
      FL_CLK            => FL_CLK,
      RESET_FL          => reset_fl,

      OUTGOING_PCKT     => OUTGOING_PCKT,

      MI                => MI,
      MI_CLK            => MI_CLK,
      RESET_MI          => reset_mi
   );

   -- -----------------------------------------------------------------
   --                           SDR2DDR
   -- -----------------------------------------------------------------

   -- SDR to DDR converter instantion
   XGMII_TXi: entity work.xgmii_tx
   port map(
      -- XGMII TX_CLK.
      XGMII_TX_CLK           => XGMII_TXCLK,
      -- XGMII TXD (Data driven onto XGMII).
      XGMII_TXD              => XGMII_TXD,
      -- XGMII TXC (Data Delimiters driven onto XGMII).
      XGMII_TXC              => XGMII_TXC,
      -- Global Asynchronous Reset.
      RESET                  => reset_int,
      -- Reference TX_CLK provided by user (156.25MHz)
      TX_CLK_REF             => TX_CLK_REF,
      -- Internal TX_CLK (use for Tx synchronous logic).
      TX_CLK_INT             => clk_int,
      -- Internal TXD at Single Data Rate.
      TXD_INT                => txd_int,
      -- Internal TXC at Single Data Rate.
      TXC_INT                => txc_int,
      -- The Locked signal from the TX DCM.                  
      TX_DCM_LOCK            => txdcm_lock,
      -- Manual reset of Tx DCM.
      TX_DCM_RESET           => RESET
   );

   -- -----------------------------------------------------------------
   --                       Synchronous reset
   -- -----------------------------------------------------------------

   reset_int <= not txdcm_lock;

   -- Reset for FL_CLK domain
   reset_flp: process(FL_CLK)
   begin
      if (FL_CLK'event and FL_CLK='1') then
         reset_fl <= not txdcm_lock;
      end if;
   end process;

   -- Reset for clk_int domain
   reset_xgmiip: process(clk_int)
   begin
      if (clk_int'event and clk_int='1') then
         reset_xgmii <= not txdcm_lock;
      end if;
   end process;

   -- Reset for MI_CLK domain
   reset_mip: process(MI_CLK)
   begin
      if (MI_CLK'event and MI_CLK='1') then
         reset_mi <= not txdcm_lock;
      end if;
   end process;

end architecture obuf_xgmii_arch;
-- ----------------------------------------------------------------------------
