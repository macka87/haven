-- combo6x_sfpro_tb.vhd: Testbench of C6X + SFPRO
-- Copyright (C) 2003 CESNET
-- Author(s): Tobola Jiri tobola@liberouter.org
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

use work.ifc_addr_space.all;
use work.plx_oper.all;
use work.phy_oper.all;
use work.ibuf_pkg.all;
use work.obuf_pkg.all;
-- use work.txt_util.all; 
use work.bp_func.all;


-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant PACKET_DIR      : string := "../data/";
   constant IFC_COUNT       : integer := 4;
   constant NUM_PACKETS     : integer := 4;
   constant PACKET_SPACE    : time := 5 us;

   constant IBUF0_BASE_ADDR  : integer := IFC_TEST0_BASE_ADDR + 16#000#;
   constant IBUF1_BASE_ADDR  : integer := IFC_TEST0_BASE_ADDR + 16#100#;
   constant IBUF2_BASE_ADDR  : integer := IFC_TEST0_BASE_ADDR + 16#200#;
   constant IBUF3_BASE_ADDR  : integer := IFC_TEST0_BASE_ADDR + 16#300#;
   constant BUFFER_SIZE   : integer := 512;
   constant MBUS_WIDTH    : integer := 18;
   constant BRAM_TYPE    : integer := 32;

   constant OBUF0_BASE_ADDR  : integer := LB_SSRAM0_BASE_ADDR;
   constant OBUF1_BASE_ADDR  : integer := LB_SSRAM0_BASE_ADDR + 16#100#;
   constant OBUF2_BASE_ADDR  : integer := LB_SSRAM0_BASE_ADDR + 16#200#;
   constant OBUF3_BASE_ADDR  : integer := LB_SSRAM0_BASE_ADDR + 16#300#;

   constant BP_BASE_ADDR   : integer := IFC_TEST1_BASE_ADDR;
   constant BP_CONTROL        : integer := BP_BASE_ADDR + 16#0000#;
   constant BP_COUNTER        : integer := BP_BASE_ADDR + 16#0004#;
   constant BP_MEM            : integer := BP_BASE_ADDR + BP_MEM_BASE_ADDR(BUFFER_SIZE, MBUS_WIDTH, BRAM_TYPE); -- bus probe memory content offset
   constant clkper      : time := 20 ns;
   constant fclkper     : time := 8 ns;
   constant camclkper   : time := 40 ns;
   
   -- combo6x signals ---------------------------------------------------
   signal c6_lclkf     : std_logic;
   -- LED:
   signal c6_xled      : std_logic_vector(3 downto 0);
   -- CAM:
    -- CAM:
   signal c6_cd        : std_logic_vector(67 downto 0);
   signal c6_cop       : std_logic_vector(8 downto 0);
   signal c6_copv      : std_logic;
   signal c6_cack_n    : std_logic;
   signal c6_ceot      : std_logic;
   signal c6_cmf       : std_logic;
   signal c6_cmm_n     : std_logic;
   signal c6_cmv       : std_logic;
   signal c6_cff       : std_logic;
   signal c6_cphase    : std_logic;
   signal c6_crst_n    : std_logic;
   signal c6_cmclk     : std_logic;
   signal c6_cmclkf    : std_logic;
   signal c6_cad       : std_logic_vector(21 downto 0);
   signal c6_cce_n     : std_logic;
   signal c6_cale_n    : std_logic;
   signal c6_coe_n     : std_logic;
   signal c6_cwe_n     : std_logic;
   signal c6_csclk     : std_logic;
   signal c6_csen_n    : std_logic_vector(3 downto 0);
   -- SDRAM:
   signal dd        : std_logic_vector(63 downto 0);
   signal dcb       : std_logic_vector(7 downto 0);
   signal dba       : std_logic_vector(2 downto 0);
   signal dqs       : std_logic_vector(17 downto 0);
   signal da        : std_logic_vector(13 downto 0);
   signal dcs_n     : std_logic_vector(3 downto 0);
   signal dclke     : std_logic_vector(1 downto 0);
   signal dcas_n    : std_logic;
   signal dras_n    : std_logic;
   signal dwe_n     : std_logic;
   signal dclk      : std_logic;
   signal dclk_n    : std_logic;
   signal dclk2     : std_logic;
   signal resddr_n  : std_logic;
   signal dsda      : std_logic;
   signal dsclk     : std_logic;
   -- LB
   signal c6_x         : std_logic_vector(39 downto 0);
   -- SSRAM0:
   signal c6_s0a       : std_logic_vector(19 downto 0);
   signal c6_s0adsp_n  : std_logic;
   signal c6_s0adsc_n  : std_logic;
   signal c6_s0adv_n   : std_logic;
   signal c6_s0cs1_n   : std_logic;
   signal c6_s0cs2_n   : std_logic;
   signal c6_s0gw_n    : std_logic;
   signal c6_s0bw_n    : std_logic;
   signal c6_s0we_n    : std_logic_vector(3 downto 0);
   signal c6_s0oe_n    : std_logic;
   signal c6_s0mode    : std_logic;
   signal c6_sclk0     : std_logic;
   signal c6_s0d       : std_logic_vector(35 downto 0);
   -- SSRAM1:
   signal c6_s1a       : std_logic_vector(19 downto 0);
   signal c6_s1adsp_n  : std_logic;
   signal c6_s1adsc_n  : std_logic;
   signal c6_s1adv_n   : std_logic;
   signal c6_s1cs1_n   : std_logic;
   signal c6_s1cs2_n   : std_logic;
   signal c6_s1gw_n    : std_logic;
   signal c6_s1bw_n    : std_logic;
   signal c6_s1we_n    : std_logic_vector(3 downto 0);
   signal c6_s1oe_n    : std_logic;
   signal c6_s1mode    : std_logic;
   signal c6_sclk1     : std_logic;
   signal c6_s1d       : std_logic_vector(31 downto 0);
   -- SSRAM2:
   signal c6_s2a       : std_logic_vector(19 downto 0);
   signal c6_s2adsp_n  : std_logic;
   signal c6_s2adsc_n  : std_logic;
   signal c6_s2adv_n   : std_logic;
   signal c6_s2cs1_n   : std_logic;
   signal c6_s2cs2_n   : std_logic;
   signal c6_s2gw_n    : std_logic;
   signal c6_s2bw_n    : std_logic;
   signal c6_s2we_n    : std_logic_vector(3 downto 0);
   signal c6_s2oe_n    : std_logic;
   signal c6_s2mode    : std_logic;
   signal c6_sclk2     : std_logic;
   signal c6_s2d       : std_logic_vector(31 downto 0);
   -- RIO
   signal c6_tdn_a     : std_logic;
   signal c6_tdp_a     : std_logic;
   signal c6_rdn_a     : std_logic;
   signal c6_rdp_a     : std_logic;
   signal c6_tdn_b     : std_logic;
   signal c6_tdp_b     : std_logic;
   signal c6_rdn_b     : std_logic;
   signal c6_rdp_b     : std_logic;
   signal c6_tdn_c     : std_logic;
   signal c6_tdp_c     : std_logic;
   signal c6_rdn_c     : std_logic;
   signal c6_rdp_c     : std_logic;
   signal c6_tdn_d     : std_logic;
   signal c6_tdp_d     : std_logic;
   signal c6_rdn_d     : std_logic;
   signal c6_rdp_d     : std_logic;

   signal lvdsfp    : std_logic;
   signal lvdsfn    : std_logic;
   signal clkf      : std_logic;
   
   -- shared signals -------------------------------------------------
   signal ios          : std_logic_vector(103 downto 0);
   signal io           : std_logic_vector(43 downto 24); 
   signal c6_txn0      : std_logic; 
   signal c6_txp0      : std_logic; 
   signal c6_rxp0      : std_logic; 
   signal c6_rxn0      : std_logic; 
   signal c6_txn1      : std_logic; 
   signal c6_txp1      : std_logic; 
   signal c6_rxp1      : std_logic; 
   signal c6_rxn1      : std_logic; 
   signal c6_txn2      : std_logic; 
   signal c6_txp2      : std_logic; 
   signal c6_rxp2      : std_logic; 
   signal c6_rxn2      : std_logic; 
   signal c6_txn3      : std_logic; 
   signal c6_txp3      : std_logic; 
   signal c6_rxp3      : std_logic; 
   signal c6_rxn3      : std_logic; 


   -- SFPRO signals --------------------------------------------------
   signal sfpro_lclkf  : std_logic;
   signal sfpro_fclk   : std_logic;
   signal sfpro_xled   : std_logic_vector(3 downto 0);
   signal sfpro_tdn_a  : std_logic;
   signal sfpro_tdp_a  : std_logic;
   signal sfpro_rdn_a  : std_logic;
   signal sfpro_rdp_a  : std_logic;
   signal sfpro_tdn_b  : std_logic;
   signal sfpro_tdp_b  : std_logic;
   signal sfpro_rdn_b  : std_logic;
   signal sfpro_rdp_b  : std_logic;
   signal sfpro_tdn_c  : std_logic;
   signal sfpro_tdp_c  : std_logic;
   signal sfpro_rdn_c  : std_logic;
   signal sfpro_rdp_c  : std_logic;
   signal sfpro_tdn_d  : std_logic;
   signal sfpro_tdp_d  : std_logic;
   signal sfpro_rdn_d  : std_logic;
   signal sfpro_rdp_d  : std_logic;

    -- RIO:
   signal sfpro_txn0      : std_logic;
   signal sfpro_txp0      : std_logic;
   signal sfpro_rxp0      : std_logic;
   signal sfpro_rxn0      : std_logic;
   signal sfpro_txn1      : std_logic;
   signal sfpro_txp1      : std_logic;
   signal sfpro_rxp1      : std_logic;
   signal sfpro_rxn1      : std_logic; 

     -- SSRAM0:
   signal sfpro_s0a       : std_logic_vector(18 downto 0);
   signal sfpro_s0adsp_n  : std_logic;
   signal sfpro_s0adsc_n  : std_logic;
   signal sfpro_s0adv_n   : std_logic;
   signal sfpro_s0cs1_n   : std_logic;
   signal sfpro_s0cs2_n   : std_logic;
   signal sfpro_s0gw_n    : std_logic;
   signal sfpro_s0bw_n    : std_logic;
   signal sfpro_s0we_n    : std_logic_vector(3 downto 0);
   signal sfpro_s0oe_n    : std_logic;
   signal sfpro_s0mode    : std_logic;
   signal sfpro_sclk0     : std_logic;
   signal sfpro_s0d       : std_logic_vector(35 downto 0);
   -- SSRAM1:
   signal sfpro_s1a       : std_logic_vector(18 downto 0);
   signal sfpro_s1adsp_n  : std_logic;
   signal sfpro_s1adsc_n  : std_logic;
   signal sfpro_s1adv_n   : std_logic;
   signal sfpro_s1cs1_n   : std_logic;
   signal sfpro_s1cs2_n   : std_logic;
   signal sfpro_s1gw_n    : std_logic;
   signal sfpro_s1bw_n    : std_logic;
   signal sfpro_s1we_n    : std_logic_vector(3 downto 0);
   signal sfpro_s1oe_n    : std_logic;
   signal sfpro_s1mode    : std_logic;
   signal sfpro_sclk1     : std_logic;
   signal sfpro_s1d       : std_logic_vector(35 downto 0); 

    -- CAM:
   signal cd        : std_logic_vector(67 downto 0);
   signal cop       : std_logic_vector(8 downto 0);
   signal copv      : std_logic;
   signal cack_n    : std_logic;
   signal ceot      : std_logic;
   signal cmf       : std_logic;
   signal cmm_n     : std_logic;
   signal cmv       : std_logic;
   signal cff       : std_logic;
   signal cphase    : std_logic;
   signal crst_n    : std_logic;
   signal cmclk     : std_logic;
   signal cmclkf    : std_logic;
   signal cad       : std_logic_vector(21 downto 0);
   signal cce_n     : std_logic;
   signal cale_n    : std_logic;
   signal coe_n     : std_logic;
   signal cwe_n     : std_logic;
   signal csclk     : std_logic;
   signal csen      : std_logic_vector(3 downto 0);

   -- unused SFPRO signals
   signal sfpro_sclk0f     : std_logic;
   signal sfpro_sclk1f     : std_logic;
   -- PLX signals ---------------------------------------------------
   alias LAD0   : std_logic_vector(26 downto  0) is c6_x(26 downto  0);
   alias LAD1   : std_logic_vector(31 downto 27) is c6_x(32 downto 28);
   alias LRESET : std_logic                      is c6_x(33);
   alias LHOLD  : std_logic                      is c6_x(34);
   alias LWR    : std_logic                      is c6_x(35);
   alias READY  : std_logic                      is c6_x(36);
   alias BLAST  : std_logic                      is c6_x(37);
   alias ADS    : std_logic                      is c6_x(38);

   signal lholda : std_logic; -- FIXME

   -- plx simulation signals ----------------------------------------
   signal plx_ctrl         : t_plx_ctrl;
   signal plx_oper         : t_plx_oper := INIT;
   signal plx_params       : t_plx_params;
   signal plx_status       : t_plx_status;
   signal plx_strobe       : std_logic := '0';
   signal plx_busy         : std_logic;

   -- phyter simulation signals
   type t_phyx_oper   is array (0 to (IFC_COUNT - 1)) of t_phy_oper;
   type t_phyx_params is array (0 to (IFC_COUNT - 1)) of t_phy_params;
   type t_phyx_strobe is array (0 to (IFC_COUNT - 1)) of std_logic;
   type t_phyx_busy   is array (0 to (IFC_COUNT - 1)) of std_logic;

   type t_phyx_txclk  is array (0 to (IFC_COUNT - 1)) of std_logic;
   type t_phyx_txd    is array (0 to (IFC_COUNT - 1)) of std_logic_vector(7 downto 0);
   type t_phyx_txen   is array (0 to (IFC_COUNT - 1)) of std_logic;
   type t_phyx_txer   is array (0 to (IFC_COUNT - 1)) of std_logic;
   type t_phyx_rxclk  is array (0 to (IFC_COUNT - 1)) of std_logic;
   type t_phyx_rxd    is array (0 to (IFC_COUNT - 1)) of std_logic_vector(7 downto 0);
   type t_phyx_rxdv   is array (0 to (IFC_COUNT - 1)) of std_logic;
   type t_phyx_rxer   is array (0 to (IFC_COUNT - 1)) of std_logic;

   signal phy_oper   : t_phyx_oper;
   signal phy_params : t_phyx_params;
   signal phy_strobe : t_phyx_strobe;
   signal phy_busy   : t_phyx_busy;
   signal phy_ctrl   : t_phy_ctrl;

   signal phy_txclk  : t_phyx_txclk;
   signal phy_txd    : t_phyx_txd;
   signal phy_txen   : t_phyx_txen;
   signal phy_txer   : t_phyx_txer;
   signal phy_rxclk  : t_phyx_rxclk;
   signal phy_rxd    : t_phyx_rxd;
   signal phy_rxdv   : t_phyx_rxdv;
   signal phy_rxer   : t_phyx_rxer;
   
   -- ---------------------------------------------------------------
   signal lclkf      : std_logic;
   signal fclk       : std_logic;
   signal clkn       : std_logic;
   signal clkp       : std_logic;
   signal ethclkn    : std_logic;
   signal ethclkp    : std_logic;

   alias reset       : std_logic is ios(20); 
   signal gnd        : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

gnd <= '0';

-- ----------------------------------------------------
-- Combo6X FPGA
UUT : entity work.fpga_u5
port map(
 
   -- CLK:
   LCLKF     => c6_lclkf,

   LVDSFP    => lvdsfp,
   LVDSFN    => lvdsfn,
   CLKF      => clkf,

   -- LED:
   XLED      => c6_xled,
   -- CAM:
   CD        => c6_cd,
   COP       => c6_cop,
   COPV      => c6_copv,
   CACK_N    => c6_cack_n,
   CEOT      => c6_ceot,
   CMF       => c6_cmf,
   CMM_N     => c6_cmm_n,
   CMV       => c6_cmv,
   CFF       => c6_cff,
   CPHASE    => c6_cphase,
   CRST_N    => c6_crst_n,
   CMCLK     => c6_cmclk,
   CAD       => c6_cad,
   CCE_N     => c6_cce_n,
   CALE_N    => c6_cale_n,
   COE_N     => c6_coe_n,
   CWE_N     => c6_cwe_n,
   CSCLK     => c6_csclk,
   CSEN_N    => c6_csen_n,
   -- SDRAM:
   DD        => dd,
   DCB       => dcb,
   DBA       => dba,
   DQS       => dqs,
   DA        => da,
   DCS_N     => dcs_n,
   DCLKE     => dclke,
   DCAS_N    => dcas_n,
   DRAS_N    => dras_n,
   DWE_N     => dwe_n,
   DCLK      => dclk,
   DCLK_N    => dclk_n,
   DCLK2     => dclk2,
   RESDDR_N  => resddr_n,
   DSDA      => dsda,
   DSCLK     => dsclk,
   -- LB:
   X       => c6_x,
   -- SSRAM0:
   S0A       => c6_s0a,
   S0ADSP_N  => c6_s0adsp_n,
   S0ADSC_N  => c6_s0adsc_n,
   S0ADV_N   => c6_s0adv_n,
   S0CS1_N   => c6_s0cs1_n,
   S0CS2_N   => c6_s0cs2_n,
   S0GW_N    => c6_s0gw_n,
   S0BW_N    => c6_s0bw_n,
   S0WE_N    => c6_s0we_n,
   S0OE_N    => c6_s0oe_n,
   SCLK0     => c6_sclk0,
   S0D       => c6_s0d,
   -- SSRAM1:
   S1A       => c6_s1a,
   S1ADSP_N  => c6_s1adsp_n,
   S1ADSC_N  => c6_s1adsc_n,
   S1ADV_N   => c6_s1adv_n,
   S1CS1_N   => c6_s1cs1_n,
   S1CS2_N   => c6_s1cs2_n,
   S1GW_N    => c6_s1gw_n,
   S1BW_N    => c6_s1bw_n,
   S1WE_N    => c6_s1we_n,
   S1OE_N    => c6_s1oe_n,
   SCLK1     => c6_sclk1,
   S1D       => c6_s1d,
   -- SSRAM2:
   S2A       => c6_s2a,
   S2ADSP_N  => c6_s2adsp_n,
   S2ADSC_N  => c6_s2adsc_n,
   S2ADV_N   => c6_s2adv_n,
   S2CS1_N   => c6_s2cs1_n,
   S2CS2_N   => c6_s2cs2_n,
   S2GW_N    => c6_s2gw_n,
   S2BW_N    => c6_s2bw_n,
   S2WE_N    => c6_s2we_n,
   S2OE_N    => c6_s2oe_n,
   SCLK2     => c6_sclk2,
   S2D       => c6_s2d,
   -- IO interface
   IOS      => ios,
   -- RIO
   TXN3      => c6_txn3,
   TXP3      => c6_txp3,
   RXP3      => c6_rxp3,
   RXN3      => c6_rxn3,
   TXN2      => c6_txn2,
   TXP2      => c6_txp2,
   RXP2      => c6_rxp2,
   RXN2      => c6_rxn2,
   TXN1      => c6_txn1,
   TXP1      => c6_txp1,
   RXP1      => c6_rxp1,
   RXN1      => c6_rxn1,
   TXN0      => c6_txn0,
   TXP0      => c6_txp0,
   RXP0      => c6_rxp0,
   RXN0      => c6_rxn0
);

-- ----------------------------------------------------
-- SFPRO FPGA
SFPRO_UUT : entity work.sfpro
port map(
   -- CLK:
   LCLKF     => sfpro_lclkf,
   FCLK      => fclk,
   ECLKP     => clkp,
   ECLKN     => clkn,
   ETHCLKP   => ethclkp,
   ETHCLKN   => ethclkn,
   
   -- LED:
   XLED      => sfpro_xled,

   -- SFP A:
   TXDISA    => open,
   TXFAULTA  => gnd,
   RXLOSSA   => gnd,
   MODDEFA   => open,
   RSA       => open,
   -- SFP B:
   TXDISB    => open,
   TXFAULTB  => gnd,
   RXLOSSB   => gnd,
   MODDEFB   => open,
   RSB       => open,
   -- SFP C:
   TXDISC    => open,
   TXFAULTC  => gnd,
   RXLOSSC   => gnd,
   MODDEFC   => open,
   RSC       => open,
   -- SFP D:
   TXDISD    => open,
   TXFAULTD  => gnd,
   RXLOSSD   => gnd,
   MODDEFD   => open,
   RSD       => open, 

   -- Rocket IOs:
   TDN_A     => sfpro_tdn_a,
   TDP_A     => sfpro_tdp_a,
   RDP_A     => sfpro_rdp_a,
   RDN_A     => sfpro_rdn_a,
   TDN_B     => sfpro_tdn_b,
   TDP_B     => sfpro_tdp_b,
   RDP_B     => sfpro_rdp_b,
   RDN_B     => sfpro_rdn_b,
   TDN_C     => sfpro_tdn_c,
   TDP_C     => sfpro_tdp_c,
   RDP_C     => sfpro_rdp_c,
   RDN_C     => sfpro_rdn_c,
   TDN_D     => sfpro_tdn_d,
   TDP_D     => sfpro_tdp_d,
   RDP_D     => sfpro_rdp_d,
   RDN_D     => sfpro_rdn_d,
 
   -- RIO:
   TXN0      => sfpro_txn0,
   TXP0      => sfpro_txp0,
   RXP0      => sfpro_rxp0,
   RXN0      => sfpro_rxn0,
   TXN1      => sfpro_txn1,
   TXP1      => sfpro_txp1,
   RXP1      => sfpro_rxp1,
   RXN1      => sfpro_rxn1,
   -- IO:

   IO       => io,
   IOS      => ios,

    -- SSRAM0:
   S0A       => sfpro_s0a,
   S0ADSP_N  => sfpro_s0adsp_n,
   S0ADSC_N  => sfpro_s0adsc_n,
   S0ADV_N   => sfpro_s0adv_n,
   S0CS1_N   => sfpro_s0cs1_n,
   S0CS2_N   => sfpro_s0cs2_n,
   S0GW_N    => sfpro_s0gw_n,
   S0BW_N    => sfpro_s0bw_n,
   S0WE_N    => sfpro_s0we_n,
   S0OE_N    => sfpro_s0oe_n,
   S0MODE    => sfpro_s0mode,
   SCLK0     => sfpro_sclk0,
   SCLK0F    => sfpro_sclk0f,
   S0D       => sfpro_s0d,
   -- SSRAM1:
   S1A       => sfpro_s1a,
   S1ADSP_N  => sfpro_s1adsp_n,
   S1ADSC_N  => sfpro_s1adsc_n,
   S1ADV_N   => sfpro_s1adv_n,
   S1CS1_N   => sfpro_s1cs1_n,
   S1CS2_N   => sfpro_s1cs2_n,
   S1GW_N    => sfpro_s1gw_n,
   S1BW_N    => sfpro_s1bw_n,
   S1WE_N    => sfpro_s1we_n,
   S1OE_N    => sfpro_s1oe_n,
   S1MODE    => sfpro_s1mode,
   SCLK1     => sfpro_sclk1,
   SCLK1F    => sfpro_sclk1f,
   S1D       => sfpro_s1d,



    -- CAM:
   CD        => cd,
   COP       => cop,
   COPV      => copv,
   CACK_N    => cack_n,
   CEOT      => ceot,
   CMF       => cmf,
   CMM_N     => cmm_n,
   CMV       => cmv,
   CFF       => cff,
   CPHASE    => cphase,
   CRST_N    => crst_n,
   CMCLK     => cmclk,
   CMCLKF    => cmclkf,
   CAD       => cad,
   CCE_N     => cce_n,
   CALE_N    => cale_n,
   COE_N     => coe_n,
   CWE_N     => cwe_n,
   CSCLK     => csclk,
   CSEN      => csen
);


-- ----------------------------------------------------
-- PLX Simulation component
PLX_SIM_U : entity work.plx_sim
generic map(
   PLX_HOLD       => 10 ns,
   DEBUG_REPORT   => false
)
port map(
   -- PLX interface
   LCLKF             => c6_lclkf,
   LAD(31 downto 27) => LAD1,
   LAD(26 downto 0)  => LAD0,
   LBE               => open,
   LHOLDA            => lholda,
   LFRAME            => open,
   ADS               => ADS,
   BLAST             => BLAST,
   LWR               => LWR,
   READY             => READY,
   LHOLD             => LHOLD,
   LINT              => open,
   LRESET            => LRESET,
   USERO             => open,

   -- Simulation interface
   STATUS      => plx_status,
   OPER        => plx_oper,
   PARAMS      => plx_params,
   STROBE      => plx_strobe,
   BUSY        => plx_busy
);

 lholda <= LHOLD after clkper;  -- FIXME

-- ----------------------------------------------------
-- RocketIO/Ethernet simulation models ----------------
PHYSIM_U0 : entity work.phy_sim_rio_eth
generic map (
      MAX_UNTAGGED_FRAME_SIZE => 40000
)
port map (
   RESET  => reset,
   -- RocketIO interface
   RXP    => sfpro_tdp_a,
   RXN    => sfpro_tdn_a,
   TXP    => sfpro_rdp_a,
   TXN    => sfpro_rdn_a,
   -- Simulation interface ---
   OPER   => phy_oper(0),
   PARAMS => phy_params(0),
   STROBE => phy_strobe(0),
   BUSY   => phy_busy(0)   
);

PHYSIM_U1 : entity work.phy_sim_rio_eth
port map (
   RESET  => reset,
   -- RocketIO interface
   RXP    => sfpro_tdp_b,
   RXN    => sfpro_tdn_b,
   TXP    => sfpro_rdp_b,
   TXN    => sfpro_rdn_b,
   -- Simulation interface ---
   OPER   => phy_oper(1),
   PARAMS => phy_params(1),
   STROBE => phy_strobe(1),
   BUSY   => phy_busy(1)   
);
PHYSIM_U2 : entity work.phy_sim_rio_eth
port map (
   RESET  => reset,
   -- RocketIO interface
   RXP    => sfpro_tdp_c,
   RXN    => sfpro_tdn_c,
   TXP    => sfpro_rdp_c,
   TXN    => sfpro_rdn_c,
   -- Simulation interface ---
   OPER   => phy_oper(2),
   PARAMS => phy_params(2),
   STROBE => phy_strobe(2),
   BUSY   => phy_busy(2)   
);
PHYSIM_U3 : entity work.phy_sim_rio_eth
port map (
   RESET  => reset,
   -- RocketIO interface
   RXP    => sfpro_tdp_d,
   RXN    => sfpro_tdn_d,
   TXP    => sfpro_rdp_d,
   TXN    => sfpro_rdn_d,
   -- Simulation interface ---
   OPER   => phy_oper(3),
   PARAMS => phy_params(3),
   STROBE => phy_strobe(3),
   BUSY   => phy_busy(3)   
); 

-- ----------------------------------------------------
-- LCLKF clock generator
clkgen : process
begin
   lclkf <= '1';
   wait for clkper/2;
   lclkf <= '0';
   wait for clkper/2;
end process;

c6_lclkf    <= lclkf;
--sfpro_lclkf <= lclkf;

-- FCLK clock generator
fclkgen : process
begin
   fclk <= '1';
   wait for fclkper/2;
   fclk <= '0';
   wait for fclkper/2;
end process;

clkn     <= not fclk after 1 ns;
clkp     <= fclk after 1 ns;
ethclkn  <= not fclk after 2 ns;
ethclkp  <= fclk after 2 ns;


--c6_lholda <= 'Z';
READY  <= 'Z';
--c6_usero  <= '0';

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------

tb : process
-- ----------------------------------------------------------------
--                    Procedures declaration
-- ----------------------------------------------------------------

-- ----------------------------------------------------------------
-- Procedure plx_op performs plx operation specified
-- in data structure t_plx_ctrl
--
-- Parameters:
--       ctrl        - structure for plx controling
--       block_wait  - block waiting
--
procedure plx_op(ctrl : in t_plx_ctrl; block_wait : in boolean := false) is
begin
   wait until (LCLKF'event and LCLKF='1' and plx_busy = '0');
   wait for 0.1*clkper;
   plx_oper    <= ctrl.oper;
   plx_params  <= ctrl.params;
   plx_strobe  <= '1';

   wait for clkper;
   plx_strobe  <= '0';

   -- block waiting, if reguired
   if (block_wait) then
      wait until (LCLKF'event and LCLKF='1' and plx_busy = '0');
   end if;
end plx_op;

-- ----------------------------------------------------------------
-- Procedure phy_op performs phy operation specified
-- in data structure t_phy_ctrl
--
-- Parameters:
--       ctrl        - structure for phy controling
--       id          - interface id
--       block_wait  - blocking waiting for completion of operation
--
procedure phy_op(ctrl : in t_phy_ctrl; id : in integer;
                 block_wait : in boolean := false) is
begin
   --wait until (phy_busy(id) = '0');
   while (phy_busy(id) /= '0') loop
      wait for 0.1 ns;
   end loop;
   phy_oper(id)   <= ctrl.oper;
   phy_params(id) <= ctrl.params;
   phy_strobe(id) <= '1';

   wait until (phy_busy(id) = '1');
   phy_strobe(id)  <= '0';

   -- block waiting, if required
   if (block_wait = true) then
      while (phy_busy(id) /= '0') loop
         wait for 0.1 ns;
      end loop;
   end if;
end phy_op;


-- ----------------------------------------------------------------
--                        Testbench Body
-- ----------------------------------------------------------------
begin
   -- local bus inicialization
   plx_op(plx_init, false);

   plx_op(plx_write(IBUF0_BASE_ADDR+16#24#,X"00000003")); -- Set error mask
   plx_op(plx_read(IBUF0_BASE_ADDR+16#24#));
   plx_op(plx_write(IBUF0_BASE_ADDR+16#38#,X"00000001")); -- Set mac check register
   plx_op(plx_read(IBUF0_BASE_ADDR+16#38#));
   plx_op(plx_write(IBUF0_BASE_ADDR+16#80#,X"00000002")); -- Set MAC Address part 1
   plx_op(plx_write(IBUF0_BASE_ADDR+16#84#,X"00010000")); -- Set MAC Address part 2
   plx_op(plx_read(IBUF0_BASE_ADDR+16#80#));
   plx_op(plx_read(IBUF0_BASE_ADDR+16#84#));
   plx_op(plx_write(IBUF0_BASE_ADDR+16#30#,X"00000015")); -- Set min len
   plx_op(plx_read(IBUF0_BASE_ADDR+16#30#));
   plx_op(plx_write(IBUF0_BASE_ADDR+16#34#,X"000005dc")); -- Set MTU 
   plx_op(plx_read(IBUF0_BASE_ADDR+16#34#));
   plx_op(plx_write(IBUF0_BASE_ADDR+16#2c#,X"000000" & IBUFCMD_SET_SPEED1000)); -- Perform SET_SPEED100 command
   plx_op(plx_read(IBUF0_BASE_ADDR+16#28#)); -- Read IBUF status     
   plx_op(plx_write(IBUF0_BASE_ADDR+16#20#,X"00000001")); -- Enable IBUF

--   plx_op(plx_write(IBUF1_BASE_ADDR+16#24#,X"00000003")); -- Set error mask
--   plx_op(plx_read(IBUF1_BASE_ADDR+16#24#));
--   plx_op(plx_write(IBUF1_BASE_ADDR+16#38#,X"00000001")); -- Set mac check register
--   plx_op(plx_read(IBUF1_BASE_ADDR+16#38#));
--   plx_op(plx_write(IBUF1_BASE_ADDR+16#80#,X"00000102")); -- Set MAC Address part 1
--   plx_op(plx_write(IBUF1_BASE_ADDR+16#84#,X"00010000")); -- Set MAC Address part 2
--   plx_op(plx_read(IBUF1_BASE_ADDR+16#84#));              -- Read MAC Address
--   plx_op(plx_read(IBUF1_BASE_ADDR+16#80#));
--   plx_op(plx_write(IBUF1_BASE_ADDR+16#30#,X"00000015")); -- Set min len
--   plx_op(plx_read(IBUF1_BASE_ADDR+16#30#));
--   plx_op(plx_write(IBUF1_BASE_ADDR+16#34#,X"000005dc")); -- Set MTU 
--   plx_op(plx_read(IBUF1_BASE_ADDR+16#34#));
--   plx_op(plx_write(IBUF1_BASE_ADDR+16#2c#,X"000000" & IBUFCMD_SET_SPEED1000)); -- Perform SET_SPEED100 command
--   plx_op(plx_read(IBUF1_BASE_ADDR+16#28#)); -- Read IBUF status     
--   plx_op(plx_write(IBUF1_BASE_ADDR+16#20#,X"00000001")); -- Enable IBUF
--
--   plx_op(plx_write(IBUF2_BASE_ADDR+16#24#,X"00000003")); -- Set error mask
--   plx_op(plx_read(IBUF2_BASE_ADDR+16#24#));
--   plx_op(plx_write(IBUF2_BASE_ADDR+16#38#,X"00000001")); -- Set mac check register
--   plx_op(plx_read(IBUF2_BASE_ADDR+16#38#));
--   plx_op(plx_write(IBUF2_BASE_ADDR+16#80#,X"00000102")); -- Set MAC Address part 1
--   plx_op(plx_write(IBUF2_BASE_ADDR+16#84#,X"00010000")); -- Set MAC Address part 2
--   plx_op(plx_read(IBUF2_BASE_ADDR+16#84#));              -- Read MAC Address
--   plx_op(plx_read(IBUF2_BASE_ADDR+16#80#));
--   plx_op(plx_write(IBUF2_BASE_ADDR+16#30#,X"00000015")); -- Set min len
--   plx_op(plx_read(IBUF2_BASE_ADDR+16#30#));
--   plx_op(plx_write(IBUF2_BASE_ADDR+16#34#,X"000005dc")); -- Set MTU 
--   plx_op(plx_read(IBUF2_BASE_ADDR+16#34#));
--   plx_op(plx_write(IBUF2_BASE_ADDR+16#2c#,X"000000" & IBUFCMD_SET_SPEED1000)); -- Perform SET_SPEED100 command
--   plx_op(plx_read(IBUF2_BASE_ADDR+16#28#)); -- Read IBUF status     
--   plx_op(plx_write(IBUF2_BASE_ADDR+16#20#,X"00000001")); -- Enable IBUF
--
--   plx_op(plx_write(IBUF3_BASE_ADDR+16#24#,X"00000003")); -- Set error mask
--   plx_op(plx_read(IBUF3_BASE_ADDR+16#24#));
--   plx_op(plx_write(IBUF3_BASE_ADDR+16#38#,X"00000001")); -- Set mac check register
--   plx_op(plx_read(IBUF3_BASE_ADDR+16#38#));
--   plx_op(plx_write(IBUF3_BASE_ADDR+16#80#,X"00000102")); -- Set MAC Address part 1
--   plx_op(plx_write(IBUF3_BASE_ADDR+16#84#,X"00010000")); -- Set MAC Address part 2
--   plx_op(plx_read(IBUF3_BASE_ADDR+16#84#));              -- Read MAC Address
--   plx_op(plx_read(IBUF3_BASE_ADDR+16#80#));
--   plx_op(plx_write(IBUF3_BASE_ADDR+16#30#,X"00000015")); -- Set min len
--   plx_op(plx_read(IBUF3_BASE_ADDR+16#30#));
--   plx_op(plx_write(IBUF3_BASE_ADDR+16#34#,X"000005dc")); -- Set MTU 
--   plx_op(plx_read(IBUF3_BASE_ADDR+16#34#));
--   plx_op(plx_write(IBUF3_BASE_ADDR+16#2c#,X"000000" & IBUFCMD_SET_SPEED1000)); -- Perform SET_SPEED100 command
--   plx_op(plx_read(IBUF3_BASE_ADDR+16#28#)); -- Read IBUF status     
--   plx_op(plx_write(IBUF3_BASE_ADDR+16#20#,X"00000001")); -- Enable IBUF

   plx_op(plx_write(OBUF0_BASE_ADDR+16#20#,X"00000000")); -- Disable OBUF
   plx_op(plx_write(OBUF0_BASE_ADDR+16#24#,x"3f123456")); -- Set low part of MAC address
   plx_op(plx_write(OBUF0_BASE_ADDR+16#28#,x"00000002")); -- Set high part of MAC address
   plx_op(plx_write(OBUF0_BASE_ADDR+16#2C#,X"000000" & OBUFCMD_SET_SPEED1000)); -- Perform SET_SPEED100 command
   plx_op(plx_read(OBUF0_BASE_ADDR+16#30#)); -- Read OBUF status     
   plx_op(plx_write(OBUF0_BASE_ADDR+16#20#,X"00000001")); -- Enable OBUF

--   plx_op(plx_write(OBUF1_BASE_ADDR+16#20#,X"00000000")); -- Disable OBUF
--   plx_op(plx_write(OBUF1_BASE_ADDR+16#24#,x"3f123456")); -- Set low part of MAC address
--   plx_op(plx_write(OBUF1_BASE_ADDR+16#28#,x"00000002")); -- Set high part of MAC address
--   plx_op(plx_write(OBUF1_BASE_ADDR+16#2C#,X"000000" & OBUFCMD_SET_SPEED1000)); -- Perform SET_SPEED100 command
--   plx_op(plx_read(OBUF1_BASE_ADDR+16#30#)); -- Read OBUF status     
--   plx_op(plx_write(OBUF1_BASE_ADDR+16#20#,X"00000001")); -- Enable OBUF
--
--   plx_op(plx_write(OBUF2_BASE_ADDR+16#20#,X"00000000")); -- Disable OBUF
--   plx_op(plx_write(OBUF2_BASE_ADDR+16#24#,x"3f123456")); -- Set low part of MAC address
--   plx_op(plx_write(OBUF2_BASE_ADDR+16#28#,x"00000002")); -- Set high part of MAC address
--   plx_op(plx_write(OBUF2_BASE_ADDR+16#2C#,X"000000" & OBUFCMD_SET_SPEED1000)); -- Perform SET_SPEED100 command
--   plx_op(plx_read(OBUF2_BASE_ADDR+16#30#)); -- Read OBUF status     
--   plx_op(plx_write(OBUF2_BASE_ADDR+16#20#,X"00000001")); -- Enable OBUF
--
--   plx_op(plx_write(OBUF3_BASE_ADDR+16#20#,X"00000000")); -- Disable OBUF
--   plx_op(plx_write(OBUF3_BASE_ADDR+16#24#,x"3f123456")); -- Set low part of MAC address
--   plx_op(plx_write(OBUF3_BASE_ADDR+16#28#,x"00000002")); -- Set high part of MAC address
--   plx_op(plx_write(OBUF3_BASE_ADDR+16#2C#,X"000000" & OBUFCMD_SET_SPEED1000)); -- Perform SET_SPEED100 command
--   plx_op(plx_read(OBUF3_BASE_ADDR+16#30#)); -- Read OBUF status     
--   plx_op(plx_write(OBUF3_BASE_ADDR+16#20#,X"00000001")); -- Enable OBUF

   plx_op(plx_read(IBUF0_BASE_ADDR+16#20#));
   plx_op(plx_read(IBUF1_BASE_ADDR+16#20#));
   plx_op(plx_read(IBUF2_BASE_ADDR+16#20#));
   plx_op(plx_read(IBUF3_BASE_ADDR+16#20#));

   -- enable bus probe
   plx_op(plx_write(BP_CONTROL,X"00000001"));
 
--   phy_op(send_packet(PACKET_DIR & "icmp_10_0_0_1.txt", 100, true), 0);
   phy_op(send_packet(PACKET_DIR & "icmp_10_0_0_1.txt", 100, true, 1000), 0);
   phy_op(send_packet(PACKET_DIR & "icmp_10_0_0_1.txt", 4, true, 1000), 1);
   phy_op(send_packet(PACKET_DIR & "icmp_10_0_0_1.txt", 4, true, 1000), 2);
   phy_op(send_packet(PACKET_DIR & "icmp_10_0_0_1.txt", 4, true, 1000), 3);
--   phy_op(send_tcpdump_nowait(PACKET_DIR & "flood64.dump"), 0);

   wait for 5 us;
--   plx_op(plx_write(IBUF0_BASE_ADDR+16#30#,X"00000040")); -- Set min len
--   plx_op(plx_write(IBUF0_BASE_ADDR+16#34#,X"000005f6")); -- Set MTU 
   wait for 10 us;
   
   plx_op(plx_read(BP_BASE_ADDR));            -- read BP counter 
   plx_op(plx_read(BP_MEM, 128));             -- read from RIO_DEBUG_BP 
   plx_op(plx_write(IBUF0_BASE_ADDR+16#2c#,X"000000" & IBUFCMD_STROBE_COUNTERS));   -- Perform STROBE_COUNTERS command
   plx_op(plx_write(OBUF0_BASE_ADDR+16#2c#,X"000000" & OBUFCMD_STROBE_COUNTERS));   -- Perform STROBE_COUNTERS command
--   plx_op(plx_write(IBUF1_BASE_ADDR+16#2c#,X"000000" & IBUFCMD_STROBE_COUNTERS));   -- Perform STROBE_COUNTERS command
--   plx_op(plx_write(OBUF1_BASE_ADDR+16#2c#,X"000000" & OBUFCMD_STROBE_COUNTERS));   -- Perform STROBE_COUNTERS command
--   plx_op(plx_write(IBUF2_BASE_ADDR+16#2c#,X"000000" & IBUFCMD_STROBE_COUNTERS));   -- Perform STROBE_COUNTERS command
--   plx_op(plx_write(OBUF2_BASE_ADDR+16#2c#,X"000000" & OBUFCMD_STROBE_COUNTERS));   -- Perform STROBE_COUNTERS command
--   plx_op(plx_write(IBUF3_BASE_ADDR+16#2c#,X"000000" & IBUFCMD_STROBE_COUNTERS));   -- Perform STROBE_COUNTERS command
--   plx_op(plx_write(OBUF3_BASE_ADDR+16#2c#,X"000000" & OBUFCMD_STROBE_COUNTERS));   -- Perform STROBE_COUNTERS command
   -- Read counters
   plx_op(plx_read(OBUF0_BASE_ADDR+16#0#));      
   plx_op(plx_read(OBUF0_BASE_ADDR+16#4#));

--   plx_op(plx_read(OBUF1_BASE_ADDR+16#0#));      
--   plx_op(plx_read(OBUF1_BASE_ADDR+16#4#));

--   plx_op(plx_read(OBUF2_BASE_ADDR+16#0#));      
--   plx_op(plx_read(OBUF2_BASE_ADDR+16#4#));

--   plx_op(plx_read(OBUF3_BASE_ADDR+16#0#));      
--   plx_op(plx_read(OBUF3_BASE_ADDR+16#4#));

   plx_op(plx_read(IBUF0_BASE_ADDR+16#0#));      
   plx_op(plx_read(IBUF0_BASE_ADDR+16#4#));
   plx_op(plx_read(IBUF0_BASE_ADDR+16#8#));
   plx_op(plx_read(IBUF0_BASE_ADDR+16#C#));

--   plx_op(plx_read(IBUF1_BASE_ADDR+16#0#));      
--   plx_op(plx_read(IBUF1_BASE_ADDR+16#4#));
--   plx_op(plx_read(IBUF1_BASE_ADDR+16#8#));
--   plx_op(plx_read(IBUF1_BASE_ADDR+16#C#));

--   plx_op(plx_read(IBUF2_BASE_ADDR+16#0#));      
--   plx_op(plx_read(IBUF2_BASE_ADDR+16#4#));
--   plx_op(plx_read(IBUF2_BASE_ADDR+16#8#));
--   plx_op(plx_read(IBUF2_BASE_ADDR+16#C#));

--   plx_op(plx_read(IBUF3_BASE_ADDR+16#0#));      
--   plx_op(plx_read(IBUF3_BASE_ADDR+16#4#));
--   plx_op(plx_read(IBUF3_BASE_ADDR+16#8#));
--   plx_op(plx_read(IBUF3_BASE_ADDR+16#C#));

   while (true) loop
      plx_op(plx_read(IBUF0_TEST_BASE_ADDR));               -- read from FIFO
--      plx_op(plx_read(IBUF1_TEST_BASE_ADDR));               -- read from FIFO
--      plx_op(plx_read(IBUF2_TEST_BASE_ADDR));               -- read from FIFO
--      plx_op(plx_read(IBUF3_TEST_BASE_ADDR));               -- read from FIFO
   end loop;
   wait;
end process;

-- --------------------------------------------------------------------
end architecture behavioral;

