-- ibuf_top4_fl16.vhd: 4 IBUFs, top level with records
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jiri Tobola <tobola@liberouter.org>
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
-- TODO: - 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

use work.math_pack.ALL;
use work.ibuf_general_pkg.ALL;
use work.fl_pkg.ALL;
use work.lb_pkg.all; 

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity ibuf_top4_fl16 is
   generic(
      DFIFO_SIZE  : integer;     -- Packet data fifo size
      HFIFO_SIZE  : integer;     -- Control fifo size
      MACS        : integer := 16;  -- Number of MAC addresses (up to 16)
      CTRL_HDR_EN : boolean := true; -- Enable FL headers
      CTRL_FTR_EN : boolean := false;-- Enable FL footers
      -- true: FCS is kept in the frame
      -- false: FCS is cut out during processing
      INBANDFCS   : boolean := false
   );
   port(

      -- Common signal
      RESET           : in  std_logic;
      IBUF_CLK        : in std_logic;

      -- GMII RX interfaces
      IBUF0_RXCLK     : in  std_logic;
      IBUF0_RXD       : in  std_logic_vector(7 downto 0);
      IBUF0_RXDV      : in  std_logic;
      IBUF0_RXER      : in  std_logic;

      IBUF1_RXCLK     : in  std_logic;
      IBUF1_RXD       : in  std_logic_vector(7 downto 0);
      IBUF1_RXDV      : in  std_logic;
      IBUF1_RXER      : in  std_logic;

      IBUF2_RXCLK     : in  std_logic;
      IBUF2_RXD       : in  std_logic_vector(7 downto 0);
      IBUF2_RXDV      : in  std_logic;
      IBUF2_RXER      : in  std_logic;

      IBUF3_RXCLK     : in  std_logic;
      IBUF3_RXD       : in  std_logic_vector(7 downto 0);
      IBUF3_RXDV      : in  std_logic;
      IBUF3_RXER      : in  std_logic;

      -- PACODAG
      IBUF0_PCD       : inout t_pacodag16;
      IBUF1_PCD       : inout t_pacodag16;
      IBUF2_PCD       : inout t_pacodag16;
      IBUF3_PCD       : inout t_pacodag16;

      -- Sampling unit interface
      IBUF0_SAU_ACCEPT : in std_logic;
      IBUF0_SAU_DV     : in std_logic;
      IBUF1_SAU_ACCEPT : in std_logic;
      IBUF1_SAU_DV     : in std_logic;
      IBUF2_SAU_ACCEPT : in std_logic;
      IBUF2_SAU_DV     : in std_logic;
      IBUF3_SAU_ACCEPT : in std_logic;
      IBUF3_SAU_DV     : in std_logic;

      -- FrameLink interface
      IBUF0_TX         : inout t_fl16;
      IBUF1_TX         : inout t_fl16;
      IBUF2_TX         : inout t_fl16;
      IBUF3_TX         : inout t_fl16;

      -- Internal bus signals ----------------
      MI               : inout t_mi32
   );
end ibuf_top4_fl16;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of ibuf_top4_fl16 is
begin

   IBUF_GMII_TOP4_MI32_I: entity work.ibuf_gmii_top4_mi32
   generic map(
      DATA_PATHS  => 2,
      DFIFO_SIZE  => DFIFO_SIZE,
      HFIFO_SIZE  => HFIFO_SIZE,
      MACS        => MACS,
      CTRL_HDR_EN => CTRL_HDR_EN,
      CTRL_FTR_EN => CTRL_FTR_EN,
      INBANDFCS   => INBANDFCS
   )
   port map(
      -- ---------------- Common signal -----------------
      RESET         => RESET,
      IBUF_CLK      => IBUF_CLK,

      -- GMII RX interfaces
      IBUF0_RXCLK     => IBUF0_RXCLK,
      IBUF0_RXD       => IBUF0_RXD,
      IBUF0_RXDV      => IBUF0_RXDV,
      IBUF0_RXER      => IBUF0_RXER,

      IBUF1_RXCLK     => IBUF1_RXCLK,
      IBUF1_RXD       => IBUF1_RXD,
      IBUF1_RXDV      => IBUF1_RXDV,
      IBUF1_RXER      => IBUF1_RXER,

      IBUF2_RXCLK     => IBUF2_RXCLK,
      IBUF2_RXD       => IBUF2_RXD,
      IBUF2_RXDV      => IBUF2_RXDV,
      IBUF2_RXER      => IBUF2_RXER,

      IBUF3_RXCLK     => IBUF3_RXCLK,
      IBUF3_RXD       => IBUF3_RXD,
      IBUF3_RXDV      => IBUF3_RXDV,
      IBUF3_RXER      => IBUF3_RXER,

      -- PHY status interface
      PHY0_LINK_STATUS       => '0',
      PHY0_DUPLEX_MODE       => '0',
      PHY0_SPEED             => "00",
      PHY0_SGMII             => '0',

      PHY1_LINK_STATUS       => '0',
      PHY1_DUPLEX_MODE       => '0',
      PHY1_SPEED             => "00",
      PHY1_SGMII             => '0',
                                             
      PHY2_LINK_STATUS       => '0',
      PHY2_DUPLEX_MODE       => '0',
      PHY2_SPEED             => "00",
      PHY2_SGMII             => '0',
                                             
      PHY3_LINK_STATUS       => '0',
      PHY3_DUPLEX_MODE       => '0',
      PHY3_SPEED             => "00",
      PHY3_SGMII             => '0',
                                             
      -- PACODAG interface
      IBUF0_CTRL_CLK       => IBUF0_PCD.CLK,
      IBUF0_CTRL_DATA      => IBUF0_PCD.DATA,
      IBUF0_CTRL_REM       => IBUF0_PCD.DREM,
      IBUF0_CTRL_SRC_RDY_N => IBUF0_PCD.SRC_RDY_N,
      IBUF0_CTRL_SOP_N     => IBUF0_PCD.SOP_N,
      IBUF0_CTRL_EOP_N     => IBUF0_PCD.EOP_N,
      IBUF0_CTRL_DST_RDY_N => IBUF0_PCD.DST_RDY_N,
      IBUF0_CTRL_RDY       => IBUF0_PCD.PACODAG_RDY,
      IBUF0_SOP            => IBUF0_PCD.SOP,
      IBUF0_STAT           => IBUF0_PCD.STAT,
      IBUF0_STAT_DV        => IBUF0_PCD.STAT_DV,

      IBUF1_CTRL_CLK       => IBUF1_PCD.CLK,
      IBUF1_CTRL_DATA      => IBUF1_PCD.DATA,
      IBUF1_CTRL_REM       => IBUF1_PCD.DREM,
      IBUF1_CTRL_SRC_RDY_N => IBUF1_PCD.SRC_RDY_N,
      IBUF1_CTRL_SOP_N     => IBUF1_PCD.SOP_N,
      IBUF1_CTRL_EOP_N     => IBUF1_PCD.EOP_N,
      IBUF1_CTRL_DST_RDY_N => IBUF1_PCD.DST_RDY_N,
      IBUF1_CTRL_RDY       => IBUF1_PCD.PACODAG_RDY,
      IBUF1_SOP            => IBUF1_PCD.SOP,
      IBUF1_STAT           => IBUF1_PCD.STAT,
      IBUF1_STAT_DV        => IBUF1_PCD.STAT_DV,

      IBUF2_CTRL_CLK       => IBUF2_PCD.CLK,
      IBUF2_CTRL_DATA      => IBUF2_PCD.DATA,
      IBUF2_CTRL_REM       => IBUF2_PCD.DREM,
      IBUF2_CTRL_SRC_RDY_N => IBUF2_PCD.SRC_RDY_N,
      IBUF2_CTRL_SOP_N     => IBUF2_PCD.SOP_N,
      IBUF2_CTRL_EOP_N     => IBUF2_PCD.EOP_N,
      IBUF2_CTRL_DST_RDY_N => IBUF2_PCD.DST_RDY_N,
      IBUF2_CTRL_RDY       => IBUF2_PCD.PACODAG_RDY,
      IBUF2_SOP            => IBUF2_PCD.SOP,
      IBUF2_STAT           => IBUF2_PCD.STAT,
      IBUF2_STAT_DV        => IBUF2_PCD.STAT_DV,

      IBUF3_CTRL_CLK       => IBUF3_PCD.CLK,
      IBUF3_CTRL_DATA      => IBUF3_PCD.DATA,
      IBUF3_CTRL_REM       => IBUF3_PCD.DREM,
      IBUF3_CTRL_SRC_RDY_N => IBUF3_PCD.SRC_RDY_N,
      IBUF3_CTRL_SOP_N     => IBUF3_PCD.SOP_N,
      IBUF3_CTRL_EOP_N     => IBUF3_PCD.EOP_N,
      IBUF3_CTRL_DST_RDY_N => IBUF3_PCD.DST_RDY_N,
      IBUF3_CTRL_RDY       => IBUF3_PCD.PACODAG_RDY,
      IBUF3_SOP            => IBUF3_PCD.SOP,
      IBUF3_STAT           => IBUF3_PCD.STAT,
      IBUF3_STAT_DV        => IBUF3_PCD.STAT_DV,

      -- Sampling unit interface
      IBUF0_SAU_ACCEPT => IBUF0_SAU_ACCEPT,
      IBUF0_SAU_DV     => IBUF0_SAU_DV,
      IBUF1_SAU_ACCEPT => IBUF1_SAU_ACCEPT,
      IBUF1_SAU_DV     => IBUF1_SAU_DV,
      IBUF2_SAU_ACCEPT => IBUF2_SAU_ACCEPT,
      IBUF2_SAU_DV     => IBUF2_SAU_DV,
      IBUF3_SAU_ACCEPT => IBUF3_SAU_ACCEPT,
      IBUF3_SAU_DV     => IBUF3_SAU_DV,

      -- FrameLink interface
      IBUF0_DATA       => IBUF0_TX.DATA,
      IBUF0_DREM       => IBUF0_TX.DREM,
      IBUF0_SRC_RDY_N  => IBUF0_TX.SRC_RDY_N,
      IBUF0_SOF_N      => IBUF0_TX.SOF_N,
      IBUF0_SOP_N      => IBUF0_TX.SOP_N,
      IBUF0_EOF_N      => IBUF0_TX.EOF_N,
      IBUF0_EOP_N      => IBUF0_TX.EOP_N,
      IBUF0_DST_RDY_N  => IBUF0_TX.DST_RDY_N,

      IBUF1_DATA       => IBUF1_TX.DATA,
      IBUF1_DREM       => IBUF1_TX.DREM,
      IBUF1_SRC_RDY_N  => IBUF1_TX.SRC_RDY_N,
      IBUF1_SOF_N      => IBUF1_TX.SOF_N,
      IBUF1_SOP_N      => IBUF1_TX.SOP_N,
      IBUF1_EOF_N      => IBUF1_TX.EOF_N,
      IBUF1_EOP_N      => IBUF1_TX.EOP_N,
      IBUF1_DST_RDY_N  => IBUF1_TX.DST_RDY_N,

      IBUF2_DATA       => IBUF2_TX.DATA,
      IBUF2_DREM       => IBUF2_TX.DREM,
      IBUF2_SRC_RDY_N  => IBUF2_TX.SRC_RDY_N,
      IBUF2_SOF_N      => IBUF2_TX.SOF_N,
      IBUF2_SOP_N      => IBUF2_TX.SOP_N,
      IBUF2_EOF_N      => IBUF2_TX.EOF_N,
      IBUF2_EOP_N      => IBUF2_TX.EOP_N,
      IBUF2_DST_RDY_N  => IBUF2_TX.DST_RDY_N,

      IBUF3_DATA       => IBUF3_TX.DATA,
      IBUF3_DREM       => IBUF3_TX.DREM,
      IBUF3_SRC_RDY_N  => IBUF3_TX.SRC_RDY_N,
      IBUF3_SOF_N      => IBUF3_TX.SOF_N,
      IBUF3_SOP_N      => IBUF3_TX.SOP_N,
      IBUF3_EOF_N      => IBUF3_TX.EOF_N,
      IBUF3_EOP_N      => IBUF3_TX.EOP_N,
      IBUF3_DST_RDY_N  => IBUF3_TX.DST_RDY_N,

      -- ---------- Internal bus signals ----------------
      MI	              => MI
   ); 

end behavioral;

