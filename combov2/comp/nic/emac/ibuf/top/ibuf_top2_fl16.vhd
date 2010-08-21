-- ibuf_top2_fl16.vhd: 2 IBUFs top level with records
-- Copyright (C) 2007 CESNET, Liberouter project
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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


library IEEE;
use IEEE.std_logic_1164.all;
use work.ibuf_general_pkg.all;
use work.lb_pkg.all;
use work.emac_pkg.all;
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity ibuf_emac_top2_fl16 is

   generic(
      DFIFO_SIZE  : integer := 8192;   -- Packet data fifo size
      HFIFO_SIZE  : integer := 511;		-- Control fifo size
      CTRL_HDR_EN : boolean := true;   -- Header enable
      CTRL_FTR_EN : boolean := false;  -- Footer enable
      MACS        : integer := 16;  		-- Number of MAC addresses (up to 16)
      INBANDFCS   : boolean := true    -- frame contains FCS (true) or not (false)
   );

   port(

      -- ---------------- Common signal -----------------
      RESET         		: in  std_logic;
      IBUF_CLK      		: in  std_logic;

      -- ------------------------------------------------
      -- -------------- IBUF interfaces -----------------
      
      -- -----------
      -- INTERFACE 0
      -- EMAC RX interface
      IBUF0_RXCLK       : in std_logic;
      IBUF0_RXCE        : in std_logic;
      IBUF0_RX          : in t_emac_rx;

      -- PACODAG interface
      IBUF0_PCD         : inout t_pacodag16;

      -- Sampling unit interface
      IBUF0_SAU_ACCEPT  : in std_logic;
      IBUF0_SAU_DV      : in std_logic;

      -- FrameLink interface
      IBUF0_TX          : inout t_fl16;

      
      -- -----------
      -- INTERFACE 1
      -- EMAC RX interface
      IBUF1_RXCLK       : in std_logic;
      IBUF1_RXCE        : in std_logic;
      IBUF1_RX          : in t_emac_rx;

      -- PACODAG interface
      IBUF1_PCD         : inout t_pacodag16;

      -- Sampling unit interface
      IBUF1_SAU_ACCEPT	: in std_logic;
      IBUF1_SAU_DV      : in std_logic;

      -- FrameLink interface
      IBUF1_TX          : inout t_fl16;


      -- ------------------------------------------------
      -- ------------ MI_32 bus signals -----------------
      MI               : inout t_mi32
   );

end entity ibuf_emac_top2_fl16;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ibuf_emac_top2_fl16 is

begin

   ibuf_emac_top2_mi32i: entity work.ibuf_emac_top2_mi32
      generic map(
         DATA_PATHS  => 2,
         DFIFO_SIZE  => DFIFO_SIZE,
         HFIFO_SIZE  => HFIFO_SIZE,
         CTRL_HDR_EN => CTRL_HDR_EN,
         CTRL_FTR_EN => CTRL_FTR_EN,
         MACS        => MACS,
         INBANDFCS   => INBANDFCS
      )
      port map(
         RESET         			=> RESET,
         IBUF_CLK      			=> IBUF_CLK,
   
         IBUF0_RXCLK          => IBUF0_RXCLK,
         IBUF0_RXCE           => IBUF0_RXCE,
         IBUF0_RX             => IBUF0_RX,
   
         IBUF0_CTRL_CLK       => IBUF0_PCD.CLK,
         IBUF0_CTRL_DI        => IBUF0_PCD.DATA,
         IBUF0_CTRL_REM       => IBUF0_PCD.DREM,
         IBUF0_CTRL_SRC_RDY_N => IBUF0_PCD.SRC_RDY_N,
         IBUF0_CTRL_SOP_N     => IBUF0_PCD.SOP_N,
         IBUF0_CTRL_EOP_N     => IBUF0_PCD.EOP_N,
         IBUF0_CTRL_DST_RDY_N => IBUF0_PCD.DST_RDY_N,
         IBUF0_CTRL_RDY       => IBUF0_PCD.PACODAG_RDY,
   
         IBUF0_SOP            => IBUF0_PCD.SOP,
         IBUF0_STAT           => IBUF0_PCD.STAT,
         IBUF0_STAT_DV        => IBUF0_PCD.STAT_DV,
   
         IBUF0_SAU_ACCEPT     => IBUF0_SAU_ACCEPT,
         IBUF0_SAU_DV         => IBUF0_SAU_DV,
   
         IBUF0_DATA           => IBUF0_TX.DATA,
         IBUF0_DREM           => IBUF0_TX.DREM,
         IBUF0_SRC_RDY_N      => IBUF0_TX.SRC_RDY_N,
         IBUF0_SOF_N          => IBUF0_TX.SOF_N,
         IBUF0_SOP_N          => IBUF0_TX.SOP_N,
         IBUF0_EOF_N          => IBUF0_TX.EOF_N,
         IBUF0_EOP_N          => IBUF0_TX.EOP_N,
         IBUF0_DST_RDY_N      => IBUF0_TX.DST_RDY_N,
         

         IBUF1_RXCLK          => IBUF1_RXCLK,
         IBUF1_RXCE           => IBUF1_RXCE,
         IBUF1_RX             => IBUF1_RX,
   
         IBUF1_CTRL_CLK       => IBUF1_PCD.CLK,
         IBUF1_CTRL_DI        => IBUF1_PCD.DATA,
         IBUF1_CTRL_REM       => IBUF1_PCD.DREM,
         IBUF1_CTRL_SRC_RDY_N => IBUF1_PCD.SRC_RDY_N,
         IBUF1_CTRL_SOP_N     => IBUF1_PCD.SOP_N,
         IBUF1_CTRL_EOP_N     => IBUF1_PCD.EOP_N,
         IBUF1_CTRL_DST_RDY_N => IBUF1_PCD.DST_RDY_N,
         IBUF1_CTRL_RDY       => IBUF1_PCD.PACODAG_RDY,
   
         IBUF1_SOP            => IBUF1_PCD.SOP,
         IBUF1_STAT           => IBUF1_PCD.STAT,
         IBUF1_STAT_DV        => IBUF1_PCD.STAT_DV,
   
         IBUF1_SAU_ACCEPT     => IBUF1_SAU_ACCEPT,
         IBUF1_SAU_DV         => IBUF1_SAU_DV,
   
         IBUF1_DATA           => IBUF1_TX.DATA,
         IBUF1_DREM           => IBUF1_TX.DREM,
         IBUF1_SRC_RDY_N      => IBUF1_TX.SRC_RDY_N,
         IBUF1_SOF_N          => IBUF1_TX.SOF_N,
         IBUF1_SOP_N          => IBUF1_TX.SOP_N,
         IBUF1_EOF_N          => IBUF1_TX.EOF_N,
         IBUF1_EOP_N          => IBUF1_TX.EOP_N,
         IBUF1_DST_RDY_N      => IBUF1_TX.DST_RDY_N,
   
         -- ------------------------------------------------
         -- ------------ MI_32 bus signals -----------------
         MI                   => MI
      );

end architecture full;
