--
-- bm_unit_arch.vhd : IB Endpoint Bus Master Unit architecture
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
--            Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--         ARCHITECTURE DECLARATION  --  IB Endpoint Bus Master Unit         --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_bm_unit_arch of IB_ENDPOINT_BM_UNIT is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
   
   constant BIT128          : boolean := (DATA_WIDTH >= 128);
   
   signal bm_sel            : std_logic;
   signal bm_sel_aux        : std_logic;
   signal g2lr_dst_rdy_n    : std_logic;
   signal l2gw_dst_rdy_n    : std_logic;
   signal down_bm_sof_n     : std_logic;
   signal down_bm_eof_n     : std_logic;
   signal down_bm_src_rdy_n : std_logic;
   signal up_bm_sof_n       : std_logic;
   signal up_bm_eof_n       : std_logic;
   signal up_bm_src_rdy_n   : std_logic;
   
   -- DOWN multiplexing logic -------------------------------------------------
   signal down_mx    : std_logic;

   -- UP multiplexing logic ---------------------------------------------------
   signal ib_mx      : std_logic;

begin

   -- -------------------------------------------------------------------------
   --                         DOWN multiplexing logic                        --
   -- -------------------------------------------------------------------------
   
   down_bm_sof_n <= BM_SOF_N or BM_SRC_RDY_N or not bm_sel;
   down_bm_eof_n <= BM_EOF_N or BM_SRC_RDY_N or not bm_sel;
   down_bm_src_rdy_n <= BM_SRC_RDY_N or not bm_sel;
   
   -- DOWN FSM ----------------------------------------------------------------
   DOWN_FSM : entity work.IB_ENDPOINT_BM_UNIT_FSM
   generic map (
      -- rd and bm trans are only 1clk long when datawidth=128
      IN1_SHORT_TRANS   => BIT128,
      IN2_SHORT_TRANS   => BIT128
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      IN1_SOF_N      => RD_SOF_N,
      IN1_EOF_N      => RD_EOF_N,
      IN1_SRC_RDY_N  => RD_SRC_RDY_N,
      IN1_DST_RDY_N  => RD_DST_RDY_N,

      IN2_SOF_N      => down_bm_sof_n,
      IN2_EOF_N      => down_bm_eof_n,
      IN2_SRC_RDY_N  => down_bm_src_rdy_n,
      IN2_DST_RDY_N  => l2gw_dst_rdy_n,

      OUT_SOF_N      => DOWN_SOF_N,
      OUT_EOF_N      => DOWN_EOF_N,
      OUT_SRC_RDY_N  => DOWN_SRC_RDY_N,
      OUT_DST_RDY_N  => DOWN_DST_RDY_N,

      OUT_MX_SEL     => down_mx
   );

   -- DOWN multiplexor --------------------------------------------------------
   with down_mx select DOWN_DATA <= RD_DATA when '0',
                                    BM_DATA when others;

   -- -------------------------------------------------------------------------
   --                          UP multiplexing logic                         --
   -- -------------------------------------------------------------------------

   up_bm_sof_n <= BM_SOF_N or BM_SRC_RDY_N or bm_sel;
   up_bm_eof_n <= BM_EOF_N or BM_SRC_RDY_N or bm_sel;
   up_bm_src_rdy_n <= BM_SRC_RDY_N or bm_sel;
   
   -- UP FSM ------------------------------------------------------------------
   UP_FSM : entity work.IB_ENDPOINT_BM_UNIT_FSM
   generic map (
      -- g2lr trans is only 1clk long when datawidth=128
      IN1_SHORT_TRANS   => false,
      IN2_SHORT_TRANS   => BIT128
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      IN1_SOF_N      => CPL_SOF_N,
      IN1_EOF_N      => CPL_EOF_N,
      IN1_SRC_RDY_N  => CPL_SRC_RDY_N,
      IN1_DST_RDY_N  => CPL_DST_RDY_N,

      IN2_SOF_N      => up_bm_sof_n,
      IN2_EOF_N      => up_bm_eof_n,
      IN2_SRC_RDY_N  => up_bm_src_rdy_n,
      IN2_DST_RDY_N  => g2lr_dst_rdy_n,

      OUT_SOF_N      => UP_SOF_N,
      OUT_EOF_N      => UP_EOF_N,
      OUT_SRC_RDY_N  => UP_SRC_RDY_N,
      OUT_DST_RDY_N  => UP_DST_RDY_N,

      OUT_MX_SEL     => ib_mx
   );
   
   -- UP multiplexor ----------------------------------------------------------
   with ib_mx select UP_DATA <= CPL_DATA when '0',
                                BM_DATA  when others;

   -- -------------------------------------------------------------------------
   --                     BM_DST_RDY multiplexing logic                      --
   -- -------------------------------------------------------------------------

   -- reg that remembers type of transaction (G2LR or L2GW)
   bm_sel_auxp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            bm_sel_aux <= '0';
         elsif ((not BM_SOF_N and not BM_SRC_RDY_N) = '1') then
            bm_sel_aux <= BM_DATA(0);
         end if;
      end if;
   end process;
   
   -- in first clk bm_sel_aux is not set yet - using BM_DATA(0) directly
   with (not BM_SOF_N and not BM_SRC_RDY_N) select
      bm_sel <= BM_DATA(0) when '1',
                bm_sel_aux when others;

   -- BM_DST_RDY_N multiplexor
   with bm_sel select BM_DST_RDY_N <= g2lr_dst_rdy_n when '0',
                                      l2gw_dst_rdy_n when others;


   -- -------------------------------------------------------------------------
   --                               DONE logic                               --
   -- -------------------------------------------------------------------------
   DONE_UNIT : entity work.IB_ENDPOINT_BM_DONE_UNIT
   port map (
      CLK         => CLK,
      RESET       => RESET,
      
      RD_TAG      => RD_TAG,
      RD_TAG_VLD  => RD_TAG_VLD,
      RD_DONE     => RD_DONE,
      
      CPL_TAG     => CPL_TAG,
      CPL_TAG_VLD => CPL_TAG_VLD,
      
      BM_TAG      => BM_TAG,
      BM_TAG_VLD  => BM_TAG_VLD
   ); 
      
end ib_endpoint_bm_unit_arch;
      
      
      
