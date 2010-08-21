--
-- lb8_16_ios_bridge.vhd: LB 8b --> 16b IOS bridge.
-- Copyright (C) 2004 CESNET
-- Author(s): Lukas Solanka <solanka@liberouter.org>
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the OpenIPCore Hardware General Public
-- License as published by the OpenIPCore Organization; either version
-- 0.20-15092000 of the License, or (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful, but
-- WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- OpenIPCore Hardware General Public License for more details.
--
-- You should have received a copy of the OpenIPCore Hardware Public
-- License along with this program; if not, download it from
-- OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.lb_pkg.all; -- Local bus

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity lb8_16_ios_bridge is
   port(
      -- Common signals
      CLK           : in std_logic;
      RESET         : in std_logic;

      -- Input local bus interface (8b) Connect directly to IOS
      IN8_DWR       : in  std_logic_vector(7 downto 0);
      IN8_BE        : in  std_logic;
      IN8_ADS_N     : in  std_logic;
      IN8_RD_N      : in  std_logic;
      IN8_WR_N      : in  std_logic;
      IN8_ABORT_N   : in  std_logic;
      IN8_DRD       : out std_logic_vector(7 downto 0);
      IN8_RDY_N     : out std_logic;
      IN8_ERR_N     : out std_logic;

      -- Output local bus interface (16b)
      OUT16_DWR     : out std_logic_vector(15 downto 0);
      OUT16_BE      : out std_logic_vector(1 downto 0);
      OUT16_ADS_N   : out std_logic;
      OUT16_RD_N    : out std_logic;
      OUT16_WR_N    : out std_logic;
      OUT16_ABORT_N : out std_logic;
      OUT16_DRD     : in std_logic_vector(15 downto 0);
      OUT16_RDY_N   : in std_logic;
      OUT16_ERR_N   : in std_logic
   );
end entity lb8_16_ios_bridge;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture lb8_16_ios_bridge_arch of lb8_16_ios_bridge is

   -- ---------------------------------------------------------------------
   --                      Output part
   -- ---------------------------------------------------------------------
   constant FIFO_DRD_WIDTH : integer := 16;
   constant FIFO_DRD_ITEMS : integer := 4;


   -- ---------------------------------------------------------------------
   --                      Signals declarations
   -- ---------------------------------------------------------------------
   -- IOB registers
   signal regiob_dwr       : std_logic_vector(7 downto 0);
   signal regiob_be        : std_logic;
   signal regiob_ads_n     : std_logic;
   signal regiob_rd_n      : std_logic;
   signal regiob_wr_n      : std_logic;
   signal regiob_abort_n   : std_logic;
   signal regiob_drd       : std_logic_vector(7 downto 0);
   signal regiob_rdy_n     : std_logic;
   signal regiob_err_n     : std_logic;

   -- Low part of 16b value holders
   signal reg_dwr_low      : std_logic_vector(7 downto 0);
   signal reg_be_low       : std_logic;
   
   -- Merge/split counters
   signal cnt_merge        : std_logic;
   signal cnt_merge_ce     : std_logic;
   signal cnt_merge_ld     : std_logic;

   signal cnt_rdy          : std_logic;
   signal cnt_rdy_ce       : std_logic;
   signal cnt_rdy_ld       : std_logic;

   -- 16b -> 8b multiplexers
   signal mx_drd           : std_logic_vector(7 downto 0);
   signal mx_drd_sel       : std_logic;

   signal fifo_drd_do      : std_logic_vector(15 downto 0);
   signal fifo_drd_we      : std_logic;
   signal fifo_drd_re      : std_logic;
   signal fifo_drd_empty   : std_logic;
   
   -- Do not optimize following registers (Precision)
   attribute dont_touch    : boolean;
   attribute dont_touch of regiob_dwr     : signal is true;
   attribute dont_touch of regiob_be      : signal is true;
   attribute dont_touch of regiob_ads_n   : signal is true;
   attribute dont_touch of regiob_rd_n    : signal is true;
   attribute dont_touch of regiob_wr_n    : signal is true;
   attribute dont_touch of regiob_abort_n : signal is true;
   attribute dont_touch of regiob_drd     : signal is true;
   attribute dont_touch of regiob_rdy_n   : signal is true;
   attribute dont_touch of regiob_err_n   : signal is true;

begin


   -- ---------------------------------------------------------------------
   --                      Input part
   -- ---------------------------------------------------------------------

   -- Input IOB registers -------------------------------------------------
   regiobs_inp: process(CLK, RESET)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            regiob_ads_n   <= '1';
            regiob_rd_n    <= '1';
            regiob_wr_n    <= '1';
            regiob_abort_n <= '1';
         else
            regiob_dwr     <= IN8_DWR;
            regiob_be      <= IN8_BE;
            regiob_ads_n   <= IN8_ADS_N;
            regiob_rd_n    <= IN8_RD_N;
            regiob_wr_n    <= IN8_WR_N;
            regiob_abort_n <= IN8_ABORT_N;
         end if;
      end if;
   end process;

   -- cnt_merge counter ------------------------------------------------
   cnt_merge_ce <= not (regiob_ads_n and regiob_rd_n and regiob_wr_n);
   cnt_merge_ld <= not regiob_abort_n;
   cnt_mergep: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_merge <= '1';
         elsif (cnt_merge_ce = '1') then
            if (cnt_merge_ld = '1') then
               cnt_merge <= '1';
            else
               cnt_merge <= not cnt_merge;
            end if;
         end if;
      end if;
   end process;


   -- low parts registers (DWR and BE)
   regs_lowp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         reg_dwr_low <= regiob_dwr;
         reg_be_low  <= regiob_be;
      end if;
   end process;

   -- Interface mapping
   OUT16_DWR    <= regiob_dwr & reg_dwr_low;
   OUT16_BE     <= regiob_be  & reg_be_low;

   OUT16_ADS_N     <= regiob_ads_n or cnt_merge;
   OUT16_RD_N      <= regiob_rd_n or cnt_merge;
   OUT16_WR_N      <= regiob_wr_n or cnt_merge;
   OUT16_ABORT_N   <= regiob_abort_n;



   -- ---------------------------------------------------------------------
   --                      Output part
   -- ---------------------------------------------------------------------

   -- DRD FIFO -------------------------------------------------------------
   FIFO_DRD_I: entity work.fifo
      generic map (
         DATA_WIDTH     => FIFO_DRD_WIDTH,
         ITEMS          => FIFO_DRD_ITEMS
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,
   
         -- write interface
         DATA_IN        => OUT16_DRD,
         WRITE_REQ      => fifo_drd_we,
         FULL           => open,
         LSTBLK         => open,
   
         -- read interface
         DATA_OUT       => fifo_drd_do,
         READ_REQ       => fifo_drd_re,
         EMPTY          => fifo_drd_empty
      );

   fifo_drd_we <= not OUT16_RDY_N; -- Should never get full !!!
   fifo_drd_re <= not cnt_rdy;
   
   -- cnt_rdy counter ------------------------------------------------
   cnt_rdy_ce <= not fifo_drd_empty;
   cnt_rdy_ld <= not regiob_abort_n;
   cnt_rdyp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_rdy <= '1';
         elsif (cnt_rdy_ce = '1') then
            if (cnt_rdy_ld = '1') then
               cnt_rdy <= '1';
            else
               cnt_rdy <= not cnt_rdy;
            end if;
         end if;
      end if;
   end process;


   -- multiplexor mx_drd ----------------------------------------------
   mx_drdp: process(cnt_rdy, fifo_drd_do)
   begin
      case cnt_rdy is
         when '0' => mx_drd <= fifo_drd_do(15 downto 8);
         when '1' => mx_drd <= fifo_drd_do( 7 downto 0);
         when others => mx_drd <= (others => 'X');
      end case;
   end process;

   -- Output IOB registers
   regiobs_outp: process(CLK, RESET)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            regiob_rdy_n   <= '1';
         else
            regiob_drd     <= mx_drd;
            regiob_rdy_n   <= fifo_drd_empty;
            regiob_err_n   <= OUT16_ERR_N;
         end if;
      end if;
   end process;

   -- Interface maping
   IN8_DRD     <= regiob_drd;
   IN8_RDY_N   <= regiob_rdy_n;
   IN8_ERR_N   <= regiob_err_n;


end architecture lb8_16_ios_bridge_arch;

