--
-- lb16_8_ios_bridge.vhd: LB 16b --> 8b IOS bridge.
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

use work.lb_pkg.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity lb16_8_ios_bridge is
   port(
      -- Common signals
      CLK         : in std_logic; -- 8b will be resampled to this clock
      CLK8        : in std_logic; -- 8b clock directly from IOS 
      RESET       : in std_logic;

      -- Input local bus interface (16b)
      IN16_DWR     : in  std_logic_vector(15 downto 0);
      IN16_BE      : in  std_logic_vector(1 downto 0);
      IN16_ADS_N   : in  std_logic;
      IN16_RD_N    : in  std_logic;
      IN16_WR_N    : in  std_logic;
      IN16_ABORT_N : in  std_logic;
      IN16_DRD     : out std_logic_vector(15 downto 0);
      IN16_RDY_N   : out std_logic;
      IN16_ERR_N   : out std_logic;
      
      -- Output local bus interface (8b) Connect directly to IOS
      OUT8_DWR     : out std_logic_vector(7 downto 0);
      OUT8_BE      : out std_logic;
      OUT8_ADS_N   : out std_logic;
      OUT8_RD_N    : out std_logic;
      OUT8_WR_N    : out std_logic;
      OUT8_ABORT_N : out std_logic;
      OUT8_DRD     : in  std_logic_vector(7 downto 0);
      OUT8_RDY_N   : in  std_logic;
      OUT8_ERR_N   : in  std_logic
   );
end entity lb16_8_ios_bridge;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture lb16_8_ios_bridge_arch of lb16_8_ios_bridge is
   -- ---------------------------------------------------------------------
   --                      Constants
   -- ---------------------------------------------------------------------
   constant FIFO_DATA_WIDTH : integer := 16 + 2 + 3; -- DATA + BE + ADS,RD,WR
   constant FIFO_ITEMS      : integer := 16;
   constant FIFO_BLOCK_SIZE : integer := 1;
   

   -- ---------------------------------------------------------------------
   --                      Signals
   -- ---------------------------------------------------------------------
   -- Requests FIFO 
   signal fifo_di       : std_logic_vector(FIFO_DATA_WIDTH-1 downto 0);
   signal fifo_wr       : std_logic;
   signal fifo_do       : std_logic_vector(FIFO_DATA_WIDTH-1 downto 0);
   signal fifo_rd       : std_logic;
   signal fifo_empty    : std_logic;
   
   -- FIFO output remap
   signal ads_n_out : std_logic;
   signal rd_n_out : std_logic;
   signal wr_n_out : std_logic;
   signal be_out : std_logic_vector(1 downto 0);
   signal dwr_out : std_logic_vector(15 downto 0);

   -- Splitting multiplexers
   signal mx_dwr        : std_logic_vector(7 downto 0);
   signal mx_dwr_sel    : std_logic;
   signal mx_be         : std_logic;
   signal mx_be_sel     : std_logic;

   -- Split/merge counters
   signal cnt_split     : std_logic_vector(0 downto 0);
   signal cnt_split_ce  : std_logic;
   signal cnt_split_ld  : std_logic;

   signal cnt_rdy       : std_logic;
   signal cnt_rdy_ce    : std_logic;
   signal cnt_rdy_ld    : std_logic;

   -- Input/output IOB registers
   signal regiob_dwr    : std_logic_vector(7 downto 0);
   signal regiob_be     : std_logic;
   signal regiob_ads_n  : std_logic;
   signal regiob_wr_n   : std_logic;
   signal regiob_rd_n   : std_logic;
   signal regiob_in_drd    : std_logic_vector(7 downto 0);
   signal regiob_in_rdy_n  : std_logic;
   signal regiob_in_err_n  : std_logic;

   -- Input reclocked registers
   signal reg_drd8      : std_logic_vector(7 downto 0);
   signal reg_rdy_n     : std_logic;
   signal reg_err_n     : std_logic;
   signal reg_drd_low   : std_logic_vector(7 downto 0);

   -- DRD mask (see description in the generate statement)
   signal drd_mask      : std_logic_vector(15 downto 0);

   signal clk_n         : std_logic;

   -- Do not optimize following registers (Precision)
   attribute dont_touch    : boolean;
   attribute dont_touch of regiob_dwr     : signal is true;
   attribute dont_touch of regiob_be      : signal is true;
   attribute dont_touch of regiob_ads_n   : signal is true;
   attribute dont_touch of regiob_rd_n    : signal is true;
   attribute dont_touch of regiob_wr_n    : signal is true;
   attribute dont_touch of regiob_in_drd     : signal is true;
   attribute dont_touch of regiob_in_rdy_n   : signal is true;
   attribute dont_touch of regiob_in_err_n   : signal is true;
begin

   
   -- ---------------------------------------------------------------------
   --                      Output part
   -- ---------------------------------------------------------------------

   -- FIFO to keep up to 16 requests ---------------------------------------
   REQ_FIFO_I: entity work.FIFO
   generic map (
      DATA_WIDTH     => FIFO_DATA_WIDTH,
      DISTMEM_TYPE   => 16,
      ITEMS          => FIFO_ITEMS,
      BLOCK_SIZE     => FIFO_BLOCK_SIZE
   )
   port map (
      RESET    => RESET,
      CLK      => CLK,

      -- Write interface
      DATA_IN  => fifo_di,
      WRITE_REQ=> fifo_wr,
      FULL     => open,
      LSTBLK   => open,

      -- Read interface
      DATA_OUT => fifo_do,
      READ_REQ => cnt_split(0),
      EMPTY    => fifo_empty
   );

   -- Fifo signals mapping
   fifo_di(0)           <= IN16_ads_n;
   fifo_di(1)           <= IN16_rd_n;
   fifo_di(2)           <= IN16_wr_n;
   fifo_di(4 downto 3)  <= IN16_be;
   fifo_di(20 downto 5) <= IN16_dwr;

   fifo_wr <= not (IN16_ads_n and IN16_rd_n and IN16_wr_n);

   ads_n_out <= fifo_do(0);
   rd_n_out  <= fifo_do(1);
   wr_n_out  <= fifo_do(2);
   be_out    <= fifo_do(4 downto 3);
   dwr_out   <= fifo_do(20 downto 5);
   


   -- cnt_split counter ------------------------------------------------
   cnt_split_ce <= not fifo_empty;
   cnt_split_ld <= not IN16_abort_n;
   cnt_splitp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_split <= (others => '0');
         elsif (cnt_split_ce = '1') then
            if (cnt_split_ld = '1') then
               cnt_split <= (others => '0');
            else
               cnt_split <= cnt_split + 1;
            end if;
         end if;
      end if;
   end process;

   
   -- multiplexor mx_dwr ----------------------------------------------
   mx_dwrp: process(cnt_split, dwr_out)
   begin
      case cnt_split(0) is
         when '0' => mx_dwr <= dwr_out(7 downto 0);
         when '1' => mx_dwr <= dwr_out(15 downto 8);
         when others => mx_dwr <= (others => 'X');
      end case;
   end process;


   -- multiplexor mx_be ----------------------------------------------
   mx_bep: process(cnt_split, be_out)
   begin
      case cnt_split(0) is
         when '0' => mx_be <= be_out(0);
         when '1' => mx_be <= be_out(1);
         when others => mx_be <= 'X';
      end case;
   end process;

   -- Output IOB registers
   regiobs_out: process(CLK, RESET)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            regiob_ads_n   <= '1';
            regiob_wr_n    <= '1';
            regiob_rd_n    <= '1';
         else
            regiob_dwr     <= mx_dwr;
            regiob_be      <= mx_be;
            regiob_ads_n   <= ads_n_out or fifo_empty;
            regiob_wr_n    <= wr_n_out or fifo_empty;
            regiob_rd_n    <= rd_n_out or fifo_empty;
         end if;
      end if;
   end process;

   -- Output interface mapping
   OUT8_dwr     <= regiob_dwr;
   OUT8_ads_n   <= regiob_ads_n;
   OUT8_be      <= regiob_be;
   OUT8_wr_n    <= regiob_wr_n;
   OUT8_rd_n    <= regiob_rd_n;
   OUT8_abort_n <= IN16_abort_n; -- ABORT propagated without delay


   -- ---------------------------------------------------------------------
   --                      Input part
   -- ---------------------------------------------------------------------

   -- Input IOB registers
   regiobs_inp: process(CLK8, RESET)
   begin
      if (CLK8'event and CLK8 = '1') then
         if (RESET = '1') then
            regiob_in_rdy_n   <= '1';
            regiob_in_err_n   <= '1';
         else
            regiob_in_drd     <= OUT8_drd;
            regiob_in_rdy_n   <= OUT8_rdy_n;
            regiob_in_err_n   <= OUT8_err_n;
         end if;
      end if;
   end process;

   -- Input clock resampling
   regs_reclockp: process(CLK, RESET)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reg_rdy_n   <= '1';
            reg_err_n   <= '1';
         else
            reg_drd8    <= regiob_in_drd;
            reg_rdy_n   <= regiob_in_rdy_n;
            reg_err_n   <= regiob_in_err_n;
         end if;
      end if;
   end process;


   -- cnt_rdy counter ------------------------------------------------
   cnt_rdy_ce <= not reg_rdy_n;
   cnt_rdy_ld <= not IN16_abort_n;
   cnt_rdyp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_rdy <= '1';
         else
            if (cnt_rdy_ce = '1') then
               if (cnt_rdy_ld = '1') then
                  cnt_rdy <= '1';
               else
                  cnt_rdy <= not cnt_rdy;
               end if;
            end if;
         end if;
      end if;
   end process;


   -- Resulting data register
   reg_drd_lowp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         reg_drd_low <= reg_drd8;
      end if;
   end process;

   -- Mask out data signals when rdy_n deasserted.
   -- This must be done to ensure consistency with LB_SWITCH which does no
   -- multiplex into the upstream port. It only ORs DRD signals from downstream
   -- ports. So that means we must ensure DRD = (others => '0') when no data is
   -- being sent
   gen_drd_mask: for i in 15 downto 0 generate
      drd_mask(i) <= not (reg_rdy_n or cnt_rdy);
   end generate;


   -- Interface mapping
   IN16_drd    <= (reg_drd8 & reg_drd_low) and drd_mask;
   IN16_rdy_n  <= reg_rdy_n or cnt_rdy;
   IN16_err_n  <= reg_err_n;
   

end architecture lb16_8_ios_bridge_arch;

