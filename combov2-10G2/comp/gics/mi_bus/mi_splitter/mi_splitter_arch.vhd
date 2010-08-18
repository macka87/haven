--
-- mi_splitter_arch.vhd: MI Splitter
-- Copyright (C) 2008 CESNET
-- Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                          ARCHITECTURE DECLARATION                         --
-- ---------------------------------------------------------------------------- 

architecture mi_splitter_arch of MI_SPLITTER is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   constant LOG2ITEMS      : integer := log2(ITEMS);
   constant ADDR_SEL_WIDTH : integer := max(LOG2ITEMS, 1);
   
   signal addr_sel      : std_logic_vector(ADDR_SEL_WIDTH-1 downto 0);
   signal addr          : std_logic_vector(ADDR_WIDTH-1 downto 0);
   
   signal pipe_dwr      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal pipe_addr     : std_logic_vector(ADDR_WIDTH+LOG2ITEMS-1 downto 0);
   signal pipe_be       : std_logic_vector(DATA_WIDTH/8-1 downto 0);
   signal pipe_rd       : std_logic;
   signal pipe_wr       : std_logic;
   signal pipe_ardy     : std_logic;
   signal pipe_drd      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal pipe_drdy     : std_logic;
   
begin
   
   -- Asserts -----------------------------------------------------------------
   assert ITEMS > 0 and DATA_WIDTH > 0 and ADDR_WIDTH > 0
      report "ITEMS, DATA_WIDTH and ADDR_WIDTH must be positive values."
      severity error;
   
   assert DATA_WIDTH =  8 or DATA_WIDTH = 16 or DATA_WIDTH = 32 or
          DATA_WIDTH = 64 or DATA_WIDTH = 128
      report "DATA_WIDTH is expected to be one of {8,16,32,64,128}."
      severity warning;
   
   assert ADDR_WIDTH <= 32
      report "ADDR_WIDTH is not expected to be greater than 32."
      severity warning;
   
   
   -- -------------------------------------------------------------------------
   --                              MI Splitter                               --
   -- -------------------------------------------------------------------------
   
   addr     <= pipe_addr(ADDR_WIDTH-1 downto 0);
   
   -- DWR, ADDR and BE signals are connected to all interfaces
   COMMON : for i in 0 to (ITEMS-1) generate
      OUT_DWR((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH)    <= pipe_dwr;
      OUT_ADDR((i+1)*ADDR_WIDTH-1 downto i*ADDR_WIDTH)   <= addr;
      OUT_BE((i+1)*DATA_WIDTH/8-1 downto i*DATA_WIDTH/8) <= pipe_be;
   end generate;

   items_gt_1: if ITEMS > 1 generate
      
      addr_sel <= pipe_addr(ADDR_WIDTH+LOG2ITEMS-1 downto ADDR_WIDTH);
      
      -- RD demultiplexer
      rd_demuxp: process(pipe_rd,addr_sel)
      begin
         OUT_RD <= (others => '0');
         for i in 0 to ITEMS-1 loop
            if(conv_std_logic_vector(i, LOG2ITEMS) = addr_sel) then
               OUT_RD(i) <= pipe_rd;
            end if;
         end loop;
      end process;

      -- WR demultiplexer
      wr_demuxp: process(pipe_wr,addr_sel)
      begin
         OUT_WR <= (others => '0');
         for i in 0 to ITEMS-1 loop
            if(conv_std_logic_vector(i, LOG2ITEMS) = addr_sel) then
               OUT_WR(i) <= pipe_wr;
            end if;
         end loop;
      end process;
      
      -- ARDY multiplexer
      ardy_muxp: process(OUT_ARDY,addr_sel)
      begin
         pipe_ardy <= '0';
         for i in 0 to ITEMS-1 loop
            if(conv_std_logic_vector(i, LOG2ITEMS) = addr_sel) then
               pipe_ardy <= OUT_ARDY(i);
            end if;
         end loop;
      end process;
      
   end generate;
   
   items_eq_1: if ITEMS = 1 generate
      OUT_RD(0)   <= pipe_rd;
      OUT_WR(0)   <= pipe_wr;
      pipe_ardy   <= OUT_ARDY(0);
   end generate;
   
   -- DRD multiplexer
   drd_muxp: process(OUT_DRD, OUT_DRDY)
   begin
      pipe_drd <= OUT_DRD(DATA_WIDTH-1 downto 0);
      for i in 0 to ITEMS-1 loop
         if(OUT_DRDY(i) = '1') then
            pipe_drd <= OUT_DRD((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH);
            exit;
         end if;
      end loop;
   end process;
   
   -- logic OR of DRDYs
   drdy_muxp: process(OUT_DRDY)
      variable var: std_logic;
   begin
      var := '0';
      for i in 0 to ITEMS-1 loop
         var := var or OUT_DRDY(i);
      end loop;
      pipe_drdy <= var;
   end process;
   
   
   -- MI_PIPE
   pipe_i: entity work.MI_PIPE
   generic map(
      DATA_WIDTH  => DATA_WIDTH,
      ADDR_WIDTH  => ADDR_WIDTH + LOG2ITEMS,
      USE_OUTREG  => PIPE_OUTREG,
      FAKE_PIPE   => not PIPE
   )
   port map(
      -- Common interface
      CLK         => CLK,
      RESET       => RESET,
      
      -- Input MI interface
      IN_DWR      => IN_DWR,
      IN_ADDR     => IN_ADDR,
      IN_BE       => IN_BE,
      IN_RD       => IN_RD,
      IN_WR       => IN_WR,
      IN_ARDY     => IN_ARDY,
      IN_DRD      => IN_DRD,
      IN_DRDY     => IN_DRDY,
      
      -- Output MI interface
      OUT_DWR     => pipe_dwr,
      OUT_ADDR    => pipe_addr,
      OUT_BE      => pipe_be,
      OUT_RD      => pipe_rd,
      OUT_WR      => pipe_wr,
      OUT_ARDY    => pipe_ardy,
      OUT_DRD     => pipe_drd,
      OUT_DRDY    => pipe_drdy
   );
   
end mi_splitter_arch;
