--
-- mi_splitter_plus_arch.vhd: MI Splitter plus
-- Copyright (C) 2010 CESNET
-- Author(s): Vaclav Bartos <washek@liberouter.org>
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

architecture mi_splitter_plus_arch of MI_SPLITTER_PLUS is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
   
   constant LOG2ITEMS   : integer := log2(ITEMS);
   
   signal port_sel      : std_logic_vector(LOG2ITEMS-1 downto 0);
   
   signal pipe_dwr      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal pipe_addr     : std_logic_vector(31 downto 0);
   signal pipe_be       : std_logic_vector(DATA_WIDTH/8-1 downto 0);
   signal pipe_rd       : std_logic;
   signal pipe_wr       : std_logic;
   signal pipe_ardy     : std_logic;
   signal pipe_drd      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal pipe_drdy     : std_logic;
   
begin
   
   -- Asserts -----------------------------------------------------------------
   assert ITEMS > 0 and DATA_WIDTH > 0
      report "ITEMS and DATA_WIDTH must be positive values."
      severity error;
   
   assert DATA_WIDTH =  8 or DATA_WIDTH = 16 or DATA_WIDTH = 32 or
          DATA_WIDTH = 64 or DATA_WIDTH = 128
      report "DATA_WIDTH is expected to be one of {8,16,32,64,128}."
      severity warning;
   
   assert (ITEMS <= 2 or PORT2_BASE >= PORT1_BASE) and
          (ITEMS <= 3 or PORT3_BASE >= PORT2_BASE) and
          (ITEMS <= 4 or PORT4_BASE >= PORT3_BASE) and
          (ITEMS <= 5 or PORT5_BASE >= PORT4_BASE) and
          (ITEMS <= 6 or PORT6_BASE >= PORT5_BASE) and
          (ITEMS <= 7 or PORT7_BASE >= PORT6_BASE)
      report "Base addresses of ports must be in ascending order."
      severity error;
   
   -- -------------------------------------------------------------------------
   --                              MI Splitter                               --
   -- -------------------------------------------------------------------------
   
   -- DWR, ADDR and BE signals are connected to all interfaces
   COMMON : for i in 0 to (ITEMS-1) generate
      OUT_DWR((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH)    <= pipe_dwr;
      OUT_ADDR((i+1)*32-1 downto i*32)                   <= pipe_addr;
      OUT_BE((i+1)*DATA_WIDTH/8-1 downto i*DATA_WIDTH/8) <= pipe_be;
   end generate;
   
   -- Address decoder ---------------------------------------------------------
   addr_decp: process(pipe_addr)
      variable port_sel_var : std_logic_vector(2 downto 0);
   begin
      port_sel_var := (others => '0');
      if (ITEMS > 7 and (pipe_addr and ADDR_CMP_MASK) >= PORT7_BASE) then
         port_sel_var := "111";
      elsif (ITEMS > 6 and (pipe_addr and ADDR_CMP_MASK) >= PORT6_BASE) then
         port_sel_var := "110";
      elsif (ITEMS > 5 and (pipe_addr and ADDR_CMP_MASK) >= PORT5_BASE) then
         port_sel_var := "101";
      elsif (ITEMS > 4 and (pipe_addr and ADDR_CMP_MASK) >= PORT4_BASE) then
         port_sel_var := "100";
      elsif (ITEMS > 3 and (pipe_addr and ADDR_CMP_MASK) >= PORT3_BASE) then
         port_sel_var := "011";
      elsif (ITEMS > 2 and (pipe_addr and ADDR_CMP_MASK) >= PORT2_BASE) then
         port_sel_var := "010";
      elsif (ITEMS > 1 and (pipe_addr and ADDR_CMP_MASK) >= PORT1_BASE) then
         port_sel_var := "001";
      else
         port_sel_var := "000";
      end if;
      port_sel <= port_sel_var(LOG2ITEMS-1 downto 0);
   end process;
   
   
   -- Routing logic -----------------------------------------------------------
   
   -- RD demultiplexer
   rd_demuxp: process(pipe_rd,port_sel)
   begin
      OUT_RD <= (others => '0');
      for i in 0 to ITEMS-1 loop
         if(conv_std_logic_vector(i, LOG2ITEMS) = port_sel) then
            OUT_RD(i) <= pipe_rd;
         end if;
      end loop;
   end process;

   -- WR demultiplexer
   wr_demuxp: process(pipe_wr,port_sel)
   begin
      OUT_WR <= (others => '0');
      for i in 0 to ITEMS-1 loop
         if(conv_std_logic_vector(i, LOG2ITEMS) = port_sel) then
            OUT_WR(i) <= pipe_wr;
         end if;
      end loop;
   end process;
   
   -- ARDY multiplexer
   ardy_muxp: process(OUT_ARDY,port_sel)
   begin
      pipe_ardy <= '0';
      for i in 0 to ITEMS-1 loop
         if(conv_std_logic_vector(i, LOG2ITEMS) = port_sel) then
            pipe_ardy <= OUT_ARDY(i);
         end if;
      end loop;
   end process;
   
   -- DRD multiplexer
   drd_muxp: process(OUT_DRD, OUT_DRDY)
   begin
      pipe_drd <= (others => 'X');
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
      ADDR_WIDTH  => 32,
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

end mi_splitter_plus_arch;
