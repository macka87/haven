-- mi_splitter_ondriks.vhd: Ondrik's MI Splitter
-- Author(s): Ondrej Lengal <ilengal@fit.vutbr.cz>
--
-- $Id$
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

architecture arch of MI_SPLITTER_ONDRIKS is

   -- -------------------------------------------------------------------------
   --                                 Types
   -- -------------------------------------------------------------------------

   constant MAX_ITEMS   : integer := 8;

   type t_array_of_items is array (0 to MAX_ITEMS-1) of
      std_logic_vector(31 downto 0);

   -- -------------------------------------------------------------------------
   --                                Constants                               --
   -- -------------------------------------------------------------------------
   
   constant LOG2ITEMS   : integer := log2(ITEMS);

   constant PORT_BASES  : t_array_of_items :=
      (PORT0_BASE, PORT1_BASE, PORT2_BASE, PORT3_BASE, PORT4_BASE, PORT5_BASE,
      PORT6_BASE, PORT7_BASE);
   
   constant PORT_LIMITS  : t_array_of_items :=
      (PORT0_LIMIT, PORT1_LIMIT, PORT2_LIMIT, PORT3_LIMIT, PORT4_LIMIT,
      PORT5_LIMIT, PORT6_LIMIT, PORT7_LIMIT);
   
   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

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
   
   -- -----------------------------------------------------------------------
   --                              ASSERTIONS
   -- -----------------------------------------------------------------------
   assert (ITEMS > 0 and ITEMS <= MAX_ITEMS)
      report "ITEMS need to be from range <1, MAX_ITEMS>!"
      severity failure;

   assert (DATA_WIDTH =  8 or DATA_WIDTH = 16 or DATA_WIDTH = 32 or
          DATA_WIDTH = 64 or DATA_WIDTH = 128)
      report "DATA_WIDTH is expected to be one of {8, 16, 32, 64, 128}!"
      severity failure;
   
--   TODO: refine this assertion:
--       * non-overlapping BASE + LIMITs
--       * limits != 0
--       * base = n * limit
--       * limit = 2^n
--          
--   assert (ITEMS < 2 or PORT2_BASE >= PORT1_BASE) and
--          (ITEMS < 3 or PORT3_BASE >= PORT2_BASE) and
--          (ITEMS < 4 or PORT4_BASE >= PORT3_BASE) and
--          (ITEMS < 5 or PORT5_BASE >= PORT4_BASE) and
--          (ITEMS < 6 or PORT6_BASE >= PORT5_BASE) and
--          (ITEMS < 7 or PORT7_BASE >= PORT6_BASE)
--      report "Base addresses of ports must be in ascending order."
--      severity failure;
   
   -- -------------------------------------------------------------------------
   --                              MI Splitter                               --
   -- -------------------------------------------------------------------------
   
   -- DWR, ADDR and BE signals are connected to all interfaces
   COMMON : for i in 0 to (ITEMS-1) generate
      OUT_DWR((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH)    <= pipe_dwr;
      OUT_BE((i+1)*DATA_WIDTH/8-1 downto i*DATA_WIDTH/8) <= pipe_be;
   end generate;
   
   -- output address
   out_addr_gen : for i in 0 to ITEMS - 1 generate
      OUT_ADDR((i+1)*32-1 downto i*32 + log2(PORT_LIMITS(i)))   <= (others => '0');
      OUT_ADDR(i*32+log2(PORT_LIMITS(i))-1 downto i*32)         <=
         pipe_addr(log2(PORT_LIMITS(i))-1 downto 0);
   end generate;

   -- Address decoder ---------------------------------------------------------
   addr_decp: process(pipe_addr)
      variable port_sel_var : integer;
   begin
      port_sel_var := 0;

      for i in MAX_ITEMS-1 downto 0 loop
         if (ITEMS > i and pipe_addr(31 downto log2(PORT_LIMITS(i)))
            = PORT_BASES(i)(31 downto log2(PORT_LIMITS(i)))) then
            port_sel_var := i;
            exit;
         end if;
      end loop;

      port_sel <= conv_std_logic_vector(port_sel_var, LOG2ITEMS);
   end process;
   
   
   -- Routing logic -----------------------------------------------------------
   
   -- RD demultiplexer
   rd_demuxp: process(pipe_rd, port_sel)
   begin
      OUT_RD <= (others => '0');
      for i in 0 to ITEMS-1 loop
         if(conv_std_logic_vector(i, LOG2ITEMS) = port_sel) then
            OUT_RD(i) <= pipe_rd;
         end if;
      end loop;
   end process;

   -- WR demultiplexer
   wr_demuxp: process(pipe_wr, port_sel)
   begin
      OUT_WR <= (others => '0');
      for i in 0 to ITEMS-1 loop
         if(conv_std_logic_vector(i, LOG2ITEMS) = port_sel) then
            OUT_WR(i) <= pipe_wr;
         end if;
      end loop;
   end process;
   
   -- ARDY multiplexer
   ardy_muxp: process(OUT_ARDY, port_sel)
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

   
   gen_pipe_true: if (PIPE = true) generate

      -- MI_PIPE
      pipe_i: entity work.MI_PIPE
      generic map(
         DATA_WIDTH  => DATA_WIDTH,
         ADDR_WIDTH  => 32,
         USE_OUTREG  => PIPE_OUTREG
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

   end generate;

   gen_pipe_fals: if (PIPE = false) generate
      pipe_dwr      <= IN_DWR;
      pipe_addr     <= IN_ADDR;
      pipe_be       <= IN_BE;
      pipe_rd       <= IN_RD;
      pipe_wr       <= IN_WR;
      IN_ARDY       <= pipe_ardy;
      IN_DRD        <= pipe_drd;
      IN_DRDY       <= pipe_drdy;
   end generate;

end;
