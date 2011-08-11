-- cdc_fifo.vhd: Clock-Domain Crossing FIFO for Virtex-5
-- Author(s): Ondrej Lengal <lengal@liberouter.org>
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity CDC_FIFO is
   generic
   (
      -- data width
      DATA_WIDTH       : integer
   );
   port
   (
      -- asynchronous reset
      RESET            :  in std_logic;

      -- write interface
      WR_CLK           :  in std_logic;
      WR_DATA          :  in std_logic_vector(DATA_WIDTH-1 downto 0);
      WR_WRITE         :  in std_logic;
      WR_FULL          : out std_logic;
      WR_ALMOST_FULL   : out std_logic;

      -- read interface
      RD_CLK           :  in std_logic;
      RD_DATA          : out std_logic_vector(DATA_WIDTH-1 downto 0);
      RD_READ          :  in std_logic;
      RD_EMPTY         : out std_logic;
      RD_ALMOST_EMPTY  : out std_logic
   );
end entity;


-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of CDC_FIFO is

-- ==========================================================================
--                                    COMPONENTS
-- ==========================================================================

component asfifo_lut_1
	port (
	rst: IN std_logic;
	wr_clk: IN std_logic;
	rd_clk: IN std_logic;
	din: IN std_logic_VECTOR(0 downto 0);
	wr_en: IN std_logic;
	rd_en: IN std_logic;
	dout: OUT std_logic_VECTOR(0 downto 0);
	full: OUT std_logic;
	empty: OUT std_logic;
	prog_full: OUT std_logic;
	prog_empty: OUT std_logic);
end component;

component asfifo_lut_8
	port (
	rst: IN std_logic;
	wr_clk: IN std_logic;
	rd_clk: IN std_logic;
	din: IN std_logic_VECTOR(7 downto 0);
	wr_en: IN std_logic;
	rd_en: IN std_logic;
	dout: OUT std_logic_VECTOR(7 downto 0);
	full: OUT std_logic;
	empty: OUT std_logic;
	prog_full: OUT std_logic;
	prog_empty: OUT std_logic);
end component;

component asfifo_lut_16
	port (
	rst: IN std_logic;
	wr_clk: IN std_logic;
	rd_clk: IN std_logic;
	din: IN std_logic_VECTOR(15 downto 0);
	wr_en: IN std_logic;
	rd_en: IN std_logic;
	dout: OUT std_logic_VECTOR(15 downto 0);
	full: OUT std_logic;
	empty: OUT std_logic;
	prog_full: OUT std_logic;
	prog_empty: OUT std_logic);
end component;

component asfifo_lut_9
	port (
	rst: IN std_logic;
	wr_clk: IN std_logic;
	rd_clk: IN std_logic;
	din: IN std_logic_VECTOR(8 downto 0);
	wr_en: IN std_logic;
	rd_en: IN std_logic;
	dout: OUT std_logic_VECTOR(8 downto 0);
	full: OUT std_logic;
	empty: OUT std_logic;
	prog_full: OUT std_logic;
	prog_empty: OUT std_logic);
end component;

component asfifo_lut_71
	port (
	rst: IN std_logic;
	wr_clk: IN std_logic;
	rd_clk: IN std_logic;
	din: IN std_logic_VECTOR(70 downto 0);
	wr_en: IN std_logic;
	rd_en: IN std_logic;
	dout: OUT std_logic_VECTOR(70 downto 0);
	full: OUT std_logic;
	empty: OUT std_logic;
	prog_full: OUT std_logic;
	prog_empty: OUT std_logic);
end component;

component asfifo_lut_73
	port (
	rst: IN std_logic;
	wr_clk: IN std_logic;
	rd_clk: IN std_logic;
	din: IN std_logic_VECTOR(72 downto 0);
	wr_en: IN std_logic;
	rd_en: IN std_logic;
	dout: OUT std_logic_VECTOR(72 downto 0);
	full: OUT std_logic;
	empty: OUT std_logic;
	prog_full: OUT std_logic;
	prog_empty: OUT std_logic);
end component;

component asfifo_lut_136
	port (
	rst: IN std_logic;
	wr_clk: IN std_logic;
	rd_clk: IN std_logic;
	din: IN std_logic_VECTOR(135 downto 0);
	wr_en: IN std_logic;
	rd_en: IN std_logic;
	dout: OUT std_logic_VECTOR(135 downto 0);
	full: OUT std_logic;
	empty: OUT std_logic;
	prog_full: OUT std_logic;
	prog_empty: OUT std_logic);
end component;

-- ==========================================================================
--                                      TYPES
-- ==========================================================================

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

begin

   -- -----------------------------------------------------------------------
   --                              Assertions
   -- -----------------------------------------------------------------------
   assert ((DATA_WIDTH =   1) OR
           (DATA_WIDTH =   8) OR
           (DATA_WIDTH =   9) OR
           (DATA_WIDTH =  16) OR
           (DATA_WIDTH =  71) OR 
           (DATA_WIDTH =  73) OR 
           (DATA_WIDTH = 136)) 
      report "Invalid data width"
      severity failure;

gen_asfifo_1:
   if (DATA_WIDTH = 1) generate

      fifo_1 : asfifo_lut_1
		port map (
			rst => RESET,
			wr_clk => WR_CLK,
			rd_clk => RD_CLK,
			din => WR_DATA,
			wr_en => WR_WRITE,
			rd_en => RD_READ,
			dout => RD_DATA,
			full => WR_FULL,
			empty => RD_EMPTY,
			prog_full => WR_ALMOST_FULL,
			prog_empty => RD_ALMOST_EMPTY);
   end generate;

gen_asfifo_8:
   if (DATA_WIDTH = 8) generate

      fifo_8 : asfifo_lut_8
		port map (
			rst => RESET,
			wr_clk => WR_CLK,
			rd_clk => RD_CLK,
			din => WR_DATA,
			wr_en => WR_WRITE,
			rd_en => RD_READ,
			dout => RD_DATA,
			full => WR_FULL,
			empty => RD_EMPTY,
			prog_full => WR_ALMOST_FULL,
			prog_empty => RD_ALMOST_EMPTY);
   end generate;

gen_asfifo_9:
   if (DATA_WIDTH = 9) generate

      fifo_9 : asfifo_lut_9
		port map (
			rst => RESET,
			wr_clk => WR_CLK,
			rd_clk => RD_CLK,
			din => WR_DATA,
			wr_en => WR_WRITE,
			rd_en => RD_READ,
			dout => RD_DATA,
			full => WR_FULL,
			empty => RD_EMPTY,
			prog_full => WR_ALMOST_FULL,
			prog_empty => RD_ALMOST_EMPTY);
   end generate;

gen_asfifo_16:
   if (DATA_WIDTH = 16) generate

      fifo_16 : asfifo_lut_16
		port map (
			rst => RESET,
			wr_clk => WR_CLK,
			rd_clk => RD_CLK,
			din => WR_DATA,
			wr_en => WR_WRITE,
			rd_en => RD_READ,
			dout => RD_DATA,
			full => WR_FULL,
			empty => RD_EMPTY,
			prog_full => WR_ALMOST_FULL,
			prog_empty => RD_ALMOST_EMPTY);
   end generate;

gen_asfifo_71:
   if (DATA_WIDTH = 71) generate

      fifo_71 : asfifo_lut_71
		port map (
			rst => RESET,
			wr_clk => WR_CLK,
			rd_clk => RD_CLK,
			din => WR_DATA,
			wr_en => WR_WRITE,
			rd_en => RD_READ,
			dout => RD_DATA,
			full => WR_FULL,
			empty => RD_EMPTY,
			prog_full => WR_ALMOST_FULL,
			prog_empty => RD_ALMOST_EMPTY);
   end generate;

gen_asfifo_73:
   if (DATA_WIDTH = 73) generate

      fifo_73 : asfifo_lut_73
		port map (
			rst => RESET,
			wr_clk => WR_CLK,
			rd_clk => RD_CLK,
			din => WR_DATA,
			wr_en => WR_WRITE,
			rd_en => RD_READ,
			dout => RD_DATA,
			full => WR_FULL,
			empty => RD_EMPTY,
			prog_full => WR_ALMOST_FULL,
			prog_empty => RD_ALMOST_EMPTY);
   end generate;

gen_asfifo_136:
   if (DATA_WIDTH = 136) generate

      fifo_136 : asfifo_lut_136
		port map (
			rst => RESET,
			wr_clk => WR_CLK,
			rd_clk => RD_CLK,
			din => WR_DATA,
			wr_en => WR_WRITE,
			rd_en => RD_READ,
			dout => RD_DATA,
			full => WR_FULL,
			empty => RD_EMPTY,
			prog_full => WR_ALMOST_FULL,
			prog_empty => RD_ALMOST_EMPTY);
   end generate;

end architecture;
