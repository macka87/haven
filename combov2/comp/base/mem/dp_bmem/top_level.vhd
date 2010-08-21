-- top_level.vhd : dp_bmem top_level architecture
-- Copyright (C) 2004 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
-- README: This entity is used for test genmem_dp which is instanced
--         with this parameters
--              TEST_BRAM_TYPE := 4; --Block Ram Type - only 1,2,4,9,18,36
--              TEST_DATA_WIDTH := 16; --DATA_WIDTH mod BRAM_TYPE must be 0
--              TEST_ITEMS_COUNT := 65536;-- item size = DATA_WIDTH
--              TEST_OUTPUT_REG := false; -- is output register needed?
--          It means 4 rows 4 columns of 4BramType
--          Cyclic counter increment address and same addres is writen
--          throw port a to generic memory.
--          Port B is conected to lbconmem for testing purposes.
--
-- TODO list :
--
-- ---------------------------------------------------------------------------
--                          Entity declaration
-- ---------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;

-- auxilarity functions and constant needed to evaluate generic address etc.
use WORK.bmem_func.all;

-- ------------------------------------------------------------------------
--                       Architecture declaration
-- ------------------------------------------------------------------------
architecture behavioral of fpga is


-- ---------------------- Internal bus & address decoder -------------------
component LOCAL_BUS is
   Port (
        -- PLX interface
      LAD    : inout std_logic_vector(31 downto 0);-- PLX mux. Addr/Data
      ADS    : in std_logic;    -- Address strobe
      BLAST  : in std_logic;    -- Last transfer in the bus, active: Low
      LHOLD  : in std_logic;    -- PLX requests Local Bus, active: High
      LHOLDA : inout std_logic; -- Hold acknowledge, active: High
      LWR    : in std_logic;    -- Local bus read/write, active: read: Low
      READY  : inout std_logic; -- Data is ready, active: Low
      LRESET : in std_logic;    -- Local Reset
      LCLKF  : in std_logic;    -- Local Clock
      USERo  : in std_logic;    -- USERo = '1': used for prog. CPLD
      --LINT   : in std_logic;    -- Local Interrupt, active LOW

      -- Internal bus signals
      LBCLK   : out std_logic;  -- internal bus clock, up to 100 MHz
      LBFRAME : out std_logic;  -- Frame
      LBHOLDA : in std_logic;   -- Hold Ack
      LBAD    : inout std_logic_vector(15 downto 0); -- Address/Data
      LBAS    : out std_logic;  -- Adress strobe
      LBRW    : out std_logic;  -- Direction (Read#/Write, low : read)
      LBRDY   : in std_logic;   -- Ready
      LBLAST  : out std_logic;  -- Last word in transfer
      -- special

      SWQ_REQ  : in std_logic   -- SW queue request
    );
end component;



component LBCONN_MEM is
   Generic ( BASE       : integer; -- Base address (28 bit)
             ADDR_WIDTH : integer  -- Width of address,
           );
   Port (
      DATA_OUT : out std_logic_vector(15 downto 0);  -- Data output
      DATA_IN  : in std_logic_vector(15 downto 0);   -- Data input
      ADDR     : out std_logic_vector(ADDR_WIDTH-1 downto 0); -- Address output
      RW       : out std_logic;                      -- Write/Read#
      EN       : out std_logic;                      -- Data Enable
      SEL      : out std_logic;                      -- Select
      DRDY     : in std_logic;                       -- Data ready input
      ARDY     : in std_logic;                       -- Address Ready (ACK)
      -- local bus interconnection
      RESET    : in std_logic;
      LBCLK    : in std_logic;
      LBFRAME  : in std_logic;
      LBAS     : in std_logic;
      LBRW     : in std_logic;
      LBLAST   : in std_logic;
      LBAD     : inout std_logic_vector(15 downto 0);
      LBHOLDA  : out std_logic;
      LBRDY    : out std_logic
      );
end component LBCONN_MEM;



component DP_BMEM is
   -- Capacity of 1, 2, 4 Block rams is 16384 bits
   -- Capacity of 9, 18, 36 Block rams is 18432 bits
   generic(
      -- Block Ram Type, only 1, 2, 4, 9, 18, 36 bits
      BRAM_TYPE   : integer;
      DATA_WIDTH  : integer;
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS : integer;
      -- Output directly from BlockRams or throw register
      OUTPUT_REG  : TOUTPUT_REG
   );

   port(
      -- Common interface
      RESET  : in    std_logic; -- Reset only if output_reg

      -- Interface A
      CLKA   : in    std_logic; -- Clock A
      PIPE_ENA : in  std_logic; -- Pipe Enable
      REA    : in    std_logic; -- Read Enable
      WEA    : in    std_logic; -- Write Enable
      ADDRA  : in    std_logic_vector(LOG2(ITEMS)-1 downto 0); -- Address A
      DIA    : in    std_logic_vector(DATA_WIDTH-1 downto 0); -- Data A In
      DOA_DV : out   std_logic; -- Data A Valid
      DOA    : out   std_logic_vector(DATA_WIDTH-1 downto 0); -- Data A Out

      -- Interface B
      CLKB   : in    std_logic; -- Clock B
      PIPE_ENB : in  std_logic; -- Pipe Enable
      REB    : in    std_logic; -- Read Enable
      WEB    : in    std_logic; -- Write Enable
      ADDRB  : in    std_logic_vector(LOG2(ITEMS)-1 downto 0); -- Address B
      DIB    : in    std_logic_vector(DATA_WIDTH-1 downto 0); -- Data B In
      DOB_DV : out   std_logic; -- Data B Valid
      DOB    : out   std_logic_vector(DATA_WIDTH-1 downto 0) -- Data B Out
   );
end component;


-- 4 rows 3 columns
constant TEST_BRAM_TYPE   : integer := 4; --Block Ram Type - only 1,2,4,9,18,36
constant TEST_DATA_WIDTH  : integer := 16; --DATA_WIDTH mod BRAM_TYPE must be 0
constant TEST_ITEMS : integer := 65536;-- item size = DATA_WIDTH
constant TEST_OUTPUT_REG  : TOUTPUT_REG := true; -- is output register needed?

constant TEST_BRAM_COLS      : integer := BRAM_COLUMN_COUNT(TEST_BRAM_TYPE, TEST_ITEMS);
constant OUTPUT_REG_BOOL : boolean :=
                         BRAM_OUT_REG_TO_BOOL(TEST_OUTPUT_REG, TEST_BRAM_COLS);


-- ------------------------------------------------------------------
--                      Signal declaration
-- ------------------------------------------------------------------

-- Global definition
signal reset       : std_logic; -- Global reset active at high

-- Internal bus signals
signal lbclk       : std_logic;
signal lbframe     : std_logic;
signal lbholda     : std_logic;
signal lbad        : std_logic_vector(15 downto 0);
signal lbas        : std_logic;
signal lbrw        : std_logic;
signal lbrdy       : std_logic;
signal lblast      : std_logic;

signal lb_data_out : std_logic_vector(15 downto 0);
signal lb_data_in  : std_logic_vector(15 downto 0);
signal lb_addr     : std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
signal lb_rw       : std_logic;
signal lb_en       : std_logic;
signal lb_sel      : std_logic;
signal lb_drdy     : std_logic;
signal lb_ardy     : std_logic;

-- address counter
signal addr_count : std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
-- data counter
signal data_count : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
-- data ready register
signal aux_drdy : std_logic;
signal aux_drdy2 : std_logic;


-- ------------------------------------------------------------------
--                       Architecture body
-- ------------------------------------------------------------------
begin

reset  <= (not LRESET);  -- LRESET is active in '0'

-- ------------------- Local bus port map --------------------
LB_U : LOCAL_BUS
port map(
   LAD      => LAD,
   ADS      => ADS,
   BLAST    => BLAST,
   LHOLD    => LHOLD,
   LHOLDA   => LHOLDA,
   LWR      => LWR,
   READY    => READY,
   LRESET   => LRESET,
   LCLKF    => LCLKF,
   USERO    => USERO,

   LBCLK    => lbclk,
   LBFRAME  => lbframe,
   LBHOLDA  => lbholda,
   LBAD     => lbad,
   LBAS     => lbas,
   LBRW     => lbrw,
   LBRDY    => lbrdy,
   LBLAST   => lblast,
   SWQ_REQ  => '0'
);


LBCONN_MEM_U: LBCONN_MEM
generic map (
   BASE       => 16#0000000#, -- Base address (28 bit)
   ADDR_WIDTH => LOG2(TEST_ITEMS)
)
port map (
   DATA_OUT => lb_data_out, -- Data output
   DATA_IN  => lb_data_in,  -- Data input
   ADDR     => lb_addr,     -- Address output
   RW       => lb_rw,       -- Write/Read#
   EN       => lb_en,       -- Data Enable
   SEL      => open,        -- Select
   DRDY     => aux_drdy,    -- Data ready input
   ARDY     => '1',         -- Address Ready (ACK)
   -- local bus interconnection
   RESET    => RESET,
   LBCLK    => LBCLK,
   LBFRAME  => LBFRAME,
   LBAS     => LBAS,
   LBRW     => LBRW,
   LBLAST   => LBLAST,
   LBAD     => LBAD,
   LBHOLDA  => LBHOLDA,
   LBRDY    => LBRDY
);

genmem_dp_map: DP_BMEM
-- 4 rows 4 columns
   generic map (
      BRAM_TYPE => TEST_BRAM_TYPE,
      DATA_WIDTH => TEST_DATA_WIDTH,
      ITEMS => TEST_ITEMS,
      OUTPUT_REG => TEST_OUTPUT_REG
      )

   port map(
	   RESET => reset,
      -- Interface A
      CLKA => lbclk,
      PIPE_ENA => '1',
      REA => '1',
      WEA => '1', -- writing to port a
      ADDRA => addr_count,
      DIA => data_count,
      DOA_DV => open,
      DOA => open,
      -- Interface B
      CLKB => lbclk,
      PIPE_ENB => '1',
      REB => lb_en,
      WEB => '0',
      ADDRB => lb_addr,
      DIB => "0000000000000000",
      DOB_DV => open,
      DOB => lb_data_in
   );


-- Counter -------------------------------------------------------------------
Counter: process(reset, lbclk)
begin
   if (reset = '1') then
      addr_count <= (others => '0');
      data_count <= (others => '0');
   elsif (lbclk'event AND lbclk = '1') then
      addr_count <= addr_count + 1;
      data_count(LOG2(TEST_ITEMS)-1 downto 0) <=
      data_count(LOG2(TEST_ITEMS)-1 downto 0) + 1;
   end if;
end process;

NOOUTPUTREG : if not OUTPUT_REG_BOOL generate
-- register aux_drdy ------------------------------------------------------
aux_drdyp: process(reset, lbclk)
begin
   if (reset = '1') then
      aux_drdy <= '0';
 elsif (lbclk'event AND lbclk = '1') then
        aux_drdy <= lb_en;
   end if;
end process;
end generate;


OUTPUTREG : if (OUTPUT_REG_BOOL) generate
-- register aux_drdy ------------------------------------------------------
aux_drdyp: process(reset, lbclk)
begin
   if (reset = '1') then
      aux_drdy <= '0';
      aux_drdy2 <= '0';
   elsif (lbclk'event AND lbclk = '1') then
        aux_drdy2 <=  lb_en;
        aux_drdy <= aux_drdy2;
   end if;
end process;
end generate;




end architecture behavioral;

