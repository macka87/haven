--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    Rearranger (Downwards)
-- Description: 
-- Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
-- Date:         15.4.2011 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity REARRANGER_DOWN is

   generic
   (
      IN_DATA_WIDTH    : integer := 128;
      OUT_DATA_WIDTH   : integer := 64
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      RX_DATA        : in  std_logic_vector(IN_DATA_WIDTH-1 downto 0);
      RX_VALID       : in  std_logic;
      RX_READ_NEXT   : out std_logic;
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      TX_DATA        : out std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      TX_VALID       : out std_logic;
      TX_READ_NEXT   : in  std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of REARRANGER_DOWN is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

constant MUX_WIDTH        : integer := (IN_DATA_WIDTH-1) / OUT_DATA_WIDTH + 1;
constant MUX_INPUT_WIDTH  : integer := MUX_WIDTH*OUT_DATA_WIDTH;
constant MUX_ADDR_WIDTH   : integer := log2(MUX_WIDTH);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- input signals
signal sig_rx_data      : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal sig_rx_read_next : std_logic;
signal sig_rx_valid     : std_logic;

-- output signals
signal sig_tx_data      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal sig_tx_read_next : std_logic;
signal sig_tx_valid     : std_logic;

-- multiplexer signals
signal mux_data_in      : std_logic_vector(MUX_INPUT_WIDTH-1 downto 0);
signal mux_addr_in      : std_logic_vector(MUX_ADDR_WIDTH-1 downto 0);
signal mux_data_out     : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);

-- address counter signals
signal cnt_addr         : std_logic_vector(MUX_ADDR_WIDTH-1 downto 0);
signal cnt_addr_clr     : std_logic;
signal cnt_addr_en      : std_logic;

signal padding          : std_logic_vector(MUX_INPUT_WIDTH-IN_DATA_WIDTH-1 downto 0);

signal is_addr_max      : std_logic;

begin

   assert (IN_DATA_WIDTH > OUT_DATA_WIDTH)
      report "OUT_DATA_WIDTH needs to be smaller than IN_DATA_WIDTH"
      severity failure;

   -- mapping inputs
   sig_rx_data   <= RX_DATA;
   sig_rx_valid  <= RX_VALID;
   RX_READ_NEXT  <= sig_rx_read_next;

   padding <= (others => '0');

   -- mapping multiplexer inputs
   mux_data_in   <= padding & sig_rx_data;
   mux_addr_in   <= cnt_addr;

   -- ------------------------- multiplexer --------------------------------
   mux_i: entity work.GEN_MUX
   generic map 
   (
      DATA_WIDTH => OUT_DATA_WIDTH,
      MUX_WIDTH  => MUX_WIDTH
   )
   port map
   (
      DATA_IN    => mux_data_in,
      SEL        => mux_addr_in,
      DATA_OUT   => mux_data_out
   );

   -- mapping multiplexer outputs
   sig_tx_data      <= mux_data_out;


   -- address counter inputs
   cnt_addr_clr  <= is_addr_max;
   cnt_addr_en   <= sig_tx_read_next AND sig_rx_valid;

   -- ------------------------ address counter -----------------------------
   cnt_addr_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            cnt_addr <= (others => '0');
         elsif (cnt_addr_en = '1') then
            if (cnt_addr_clr = '1') then
               cnt_addr <= (others => '0');
            else
               cnt_addr <= cnt_addr + 1;
            end if;
         end if;
      end if;
   end process;

   cnt_addr_max_comp_p: process (cnt_addr)
   begin
      is_addr_max <= '0';

      if (cnt_addr = MUX_WIDTH-1) then
         is_addr_max <= '1';
      else
         is_addr_max <= '0';
      end if;
   end process;

   -- the valid signal
   sig_tx_valid     <= sig_rx_valid;
   sig_rx_read_next <= sig_tx_read_next AND is_addr_max;

   -- mapping outputs
   TX_DATA          <= sig_tx_data;
   TX_VALID         <= sig_tx_valid;
   sig_tx_read_next <= TX_READ_NEXT;

end architecture;

