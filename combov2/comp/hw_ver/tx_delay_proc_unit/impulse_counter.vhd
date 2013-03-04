-- --------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    TX Asynchronous FrameLink Unit Impulse Counter
-- Description: 
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================

-- This unit serves as the counter of TX_ASYNC_FL_UNIT that gives a single impulse when it finishes counting.
entity IMPULSE_COUNTER is
   generic
   (
      DATA_WIDTH     : integer
   );
   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------- INPUT -----------
      -- the number of clock cycles to wait (aka 'the delay')
      DATA           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      -- load the data into the counter and starts counting
      LOAD           : in  std_logic;

      -- ----------- OUTPUT -----------
      -- produces an impulse when the counter reaches zero
      ZERO_IMPULSE   : out std_logic
   );
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of IMPULSE_COUNTER is

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- inputs
signal sig_data    : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_load    : std_logic;

-- outputs
signal sig_zero_impulse  : std_logic;

-- data multiplexer
signal mux_data_out      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal mux_data_sel      : std_logic;

-- the delay register
signal reg_delay         : std_logic_vector(DATA_WIDTH-1 downto 0);
signal reg_delay_in      : std_logic_vector(DATA_WIDTH-1 downto 0);

-- the decrement
signal sig_data_decremented  : std_logic_vector(DATA_WIDTH-1 downto 0);

-- the delay comparer
signal cmp_delay_zero_out    : std_logic;

-- the validity register
signal reg_valid       : std_logic;
signal reg_valid_set   : std_logic;
signal reg_valid_clr   : std_logic;

-- ==========================================================================
--                           ARCHITECTURE BODY
-- ==========================================================================
begin

   -- mapping inputs
   sig_data <= DATA;
   sig_load <= LOAD;

   --
   mux_data_sel <= sig_load;

   -- the data multiplexer
   mux_data_p: process(mux_data_sel, sig_data, reg_delay)
   begin
      mux_data_out <= sig_data;

      case (mux_data_sel) is
         when '0'    => mux_data_out <= sig_data;
         when '1'    => mux_data_out <= reg_delay;
         when others => null;
      end case;
   end process;

   -- the decrement
   sig_data_decremented <= mux_data_out - 1;

   --
   reg_delay_in <= sig_data_decremented;

   -- the register for the delay
   reg_delay_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         reg_delay <= reg_delay_in;
      end if;
   end process;

   -- the comparer
   cmp_delay_zero_p: process(reg_delay)
   begin
      cmp_delay_zero_out <= '0';

      if (reg_delay = 0) then
         cmp_delay_zero_out <= '1';
      end if;
   end process;

   --
   reg_valid_set <= sig_load;
   reg_valid_clr <= cmp_delay_zero_out;

   -- the validity register
   reg_valid_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_valid <= '0';
         elsif (reg_valid_set = '1') then
            reg_valid <= '1';
         elsif (reg_valid_clr = '1') then
            reg_valid <= '0';
         end if;
      end if;
   end process;

   sig_zero_impulse <= cmp_delay_zero_out AND reg_valid;

   -- mapping outputs
   ZERO_IMPULSE <= sig_zero_impulse;


end architecture;

