--  ---------------------------------------------------------
--  Hardware accelerated Functional Verification of Processor
--  ---------------------------------------------------------

--  \file   halt_monitor.vhd
--  \date   10-04-2013
--  \brief  Halt monitor monitors port_halt for detection of halt instruction
--          after detection of halt instruction holds processor in reset
--          and propagate information about halt instruction to other monitors

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity HALT_MONITOR is port
   (
      CLK       : in  std_logic;
      RESET     : in  std_logic;

      -- detection of halt instruction
      port_halt : in std_logic;

      -- program driver done
      DRIVER_DONE : in std_logic;

      -- HALT propagation
      HALT      : out std_logic;

      -- Codix reset
      RST_n     : out std_logic

   );
   
end entity;

-- ----------------------------------------------------------
--                 architecture
-- ----------------------------------------------------------
architecture arch of HALT_MONITOR is

-- ----------------------------------------------------------
--                 FSM states
-- ----------------------------------------------------------
type state_type is (input_state, computation_state, output_state);

-- FSM signals
signal state_reg, state_next : state_type;

signal is_input, is_computing, is_output : std_logic;

begin

   -- state logic
   fsm_state_logic : process (CLK)
   begin
     if CLK='1' and CLK'event then
        if RESET='1' then
          state_reg <= input_state;
        else
          state_reg <= state_next;
        end if;   
     end if;   
   end process;

   -- next state logic
   fsm_next_state_logic : process (port_halt, DRIVER_DONE)
   begin

     state_next <= state_reg;

     case state_reg is
        
        -- init state
        when input_state =>
--          RST_n <= '0';
--          HALT  <= '0';

          if DRIVER_DONE = '1' then
             state_next <= computation_state;
          else
             state_next <= input_state;
          end if;

        when computation_state =>
--          RST_n <= '1';
--          HALT  <= '0';

          if port_halt = '1' then
             state_next <= output_state;
          else
             state_next <= computation_state;
          end if;

        when output_state =>
--          RST_n <= '0';
--          HALT  <= '1';

          if DRIVER_DONE = '0' then
             state_next <= input_state;
          else
             state_next <= output_state;
          end if;

     end case;
  end process;

  -- Moore output logic
  moore_output : process (state_reg)
  begin
     -- default values
     is_input     <= '0';
     is_computing <= '0'; 
     is_output    <= '0';
      
     case state_reg is
        when input_state       => is_input     <= '1';
        when computation_state => is_computing <= '1';
        when output_state      => is_output    <= '1';
     end case;   
  end process moore_output;

  mux_output : process (is_input, is_computing, is_output)
  begin
     -- according to the priority !
     if (is_input = '1') then 
        RST_n <= '0';
        HALT  <= '0';
     elsif (is_computing = '1') then 
        RST_n <= '1';
        HALT  <= '0';
     elsif (is_output = '1') then 
        RST_n <= '0';
        HALT  <= '1';
     end if;
  end process;


--   process(RESET, port_halt, DRIVER_DONE)
--   begin
--      if DRIVER_DONE = '1' and port_halt = '0' then
--         RST_n <= '1';
--      else
--         RST_n <= '0';
--      end if;
--   end process;

end architecture;
