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
entity PORTOUT_MONITOR is
   generic
   (
      IN_DATA_WIDTH  : integer := 32;
      OUT_DATA_WIDTH : integer := 64
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      --           input interface - processor
      -- error detection? after halt?
      port_error     : in std_logic_vector(IN_DATA_WIDTH-1 downto 0);
      port_output    : in std_logic_vector(IN_DATA_WIDTH-1 downto 0);
      port_output_en : in std_logic;

      --           T - transmitter
      --           output frame link interface
      TX_DATA        : out std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(2 downto 0);
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic

   );
end entity;

-- ----------------------------------------------------------
--                 architecture
-- ----------------------------------------------------------
architecture arch of PORTOUT_MONITOR is

-- ----------------------------------------------------------
--                 FSM states
-- ----------------------------------------------------------
type state_type is (init_state, error_state, output_state, stop_state, wait_state);

-- ----------------------------------------------------------
--                 constants
-- ----------------------------------------------------------
constant DATA_TYPE   :  std_logic_vector(7 downto 0) := X"00";
constant START_TYPE  :  std_logic_vector(7 downto 0) := X"01";
constant STOP_TYPE   :  std_logic_vector(7 downto 0) := X"04";

-- ----------------------------------------------------------
--                 signals
-- ----------------------------------------------------------

-- FSM signals
signal state_reg, state_next : state_type;

-- input control
signal sig_portout    : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal sig_error      : std_logic_vector(IN_DATA_WIDTH-1 downto 0);

-- output control
signal sig_tx_data    : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal sig_tx_rem     : std_logic_vector(2 downto 0);
signal sig_tx_src_rdy_n : std_logic;
signal sig_tx_dst_rdy_n : std_logic; -- input
signal sig_tx_sop_n   : std_logic;
signal sig_tx_eop_n   : std_logic;
signal sig_tx_sof_n   : std_logic;
signal sig_tx_eof_n   : std_logic;


-- ----------------------------------------------------------
--                 architecture body
-- ----------------------------------------------------------
begin

   -- state logic
   fsm_state_logic : process (CLK)
   begin
     if CLK='1' and CLK'event then
        if RESET='1' then
          state_reg <= init_state;
        else
          state_reg <= state_next;
        end if;   
     end if;   
   end process;

   -- next state logic
   fsm_next_state_logic : process (state_reg, port_output_en, TX_DST_RDY_N)
   begin


     state_next <= state_reg;

     sig_tx_src_rdy_n <= '0';       -- source ready

     case state_reg is
        
        -- init state
        when init_state =>

          if port_output_en = '1' then
            state_next <= output_state;
--          elsif ?? then
--            state_next <= error_state;
          else
            state_next <= init_state;
          end if;

        -- data transfer - portout
        when output_state =>

          -- output data - portout
          sig_tx_data(31 downto 0) <= sig_portout;

          if sig_tx_dst_rdy_n = '1' then
            state_next <= wait_state;
          else
            state_next <= init_state;
          end if;

--          if ?? then
--            state_next <= stop_state;
--          end if;

        -- wait for destination ready signal
        when wait_state =>
          if sig_tx_dst_rdy_n = '1' then
            state_next <= wait_state;
          else
            state_next <= output_state;
          end if;

        when stop_state =>
          state_next <= stop_state;

        when error_state =>
          state_next <= error_state;

     end case;
  end process;
  
  -- input processing
  sig_tx_dst_rdy_n <= TX_DST_RDY_N;
  sig_portout      <= port_output;
  sig_error        <= port_error;

  -- output processing
  TX_DATA <= sig_tx_data;
  TX_REM  <= sig_tx_rem;
  TX_SRC_RDY_N <= sig_tx_src_rdy_n;
  TX_SOP_N <= sig_tx_sop_n;
  TX_EOP_N <= sig_tx_eop_n;
  TX_SOF_N <= sig_tx_sof_n;
  TX_EOF_N <= sig_tx_eof_n;


end architecture;
