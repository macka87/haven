--  ---------------------------------------------------------
--  Hardware accelerated Functional Verification of Processor
--  ---------------------------------------------------------

--  \file   portout_monitor.vhd
--  \date   15-04-2013
--  \brief  Portout monitor monitors output interface of processor
--          if portout_en signal is enabled 32b portout signal is
--          send to SW part of verification environment (header + data)

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
type state_type is (header_state, data_state, init_state);

-- ----------------------------------------------------------
--                 constants
-- ----------------------------------------------------------
constant DATA_TYPE   :  std_logic_vector(7 downto 0) := X"00";
constant ENDPOINT_ID :  std_logic_vector(7 downto 0) := X"11"; --??
constant PROTOCOL_ID :  std_logic_vector(7 downto 0) := X"22"; --??

--constant START_TYPE  :  std_logic_vector(7 downto 0) := X"01";

-- ----------------------------------------------------------
--                 signals
-- ----------------------------------------------------------

-- FSM signals
signal state_reg, state_next : state_type;

-- output control
signal sig_tx_data    : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal sig_tx_rem     : std_logic_vector(2 downto 0);
signal sig_tx_src_rdy_n : std_logic;
signal sig_tx_dst_rdy_n : std_logic; -- input
signal sig_tx_sop_n   : std_logic;
signal sig_tx_eop_n   : std_logic;
signal sig_tx_sof_n   : std_logic;
signal sig_tx_eof_n   : std_logic;

-- internals
signal header_data    : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal header_rem     : std_logic_vector(2 downto 0);

-- ----------------------------------------------------------
--                 architecture body
-- ----------------------------------------------------------
begin

   -- header
   header_data(63 downto 56) <= X"00";
   header_data(55 downto 48) <= X"00"; --?? tx_header_fifo_data
   header_data(47 downto 40) <= X"00";
   header_data(39 downto 32) <= DATA_TYPE;
   header_data(31 downto 24) <= X"00";
   header_data(23 downto 16) <= X"00";
   header_data(15 downto  8) <= PROTOCOL_ID;
   header_data( 7 downto  0) <= ENDPOINT_ID;
   header_rem  <= (others => '1');


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
   fsm_next_state_logic : process (state_reg, port_output_en, sig_tx_dst_rdy_n, header_data, port_output)
   begin


     state_next <= state_reg;

     sig_tx_src_rdy_n <= '1';       -- source not ready

     sig_tx_data  <= X"0000000000000000";
     sig_tx_rem   <= "000";
     sig_tx_eof_n <= '1';
     sig_tx_eop_n <= '1';
     sig_tx_sof_n <= '1';
     sig_tx_sop_n <= '1';

    -- TODO default values??

     case state_reg is
        
        -- init state
        when init_state =>

          if port_output_en = '1' then
            state_next <= header_state;
          else
            state_next <= init_state;
          end if;

        -- data header transfer
        when header_state =>

          -- destination not ready
          if sig_tx_dst_rdy_n = '1' then
            state_next <= header_state;

          -- destination ready
          else 
            -- header & SOF & SOP & source ready
            sig_tx_data <= header_data;
            sig_tx_rem  <= header_rem;
            sig_tx_sof_n<= '0';
            sig_tx_sop_n<= '0';
            sig_tx_eof_n<= '1';
            sig_tx_eop_n<= '1';
            sig_tx_src_rdy_n<= '0';

            state_next <= data_state;
          end if;

        -- data transaction transfer
        when data_state =>
          
          -- destination not ready
          if sig_tx_dst_rdy_n = '1' then
            state_next <= data_state;

          -- destination ready
          else 
            -- header & EOF & EOP & source ready
            sig_tx_data <= port_output & X"00000000";
            sig_tx_rem  <= header_rem;
            sig_tx_sof_n<= '0';
            sig_tx_sop_n<= '0';
            sig_tx_eof_n<= '1';
            sig_tx_eop_n<= '1';
            sig_tx_src_rdy_n<= '0';

            state_next <= init_state;
          end if;
         
     end case;
  end process;
  
  -- input processing
  sig_tx_dst_rdy_n <= TX_DST_RDY_N;

  -- output processing
  TX_DATA <= sig_tx_data;
  TX_REM  <= sig_tx_rem;
  TX_SRC_RDY_N <= sig_tx_src_rdy_n;
  TX_SOP_N <= sig_tx_sop_n;
  TX_EOP_N <= sig_tx_eop_n;
  TX_SOF_N <= sig_tx_sof_n;
  TX_EOF_N <= sig_tx_eof_n;


end architecture;
