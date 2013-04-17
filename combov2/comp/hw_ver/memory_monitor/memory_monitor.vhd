--  ---------------------------------------------------------
--  Hardware accelerated Functional Verification of Processor
--  ---------------------------------------------------------

--  \file   memory_monitor.vhd
--  \date   10-04-2013
--  \brief  Memory monitor is activated by halt signal, then reads
--          memory of processor through its interface and sends
--          content of memory to SW part of verification environment

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.numeric_std.all;

--use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity MEMORY_MONITOR is

   generic
   (
      IN_DATA_WIDTH  : integer := 32;
      OUT_DATA_WIDTH : integer := 64
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      
      --           input interface - codix - memory read
      --           dbg_mode_mem_* ports
      dbg_mode_mem      : out std_logic;
      dbg_mode_mem_Q0   : in std_logic_vector(31 downto 0); -- data
      dbg_mode_mem_RA0  : out std_logic_vector(18 downto 0);  -- address 19b
      dbg_mode_mem_RE0  : out std_logic;                      -- read enable
      dbg_mode_mem_RSC0 : out std_logic_vector(2 downto 0);   -- subblock count
      dbg_mode_mem_RSI0 : out std_logic_vector(1 downto 0);   -- subblock index

      -- halt instruction detection
      HALT      : in std_logic;

      --           T - transmitter
      --           output frame link interface
      TX_DATA   : out std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      TX_REM    : out std_logic_vector(2 downto 0);
      TX_SRC_RDY_N : out std_logic;
      TX_DST_RDY_N : in  std_logic;
      TX_SOP_N  : out std_logic;
      TX_EOP_N  : out std_logic;
      TX_SOF_N  : out std_logic;
      TX_EOF_N  : out std_logic

   );
   
end entity;

-- ----------------------------------------------------------
--                 architecture
-- ----------------------------------------------------------
architecture arch of MEMORY_MONITOR is

-- ----------------------------------------------------------
--                 FSM states
-- ----------------------------------------------------------
type state_type is (init_state, read_1half, read_2half);

-- ----------------------------------------------------------
--                 constants
-- ----------------------------------------------------------
constant DATA_TYPE   :  std_logic_vector(7 downto 0) := X"00";
constant START_TYPE  :  std_logic_vector(7 downto 0) := X"01";
constant STOP_TYPE   :  std_logic_vector(7 downto 0) := X"04";

constant MAX_ADDRESS :  std_logic_vector(18 downto 0) := (others => '1');

constant ENDPOINT_ID :  std_logic_vector(7 downto 0) := X"11"; --??
constant PROTOCOL_ID :  std_logic_vector(7 downto 0) := X"22"; --??

-- ----------------------------------------------------------
--                 signals
-- ----------------------------------------------------------

-- FSM signals
signal state_reg, state_next : state_type;

-- address counter register
signal cnt_addr : std_logic_vector(18 downto 0);

-- input control
signal sig_dbg_mode  : std_logic;
signal sig_re0       : std_logic;
signal sig_rsc0      : std_logic_vector(2 downto 0);
signal sig_rsi0      : std_logic_vector(1 downto 0);
signal sig_qdata1    : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal sig_qdata2    : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal data_reg      : std_logic_vector(IN_DATA_WIDTH-1 downto 0);

-- output control
signal sig_tx_data   : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal sig_tx_rem    : std_logic_vector(2 downto 0);
signal sig_tx_src_rdy_n : std_logic;
signal sig_tx_dst_rdy_n : std_logic; -- input
signal sig_tx_sop_n  : std_logic;
signal sig_tx_eop_n  : std_logic;
signal sig_tx_sof_n  : std_logic;
signal sig_tx_eof_n  : std_logic;

signal header_data    : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);


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
   fsm_next_state_logic : process (state_reg, dbg_mode_mem_Q0, HALT, TX_DST_RDY_N)
   begin

     state_next         <= state_reg;

     sig_dbg_mode    <= '1';        -- memory debug mode port
     sig_re0         <= '0';        -- read enable
     sig_rsc0        <= "100";      -- subblock count - 4
     sig_rsi0        <= "00";       -- subblock index

     -- TODO: initialize sig_tx_*

     sig_tx_src_rdy_n <= '1';       -- source not ready

     case state_reg is
        
        -- init state
        when init_state =>

          -- initialize address
          cnt_addr <= (others => '0');

          if HALT = '1' and TX_DST_RDY_N = '1' then

            -- header & SOF & SOP & source ready
            sig_tx_data <= header_data;
            sig_tx_rem  <= "111";
            sig_tx_sof_n<= '0';
            sig_tx_sop_n<= '0';
            sig_tx_eof_n<= '1';
            sig_tx_eop_n<= '1';
            sig_tx_src_rdy_n<= '0';

            -- read enable
            sig_re0 <= '1';

            state_next <= read_1half;

          else
            state_next <= init_state;
          end if;

        -- data transfer - read first half (32b) from memory
        when read_1half =>

          -- read enable
          sig_re0 <= '1';

          -- increment address
          cnt_addr <= cnt_addr + 4;

          -- read data
          sig_qdata1 <= data_reg;

          -- end of memory address space
          if cnt_addr >= MAX_ADDRESS then
            sig_tx_data      <= sig_qdata1 & X"00000000";
            sig_tx_eop_n     <= '0';
            sig_tx_eof_n     <= '0';
            sig_tx_src_rdy_n <= '0';
            sig_tx_rem       <= "011";

            state_next <= init_state;

          -- continue with reading
          else

            state_next <= read_2half;

          end if;

        when read_2half =>

          -- increment address
          cnt_addr <= cnt_addr + 4;

          -- read data
          sig_qdata2 <= data_reg;

          -- write data 1half + 2half
          sig_tx_data <= sig_qdata1 & sig_qdata2;

          -- end of memory address space
          if cnt_addr >= MAX_ADDRESS then

            -- read enable
            sig_re0 <= '1';

            sig_tx_eop_n     <= '0';
            sig_tx_eof_n     <= '0';
            sig_tx_src_rdy_n <= '0';
            sig_tx_rem       <= "111";
            state_next <= init_state;

          -- continue with reading
          else
            -- read enable
            sig_re0 <= '1';

            state_next <= read_1half;
          end if;

     end case;
  end process;
  
  -- input processing
  sig_tx_dst_rdy_n <= TX_DST_RDY_N;
  data_reg <= dbg_mode_mem_Q0;

  -- output processing

  dbg_mode_mem      <= sig_dbg_mode;
  dbg_mode_mem_RA0  <= cnt_addr;
  dbg_mode_mem_RE0  <= sig_re0;
  dbg_mode_mem_RSI0 <= sig_rsi0;
  dbg_mode_mem_RSC0 <= sig_rsc0;

  TX_DATA      <= sig_tx_data;
  TX_REM       <= sig_tx_rem;
  TX_SRC_RDY_N <= sig_tx_src_rdy_n;
  TX_SOP_N     <= sig_tx_sop_n;
  TX_EOP_N     <= sig_tx_eop_n;
  TX_SOF_N     <= sig_tx_sof_n;
  TX_EOF_N     <= sig_tx_eof_n;


end architecture;
