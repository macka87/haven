--  ---------------------------------------------------------
--  Hardware accelerated Functional Verification of Processor
--  ---------------------------------------------------------

--  \file   program_driver.vhd
--  \date   27-03-2013
--  \brief  Program driver transform data received from SW part
--          and resends it to processor interface

--          processor (Codix) interface    - haven/codix/vhdl/codix_ca_t.vhd
--                                           haven/codix/fve/ifc.sv
--          frame link interface (example) - haven/combov2/comp/hw_ver/fl_hw_driver/fl_driver_ctrl/fl_driver_ctrl.vhd

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
      dbg_mode_mem   : out std_logic;
      --dbg_mode_mem_D0   : in std_logic_vector(31 downto 0);
      --dbg_mode_mem_Q0   : out std_logic_vector(31 downto 0);
      --dbg_mode_mem_RA0  : in std_logic_vector(18 downto 0);
      --dbg_mode_mem_RE0  : in std_logic;
      --dbg_mode_mem_RSC0 : in std_logic_vector(2 downto 0);
      --dbg_mode_mem_RSI0 : in std_logic_vector(1 downto 0);

      --           memory interface
      -- data 32b width
      --FR0       : out std_logic_vector(2 downto 0);
      --FR1       : out std_logic_vector(2 downto 0);
      --FW0       : out std_logic_vector(2 downto 0);
      --RR0       : out std_logic_vector(2 downto 0);
      --RR1       : out std_logic_vector(2 downto 0);
      --RW0       : out std_logic_vector(2 downto 0);

      -- halt instruction detection
      HALT      : in std_logic;

      -- two ports - memory read
      Q0        : in  std_logic_vector(IN_DATA_WIDTH-1 downto 0);
      Q1        : in  std_logic_vector(IN_DATA_WIDTH-1 downto 0);
      -- address
      RA0       : out std_logic_vector(18 downto 0);
      RA1       : out std_logic_vector(18 downto 0);
      -- read enable
      RE0       : out std_logic;
      RE1       : out std_logic;
      -- read subblock count
      RSC0      : out std_logic_vector(2 downto 0);
      RSC1      : out std_logic_vector(2 downto 0);
      -- read subblock index
      RSI0      : out std_logic_vector(1 downto 0);
      RSI1      : out std_logic_vector(1 downto 0);

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
type state_type is (init_state, transfer_state, stop_state, wait_state);

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

-- address counter active
signal sig_cnt_act   : std_logic;
-- address counter register
signal sig_cnt_addr0 : std_logic_vector(18 downto 0);
signal sig_cnt_addr1 : std_logic_vector(18 downto 0);

-- input control
signal sig_dbg_mode  : std_logic;
signal sig_re0       : std_logic;
signal sig_re1       : std_logic;
signal sig_rsc0      : std_logic_vector(2 downto 0);
signal sig_rsc1      : std_logic_vector(2 downto 0);
signal sig_rsi0      : std_logic_vector(1 downto 0);
signal sig_rsi1      : std_logic_vector(1 downto 0);
signal sig_qdata0    : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal sig_qdata1    : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal sig_qdata_tmp : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);

-- output control
signal sig_tx_data   : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal sig_tx_rem    : std_logic_vector(2 downto 0);
signal sig_tx_src_rdy_n : std_logic;
signal sig_tx_dst_rdy_n : std_logic; -- input
signal sig_tx_sop_n  : std_logic;
signal sig_tx_eop_n  : std_logic;
signal sig_tx_sof_n  : std_logic;
signal sig_tx_eof_n  : std_logic;

-- ----------------------------------------------------------
--                 architecture body
-- ----------------------------------------------------------
begin

   -- address counter
   address_counter : process (CLK, RESET)
   begin
      if CLK='1' and CLK'event then
         if RESET='1' then
            sig_cnt_addr0 <= (others=>'0');
            sig_cnt_addr1 <= std_logic_vector(to_unsigned(4, sig_cnt_addr1'length));

         elsif sig_cnt_act = '1' then
            sig_cnt_addr0 <= sig_cnt_addr0 + 8;
            sig_cnt_addr1 <= sig_cnt_addr1 + 8;
         end if; 
      end if;
   end process;

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
   fsm_next_state_logic : process (state_reg, Q0, Q1, HALT, TX_DST_RDY_N)
   begin


     state_next         <= state_reg;

     sig_cnt_act        <= '0';

     sig_dbg_mode    <= '1';        -- memory debug mode port
     sig_re0         <= '0';        -- read enable
     sig_re1         <= '0';
     sig_rsc0        <= "100";      -- subblock count - 4
     sig_rsc1        <= "100";
     sig_rsi0        <= "00";       -- subblock index
     sig_rsi1        <= "00";

     sig_tx_src_rdy_n <= '0';       -- source ready

     case state_reg is
        
        -- init state
        when init_state =>

          if HALT = '1' then
            state_next <= transfer_state;
          else
            state_next <= init_state;
          end if;

        -- data transfer - read memory and send to SW
        when transfer_state =>

          -- enable address counter
          sig_cnt_act       <= '1';
          
          -- output data = Q1 + Q2
          sig_tx_data <= sig_qdata_tmp;

          -- continue with data transfer
          state_next <= transfer_state;

          if sig_tx_dst_rdy_n = '1' then
            state_next <= wait_state;
          end if;

--          if sig_end_flag = '1' then
--            state_next <= stop_state;
--          end if;

        -- wait for destination ready signal
        when wait_state =>
          if sig_tx_dst_rdy_n = '1' then
            state_next <= wait_state;
          else
            state_next <= transfer_state;
          end if;

        when stop_state =>
          state_next <= stop_state;

     end case;
  end process;
  
  -- input processing
  sig_qdata0 <= Q0;
  sig_qdata1 <= Q1;
  sig_tx_dst_rdy_n <= TX_DST_RDY_N;

  -- output processing
  sig_qdata_tmp <= sig_qdata0 & sig_qdata1;

  dbg_mode_mem <= sig_dbg_mode;
  RA0 <= sig_cnt_addr0;
  RA1 <= sig_cnt_addr1;
  RE0 <= sig_re0;
  RE1 <= sig_re1;
  RSI0 <= sig_rsi0;
  RSI1 <= sig_rsi1;
  RSC0 <= sig_rsc0;
  RSC1 <= sig_rsc1;

  TX_DATA <= sig_tx_data;
  TX_REM  <= sig_tx_rem;
  TX_SRC_RDY_N <= sig_tx_src_rdy_n;
  TX_SOP_N <= sig_tx_sop_n;
  TX_EOP_N <= sig_tx_eop_n;
  TX_SOF_N <= sig_tx_sof_n;
  TX_EOF_N <= sig_tx_eof_n;


end architecture;
