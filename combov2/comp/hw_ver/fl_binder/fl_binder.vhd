--  ---------------------------------------------------------
--  Hardware accelerated Functional Verification of Processor
--  ---------------------------------------------------------

--  \file   fl_binder.vhd
--  \date   22-04-2013
--  \brief  fl_binder merges framelink interface signals from memory
--          monitor, portout monitor and register file monitor.
--          Output of binder is connected to SW part of verification environment

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.numeric_std.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity FL_BINDER is

   generic
   (
      -- framelink data width
      DATA_WIDTH  : integer := 64
   );

   port
   (
      CLK          : in  std_logic;
      RESET        : in  std_logic;

      -- halt instruction detection and control signals
      HALT         : in  std_logic;
      MEM_DONE     : in  std_logic;
      REGS_DONE    : in  std_logic;
 
      -- RX (R -> receiver)
      -- input framelink - PM - portout monitor
      PM_RX_DATA   : in std_logic_vector(DATA_WIDTH-1 downto 0);
      PM_RX_REM    : in std_logic_vector(2 downto 0);
      PM_RX_SRC_RDY_N : in std_logic;
      PM_RX_DST_RDY_N : out std_logic;
      PM_RX_SOP_N  : in std_logic;
      PM_RX_EOP_N  : in std_logic;
      PM_RX_SOF_N  : in std_logic;
      PM_RX_EOF_N  : in std_logic;

      -- input framelink - RM - register file monitor
      RM_RX_DATA   : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RM_RX_REM    : in std_logic_vector(2 downto 0);
      RM_RX_SRC_RDY_N : in std_logic;
      RM_RX_DST_RDY_N : out std_logic;
      RM_RX_SOP_N  : in std_logic;
      RM_RX_EOP_N  : in std_logic;
      RM_RX_SOF_N  : in std_logic;
      RM_RX_EOF_N  : in std_logic;

      -- input framelink - MM - memory monitor
      MM_RX_DATA   : in std_logic_vector(DATA_WIDTH-1 downto 0);
      MM_RX_REM    : in std_logic_vector(2 downto 0);
      MM_RX_SRC_RDY_N : in std_logic;
      MM_RX_DST_RDY_N : out std_logic;
      MM_RX_SOP_N  : in std_logic;
      MM_RX_EOP_N  : in std_logic;
      MM_RX_SOF_N  : in std_logic;
      MM_RX_EOF_N  : in std_logic;

     
      -- output frame link interface (T -> transmitter)
      TX_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM       : out std_logic_vector(2 downto 0);
      TX_SRC_RDY_N : out std_logic;
      TX_DST_RDY_N : in  std_logic;
      TX_SOP_N     : out std_logic;
      TX_EOP_N     : out std_logic;
      TX_SOF_N     : out std_logic;
      TX_EOF_N     : out std_logic

   );
   
end entity;

-- ----------------------------------------------------------
--                 architecture
-- ----------------------------------------------------------
architecture arch of FL_BINDER is

-- ----------------------------------------------------------
--                 constants
-- ----------------------------------------------------------
constant PORTOUT_MONITOR_IDX  : integer := 0;
constant REGISTER_MONITOR_IDX : integer := 1;
constant MEMORY_MONITOR_IDX   : integer := 2;

-- ----------------------------------------------------------
--                 FSM states
-- ----------------------------------------------------------
type state_type is (state_portout, state_regs, state_mem);

-- ----------------------------------------------------------
--                 signals
-- ----------------------------------------------------------

-- FSM signals
signal state_reg, state_next : state_type;

-- ----------------------------------------------------------
--                 architecture body
-- ----------------------------------------------------------
begin

   -- state logic
   fsm_state_logic : process (CLK)
   begin
     if CLK='1' and CLK'event then
        if RESET='1' then
          state_reg <= state_portout;
        else
          state_reg <= state_next;
        end if;
     end if; 
   end process;

   -- next state logic
   fsm_next_state_logic : process (state_reg, HALT, MEM_DONE, REGS_DONE, PM_RX_SRC_RDY_N, 
                                   RM_RX_SRC_RDY_N, MM_RX_SRC_RDY_N, TX_DST_RDY_N,PM_RX_DATA,
                                   RM_RX_DATA, MM_RX_DATA, PM_RX_REM, PM_RX_SOP_N, PM_RX_SOF_N, 
                                   PM_RX_EOP_N, PM_RX_EOF_N, RM_RX_REM, RM_RX_SOP_N, RM_RX_SOF_N, 
                                   RM_RX_EOP_N, RM_RX_EOF_N, MM_RX_REM, MM_RX_SOP_N, MM_RX_SOF_N, 
                                   MM_RX_EOP_N, MM_RX_EOF_N)
   begin

     state_next <= state_reg;

     PM_RX_DST_RDY_N <= '0';
     RM_RX_DST_RDY_N <= '0';
     MM_RX_DST_RDY_N <= '0';

     case state_reg is
        
        -- transfer of portout data
        when state_portout =>

          -- src and dst signals connection
          PM_RX_DST_RDY_N <= TX_DST_RDY_N;

          -- next state based on control signals
          if HALT = '1' then
            TX_SRC_RDY_N <= '1';
            state_next <= state_regs;
          else
            TX_SRC_RDY_N <= PM_RX_SRC_RDY_N;
            state_next <= state_portout;
          end if;

          -- source and destination ready
          if PM_RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' then
 
            -- connect portout monitor to output interface
            TX_DATA      <= PM_RX_DATA;
            TX_REM       <= PM_RX_REM;
            TX_SOP_N     <= PM_RX_SOP_N;
            TX_SOF_N     <= PM_RX_SOF_N;
            TX_EOP_N     <= PM_RX_EOP_N;
            TX_EOF_N     <= PM_RX_EOF_N;

          end if;

        -- transfer of register file data
        when state_regs =>

          -- src and dst signals connection
          TX_SRC_RDY_N <= RM_RX_SRC_RDY_N;
          RM_RX_DST_RDY_N <= TX_DST_RDY_N;

          -- next state based on control signals
          if REGS_DONE = '1' then
            state_next <= state_mem;
          else
            state_next <= state_regs;
          end if;

          -- source and destination ready
          if RM_RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' then

            --report "in state regs at time " & time'image(now);

            -- connect portout monitor to output interface
            TX_DATA      <= RM_RX_DATA;
            TX_REM       <= RM_RX_REM;
            TX_SOP_N     <= RM_RX_SOP_N;
            TX_SOF_N     <= RM_RX_SOF_N;
            TX_EOP_N     <= RM_RX_EOP_N;
            TX_EOF_N     <= RM_RX_EOF_N;

          end if;

        -- transfer of memory data
        when state_mem =>

          -- src and dst signals connection
          TX_SRC_RDY_N <= MM_RX_SRC_RDY_N;
          MM_RX_DST_RDY_N <= TX_DST_RDY_N;

          -- next state based on control signals
          if MEM_DONE = '1' then
            state_next <= state_portout;
          else
            state_next <= state_mem;
          end if;

          -- source and destination ready
          if MM_RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' then
  
            -- connect portout monitor to output interface
            TX_DATA      <= MM_RX_DATA;
            TX_REM       <= MM_RX_REM;
            TX_SOP_N     <= MM_RX_SOP_N;
            TX_SOF_N     <= MM_RX_SOF_N;
            TX_EOP_N     <= MM_RX_EOP_N;
            TX_EOF_N     <= MM_RX_EOF_N;

          end if;
      

     end case;
  end process;

  -- Moore output logic
--  moore_output : process (state_reg)
--  begin
     -- default values
--     transfer_portout   <= '0';
--     transfer_registers <= '0';
--     transfer_memory    <= '0';   
--     case state_reg is
--        when state_portout => transfer_portout   <= '1';
--        when state_regs    => transfer_registers <= '1';
--        when state_mem     => transfer_memory    <= '1';
--     end case;   
--  end process moore_output;

  -- output mapping
--  output_processing : process(CLK)
--  begin
--        if(transfer_portout = '1') then
--        elsif(transfer_registers = '1') then
--        elsif(transfer_memory = '1') then
--        end if;
--  end process;

end architecture;
