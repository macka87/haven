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

--use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity PROGRAM_DRIVER is

   generic
   (
      IN_DATA_WIDTH  : integer := 64;
      OUT_DATA_WIDTH : integer := 32
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      --           R - receiver, T - transmitter
      --           input frame link interface
      RX_DATA        : in  std_logic_vector(IN_DATA_WIDTH-1 downto 0);
--      RX_REM         : in  std_logic_vector(log2(IN_DATA_WIDTH/8)-1 downto 0);
      RX_REM         : in  std_logic_vector(2 downto 0);

      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      
      --           output interface - codix - memory write
      --           dbg_mode_mem_* ports
      dbg_mode_mem      : out std_logic;
      --dbg_mode_mem_D0   : in std_logic_vector(31 downto 0);
      --dbg_mode_mem_Q0   : out std_logic_vector(31 downto 0);
      --dbg_mode_mem_RA0  : in std_logic_vector(18 downto 0);
      --dbg_mode_mem_RE0  : in std_logic;
      --dbg_mode_mem_RSC0 : in std_logic_vector(2 downto 0);
      --dbg_mode_mem_RSI0 : in std_logic_vector(1 downto 0);
      --dbg_mode_mem_WA0  : in std_logic_vector(18 downto 0);
      --dbg_mode_mem_WE0  : in std_logic;
      --dbg_mode_mem_WSC0 : in std_logic_vector(2 downto 0);
      --dbg_mode_mem_WSI0 : in std_logic_vector(1 downto 0);

      --           memory interface
      -- data 32b width
      D0   : out std_logic_vector(31 downto 0);
      --FR0  : out std_logic_vector(2 downto 0);
      --FR1  : out std_logic_vector(2 downto 0);
      --FW0  : out std_logic_vector(2 downto 0);
      --Q0   : out std_logic_vector(31 downto 0);
      --Q1   : out std_logic_vector(31 downto 0);
      --RA0  : in std_logic_vector(18 downto 0);
      --RA1  : in std_logic_vector(18 downto 0);
      --RE0  : in std_logic;
      --RE1  : in std_logic;
      --RR0  : out std_logic_vector(2 downto 0);
      --RR1  : out std_logic_vector(2 downto 0);
      --RSC0 : in std_logic_vector(2 downto 0);
      --RSC1 : in std_logic_vector(2 downto 0);
      --RSI0 : in std_logic_vector(1 downto 0);
      --RSI1 : in std_logic_vector(1 downto 0);
      --RW0  : out std_logic_vector(2 downto 0);
      -- address
      WA0  : out std_logic_vector(18 downto 0);
       -- write enable
      WE0  : out std_logic;
      -- write subblock count
      WSC0 : out std_logic_vector(2 downto 0);
      -- write subblock index
      WSI0 : out std_logic_vector(1 downto 0)

   );
   
end entity;

-- ----------------------------------------------------------
--                 architecture
-- ----------------------------------------------------------
architecture arch of PROGRAM_DRIVER is

-- ----------------------------------------------------------
--                 FSM states
-- ----------------------------------------------------------
type state_type is (init_state, control_state, data_state, stop_state, transfer_state);

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
signal state_reg, state_next   : state_type;

-- trasaction type
signal sig_trans_type    : std_logic_vector(7 downto 0);

-- address counter active
signal sig_cnt_act       : std_logic;

-- address counter register
signal sig_cnt_addr      : std_logic_vector(18 downto 0);                 -- address 19b

-- output control
signal sig_out_dbg_mode  : std_logic;                                     -- debug mode memory
signal sig_out_we        : std_logic;                                     -- write enable
signal sig_out_sb_cnt    : std_logic_vector(2 downto 0);                  -- subblock count
signal sig_out_sb_idx    : std_logic_vector(1 downto 0);                  -- subblock index
signal sig_out_data_tmp  : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);   -- temporary data 32b
signal sig_out_data      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);   -- data out 32b

signal sig_out_dst_rdy_n : std_logic;

signal data_ready          : std_logic;

-- ----------------------------------------------------------
--                 architecture body
-- ----------------------------------------------------------
begin

   -- address counter
   address_counter : process (CLK, RESET)
   begin
      if CLK='1' and CLK'event then
         if RESET='1' then
            sig_cnt_addr <= (others=>'0');
         elsif sig_cnt_act = '1' then
            sig_cnt_addr <= sig_cnt_addr + 4;
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
   fsm_next_state_logic : process (state_reg, data_ready, RX_SOF_N,
                                   sig_trans_type, RX_EOF_N, RX_SRC_RDY_N)
   begin


     state_next         <= state_reg;   

     sig_cnt_act        <= '0';

     sig_out_dbg_mode   <= '1';        -- memory debug mode port
     sig_out_we         <= '1';        -- write enable
     sig_out_sb_cnt     <= "100";      -- subblock count - 4
     sig_out_sb_idx     <= "00";       -- subblock index

     sig_out_dst_rdy_n  <= '0';        -- destination ready signal


     case state_reg is
        
        -- init state
        when init_state =>

          -- source and destination ready
          if data_ready = '1' then

            -- start of frame and start of part
            if ((RX_SOP_N nand RX_SOF_N) = '1') then
              -- data transaction              
              if sig_trans_type = DATA_TYPE then
                state_next <= data_state;
              -- stop state
              elsif sig_trans_type = STOP_TYPE then
                state_next <= stop_state;
              -- control transaction
              else
                state_next <= control_state;
              end if;
            end if;
          -- data not ready
          else 
            state_next <= init_state;
          end if;

        -- data transaction processing state
        when data_state =>

          -- destination not ready
          sig_out_dst_rdy_n <= '1';
          -- enable address counter
          sig_cnt_act       <= '1';

          -- end of frame
          if ((RX_EOP_N nand RX_EOF_N) = '1') then

            state_next <= init_state;
          -- send data to processor memory
          else
            -- first part of data - to D0 output
            sig_out_data <= RX_DATA(63 downto 32);
            -- second half of data - temporary register
            sig_out_data_tmp <= RX_DATA(31 downto 0);
            state_next <= transfer_state;
          end if;

        -- data trasaction transfer
        when transfer_state =>

          -- destination not ready
          sig_out_dst_rdy_n <= '1';
          -- enable address counter
          sig_cnt_act       <= '1';

          -- second part of data - to D0 output
          sig_out_data <= sig_out_data_tmp;
          state_next   <= init_state;

        -- control transactions
        when control_state =>
          -- end of frame
          if (RX_EOP_N nand RX_EOF_N) = '1' then
            state_next <= init_state; 
          else
            state_next <= control_state;
          end if;

        when stop_state =>
          state_next <= stop_state;

     end case;      
  end process;
  
  sig_trans_type <= RX_DATA(39 downto 32);
  RX_DST_RDY_N <= sig_out_dst_rdy_n;

  -- source and destination are ready TODO: nor|nand?
  data_ready   <= RX_SRC_RDY_N nor sig_out_dst_rdy_n;

  -- output processing
  dbg_mode_mem <= sig_out_dbg_mode;
  WE0          <= sig_out_we;
  WA0          <= sig_cnt_addr;
  WSC0         <= sig_out_sb_cnt;
  WSI0         <= sig_out_sb_idx;
  D0           <= sig_out_data;


end architecture;

