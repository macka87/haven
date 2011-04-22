--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Driver Controller
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
entity FL_DRIVER_CTRL is

   generic
   (
      -- data width
      DATA_WIDTH     : integer := 64;
      DELAY_WIDTH    : integer := 9
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input FrameLink interface
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      
      -- output delay interface
      TX_DELAY       : out std_logic_vector(DELAY_WIDTH-1 downto 0);
      TX_DELAY_WR_N  : out std_logic;
      TX_DELAY_RDY_N : in  std_logic;
      
      -- driver is disabled from software
      TX_FINISH      : out std_logic 
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of FL_DRIVER_CTRL is
-- ==========================================================================
--                                      TYPES
-- ==========================================================================
type state_type is (init_state, sof_state, sop_state, data_state, delay_state,
                    delay_rdy_state, wait_state, stop_state, counter_state);

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================
constant DATA_TYPE  :  std_logic_vector(7 downto 0) := X"00";
constant WAIT_TYPE  :  std_logic_vector(7 downto 0) := X"02";
constant DELAY_TYPE :  std_logic_vector(7 downto 0) := X"05";
constant STOP_TYPE  :  std_logic_vector(7 downto 0) := X"04";

constant REM_INDEX  : integer := 4+log2(DATA_WIDTH/8);
constant COMP_VALUE : std_logic_vector(DATA_WIDTH-1 downto 0) 
                      := conv_std_logic_vector(255, DATA_WIDTH);
                      
constant ZERO_VALUE : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0) 
                      := (others => '0');       

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================
-- FSM signals ---------------------------------------------------------------
signal state_reg, state_next   : state_type;
signal is_header, is_data, is_delay, is_delaying, is_stop, is_wait, is_cntr : std_logic;

signal sig_rx_dst_rdy_n    : std_logic;

signal sig_trans_type      : std_logic_vector(7 downto 0);
signal sig_reg_last        : std_logic; 
signal sig_new_last        : std_logic;
signal sig_new_compl       : std_logic;

-- data processing
signal sig_tx_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_tx_rem          : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal sig_tx_sof_n        : std_logic;
signal sig_tx_sop_n        : std_logic;
signal sig_tx_eof_n        : std_logic;
signal sig_tx_eop_n        : std_logic;
signal sig_tx_src_rdy_n    : std_logic;
signal sig_tx_dst_rdy_n    : std_logic;

signal sig_out_sof_n       : std_logic;
signal sig_out_sop_n       : std_logic;
signal sig_out_eof_n       : std_logic;
signal sig_out_eop_n       : std_logic; 

-- wait processing 
signal sig_difference      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_mux_counter     : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_counter_reg     : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_counter_is_zero : std_logic; 
signal sig_minimum         : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_minimum_final   : std_logic_vector(7 downto 0);
signal sig_wait            : std_logic_vector(8 downto 0);

-- delay processing
signal sig_delay           : std_logic_vector(8 downto 0);
signal sig_delay_wr_n      : std_logic;
signal sig_output_reg      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_rem_reg         : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal sig_eof_reg         : std_logic;
signal sig_incremented     : std_logic_vector(log2(DATA_WIDTH/8) downto 0);
signal sig_select          : std_logic_vector(log2(DATA_WIDTH/8) downto 0);
signal sig_mux_delay       : std_logic_vector(7 downto 0);
signal sig_set_boundary    : std_logic_vector(log2(DATA_WIDTH/8) downto 0);
signal sig_set_delay_rdy_n : std_logic;
signal sig_set_delay_rdy_n_final : std_logic;

signal data_ready          : std_logic;

-- ==========================================================================
--                           ARCHITECTURE BODY
-- ==========================================================================
begin
   -- state logic
   fsm_state_logic : process (CLK)
   begin
     if (rising_edge(CLK)) then
        if (RESET='1') then
          state_reg <= init_state;
        else
          state_reg <= state_next;
        end if;   
     end if;   
   end process;
   
   -- next state logic
   fsm_next_state_logic : process (state_reg, data_ready,
                                   sig_trans_type, sig_reg_last, RX_EOF_N,
                                   sig_counter_is_zero, sig_set_delay_rdy_n)
   begin
     state_next <= state_reg;  
     
     sig_out_sof_n <= '1';
     sig_out_sop_n <= '1'; 
     sig_out_eof_n <= '1';
     sig_out_eop_n <= '1';

     case state_reg is
        
        when init_state =>
          if (data_ready = '1') then
            -- read header
            sig_trans_type <= RX_DATA(39 downto 32);
            sig_new_compl  <= RX_DATA(57); 
            sig_new_last   <= RX_DATA(56);
          
            if (sig_trans_type = DATA_TYPE) then
              if (sig_reg_last = '1') then
                state_next <= sof_state;
              elsif (sig_reg_last = '0') then  
                state_next <= sop_state;
              end if;
            elsif (sig_trans_type = DELAY_TYPE) then
                state_next <= delay_state;  
            elsif (sig_trans_type = STOP_TYPE) then 
                state_next <= stop_state; 
            elsif (sig_trans_type = WAIT_TYPE) then
                state_next <= wait_state; 
            end if;
          else 
            state_next <= init_state;
          end if;                
        
        when sof_state => 
          if (data_ready = '1') then 
            if (RX_EOF_N = '0') then 
              state_next <= init_state;
              sig_out_sof_n <= '0';
              sig_out_sop_n <= '0'; 
              sig_out_eof_n <= not sig_reg_last;
              sig_out_eop_n <= '0';
            elsif (RX_EOF_N = '1') then   
              state_next <= data_state;
              sig_out_sof_n <= '0';
              sig_out_sop_n <= '0';
              sig_out_eof_n <= '1';
              sig_out_eop_n <= '1';
            end if;  
          else 
            state_next <= sof_state;  
          end if;
        
        when sop_state =>
          if (data_ready = '1') then 
            if (RX_EOF_N = '0') then 
              state_next <= init_state;
              sig_out_sof_n <= '1';
              sig_out_sop_n <= '0'; 
              sig_out_eof_n <= not sig_reg_last;
              sig_out_eop_n <= '0';
            elsif (RX_EOF_N = '1') then   
              state_next <= data_state;
              sig_out_sof_n <= '1';
              sig_out_sop_n <= '0';
              sig_out_eof_n <= '1';
              sig_out_eop_n <= '1';
            end if;
          else 
            state_next <= sop_state;     
          end if;
             
        when data_state =>
          if (data_ready = '1') then 
            if (RX_EOF_N = '0') then 
              state_next <= init_state;
              sig_out_sof_n <= '1';
              sig_out_sop_n <= '1'; 
              sig_out_eof_n <= not sig_reg_last;
              sig_out_eop_n <= '0';
            elsif (RX_EOF_N = '1') then   
              state_next <= data_state;
              sig_out_sof_n <= '1';
              sig_out_sop_n <= '1';
              sig_out_eof_n <= '1';
              sig_out_eop_n <= '1';
            end if;
          else 
            state_next <= data_state;      
          end if;
        
        when delay_state =>
          if (data_ready = '1') then
            state_next <= delay_rdy_state;
          else 
            state_next <= delay_state;        
          end if;
        
        when delay_rdy_state =>
          if (sig_set_delay_rdy_n = '0') then 
            state_next <= init_state;
          else 
            state_next <= delay_rdy_state;        
          end if;
          
        when stop_state =>
          state_next <= stop_state;
        
        when wait_state =>
          if (data_ready = '1' and RX_EOF_N = '0') then
            state_next <= counter_state; 
          else 
            state_next <= wait_state;    
          end if;  
          
        when counter_state =>
          if (sig_counter_is_zero = '1') then
            state_next <= init_state; 
          else 
            state_next <= counter_state;    
          end if; 
            
        end case;      
   end process;
   
   -- Moore output logic
   moore_output : process (state_reg)
   begin
      -- default values
      is_header    <= '0';
      is_data      <= '0';
      is_delay     <= '0'; 
      is_stop      <= '0';
      is_wait      <= '0'; 
      is_cntr      <= '0';
      is_delaying  <= '0';
      
      case state_reg is
         when init_state    => is_header <= '1';
         when sof_state     => is_data   <= '1';
         when sop_state     => is_data   <= '1';
         when data_state    => is_data   <= '1';
         when delay_state   => is_delay  <= '1';  
         when stop_state    => is_stop   <= '1';
         when wait_state    => is_wait   <= '1'; 
         when counter_state   => is_cntr      <= '1';
         when delay_rdy_state => is_delaying  <= '1';
      end case;   
   end process moore_output;
   
   -- register for fl_part_last value
   reg1 : process (CLK)
   begin
      if (RESET = '1') then 
         sig_reg_last <= '1';
      elsif (rising_edge(CLK)) then
         if (data_ready = '1') then
            sig_reg_last <= sig_new_last;   
         end if;   
      end if;
   end process;
   
   -- ================= DATA PROCESSING =====================================
   sig_tx_data      <= RX_DATA;
   sig_tx_rem       <= RX_REM;
   sig_tx_sof_n     <= sig_out_sof_n; 
   sig_tx_eof_n     <= sig_out_eof_n; 
   sig_tx_sop_n     <= sig_out_sop_n; 
   sig_tx_eop_n     <= sig_out_eop_n; 
   sig_tx_src_rdy_n <= not((not RX_SRC_RDY_N) and is_data);
   
   TX_DATA            <= sig_tx_data;
   TX_REM             <= sig_tx_rem;
   TX_SOF_N           <= sig_tx_sof_n;
   TX_EOF_N           <= sig_tx_eof_n;
   TX_SOP_N           <= sig_tx_sop_n;
   TX_EOP_N           <= sig_tx_eop_n;
   TX_SRC_RDY_N       <= sig_tx_src_rdy_n;
   sig_tx_dst_rdy_n   <= TX_DST_RDY_N;
   
   mux1 : process (is_header, is_data, is_delay, is_delaying,
      sig_set_delay_rdy_n, is_cntr, sig_tx_dst_rdy_n)
   begin
     if    (is_header = '1') then sig_rx_dst_rdy_n <= '0';
     elsif (is_data   = '1') then sig_rx_dst_rdy_n <= sig_tx_dst_rdy_n; 
     elsif (is_delaying = '1') then sig_rx_dst_rdy_n <= '1';  
     elsif (is_cntr   = '1') then sig_rx_dst_rdy_n <= '1'; 
     end if;
   end process;
  
   RX_DST_RDY_N <= sig_rx_dst_rdy_n;
   -- ================= WAIT PROCESSING =====================================
   mux2 : process (is_wait, sig_difference, RX_DATA)
   begin
      sig_mux_counter <= (others => '0');

      case is_wait is
         when '0'    => sig_mux_counter <= sig_difference;
         when '1'    => sig_mux_counter <= RX_DATA;
         when others => null;   
      end case;   
   end process;
   
   reg2 : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then 
            sig_counter_reg <= (others => '0');
         elsif (((is_wait or is_cntr) and (not TX_DELAY_RDY_N)) = '1') then
            sig_counter_reg <= sig_mux_counter;   
         end if;   
      end if;
   end process;
   
   comparator1 : process (sig_mux_counter)
   begin
      if (sig_mux_counter = ZERO_VALUE) then sig_counter_is_zero <= '1';
      else sig_counter_is_zero <= '0';
      end if;
   end process;
  
   minimum_extractor : process (sig_counter_reg)
   begin
      if (sig_counter_reg > COMP_VALUE) then 
        sig_minimum <= COMP_VALUE;
      else   
        sig_minimum <= sig_counter_reg;
      end if;  
   end process;
   
   sig_difference <= sig_counter_reg - sig_minimum;
   sig_minimum_final <= sig_minimum(7 downto 0); 
   sig_wait <= '1' & sig_minimum_final; 
   
   mux3 : process (is_delaying, is_wait, sig_wait, sig_delay)
   begin
     if (is_cntr  = '1')       then TX_DELAY <= sig_wait;
     elsif (is_delaying = '1') then TX_DELAY <= sig_delay;
     end if;
   end process;
   
   sig_delay_wr_n <= is_delaying nor is_cntr;
   TX_DELAY_WR_N <= sig_delay_wr_n;
   
   data_ready <= RX_SRC_RDY_N nor sig_rx_dst_rdy_n;

   -- ================= DELAY PROCESSING ====================================
   reg3 : process (CLK)
   begin
      if (RESET = '1') then 
         sig_output_reg <= (others => '0');
         sig_rem_reg    <= RX_REM; 
         sig_eof_reg    <= '0';
      elsif (rising_edge(CLK)) then
         if (data_ready = '1') then
            sig_output_reg <= RX_DATA;  
            sig_rem_reg    <= RX_REM; 
            sig_eof_reg    <= not RX_EOF_N;  
         end if;   
      end if;
   end process;
   
   sig_incremented <= sig_select + 1;
   
   reg4 : process (CLK)
   begin
      if (RESET = '1') then 
         sig_select <= (others => '0');
      elsif (rising_edge(CLK)) then
         if (data_ready = '1') then -- reset
            sig_select <= (others => '0');
         elsif ((sig_delay_wr_n nor TX_DELAY_RDY_N) = '1') then -- enable
            sig_select <= sig_incremented;
         end if;   
      end if;
   end process;
   
   mux4 : process (sig_output_reg, sig_select)
   begin
      sig_mux_delay <= (others => '0');

      case sig_select(3 downto 0) is
         when "0000"  => sig_mux_delay <= sig_output_reg (7 downto 0);
         when "0001"  => sig_mux_delay <= sig_output_reg (15 downto 8);
         when "0010"  => sig_mux_delay <= sig_output_reg (23 downto 16);
         when "0011"  => sig_mux_delay <= sig_output_reg (31 downto 24);
         when "0100"  => sig_mux_delay <= sig_output_reg (39 downto 32);
         when "0101"  => sig_mux_delay <= sig_output_reg (47 downto 40);
         when "0110"  => sig_mux_delay <= sig_output_reg (55 downto 48);
         when "0111"  => sig_mux_delay <= sig_output_reg (63 downto 56);
         when others => null;   
      end case;   
   end process;
   
   sig_delay <= '0' & sig_mux_delay;
   
   mux5 : process (sig_eof_reg, sig_rem_reg)
   begin
      sig_set_boundary <= (others => '0');

      case sig_eof_reg is
         when '0'    => sig_set_boundary <= "1000";
         when '1'    => sig_set_boundary <= ('0'& sig_rem_reg) + 1;
         when others => null;   
      end case;   
   end process;
   
   comparator2 : process (sig_incremented, sig_set_boundary)
   begin
      if (sig_incremented = sig_set_boundary) then sig_set_delay_rdy_n <= '0';
      else sig_set_delay_rdy_n <= '1';
      end if;
   end process;
   
   sig_set_delay_rdy_n_final <= sig_set_delay_rdy_n or sig_eof_reg; 
   
   -- ================= STOP PROCESSING ====================================
   TX_FINISH <= is_stop;
      
end architecture;
