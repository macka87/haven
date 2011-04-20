--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Driver 
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
entity FL_DRIVER is

   generic
   (
      -- data width
      IN_DATA_WIDTH  : integer := 64;
      OUT_DATA_WIDTH : integer := 71;
      DELAY_WIDTH    : integer := 9
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input FrameLink interface
      RX_DATA        : in  std_logic_vector(IN_DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(IN_DATA_WIDTH/8)-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA        : out std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      
      -- output delay interface
      TX_DELAY       : out std_logic_vector(DELAY_WIDTH-1 downto 0);
      TX_DELAY_WR_N  : out std_logic;
      TX_DELAY_RDY_N : in  std_logic;
      
      -- driver is disabled from software
      TX_FINISH      : out std_logic; 
   );
   
end entity FL_DRIVER;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of FL_DRIVER is
-- ==========================================================================
--                                      TYPES
-- ==========================================================================
type state_type is (init_state, sof_state, sop_state, data_state, delay_state,
                    wait_state, stop_state);

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================
constant DATA_TYPE  :  std_logic_vector := X"00";
constant WAIT_TYPE  :  std_logic_vector := X"02";
constant DELAY_TYPE :  std_logic_vector := X"05";
constant STOP_TYPE  :  std_logic_vector := X"04";

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================
-- FSM signals ---------------------------------------------------------------
signal state_reg, state_next   : state_type;
signal read_header             : std_logic;
signal read_data               : std_logic;
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
   fsm_next_state_logic : process (state_reg)
   begin
     state_next <= state_reg;  

     case state_reg is
        
        when init_state =>
          if (RX_SRC_RDY_N ='0' and sig_dst_rdy_n ='0') then
            if (sig_trans_type = DATA_TYPE)
              if (sig_reg_last = '1') then
                state_next <= sof_state;
                sig_reg_last <= sig_new_last;
              elsif (sig_reg_last = '0') then  
                state_next <= sop_state;
                sig_reg_last <= sig_new_last;
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
          if (RX_SRC_RDY_N ='0' and sig_dst_rdy_n ='0') then 
            if (RX_EOF_N = '0') then 
              state_next <= init_state;
              sig_out_sof_n <= '0';
              sig_out_sop_n <= '0'; 
              sig_out_eof_n <= '0';
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
          if (RX_SRC_RDY_N ='0' and sig_dst_rdy_n ='0') then 
            if (RX_EOF_N = '0') then 
              state_next <= init_state;
              sig_out_sof_n <= '1';
              sig_out_sop_n <= '0'; 
              sig_out_eof_n <= sig_reg_last;
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
          if (RX_SRC_RDY_N ='0' and sig_dst_rdy_n ='0') then 
            if (RX_EOF_N = '0') then 
              state_next <= init_state;
              sig_out_sof_n <= '1';
              sig_out_sop_n <= '1'; 
              sig_out_eof_n <= sig_reg_last;
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
          if (RX_SRC_RDY_N ='0' and sig_dst_rdy_n ='0' and RX_EOF_N = '0') then 
            state_next <= init_state;
          else 
            state_next <= delay_state;        
          end if;
          
        when stop_state =>
          state_next <= stop_state;
        
        when wait_state =>
          if (RX_SRC_RDY_N ='0' and sig_dst_rdy_n ='0' and RX_EOF_N = '0' and
              sig_counter_is_zero = '1') then
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
      
      case state_reg is
         when init_state  => is_header <= '1';
         when sof_state   => is_data   <= '1';
         when sop_state   => is_data   <= '1';
         when data_state  => is_data   <= '1';
         when delay_state => is_delay  <= '1';  
         when stop_state  => is_stop   <= '1';
         when wait_state  => is_wait   <= '1'; 
         when counter_state => is_cntr <= '1';
                                                    
                                                                                                             
      end case;   
   end process moore_output;
end architecture;
