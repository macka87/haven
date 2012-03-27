-----------------------------------------------------------------------------
-- Project Name: HAVEN
-- File Name:    alu.vhd
-- Description:  Arithmetic Logic Unit
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         13.3.2012 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity ALU_ENT is
   generic
   (
      DATA_WIDTH  : integer := 8      
   );
   
   port
   (
      CLK            : in  std_logic;
      RST            : in  std_logic;
      ACT            : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      OP             : in  std_logic_vector(3 downto 0);  -- operation
      MOVI           : in  std_logic_vector(1 downto 0);  -- operand selector
      REG_A          : in  std_logic_vector(DATA_WIDTH-1 downto 0); -- register A
      REG_B          : in  std_logic_vector(DATA_WIDTH-1 downto 0); -- register B 
      MEM            : in  std_logic_vector(DATA_WIDTH-1 downto 0); -- memory operand
      IMM            : in  std_logic_vector(DATA_WIDTH-1 downto 0); -- immediate operand
      ALU_RDY        : out std_logic; 
     
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      EX_ALU         : out std_logic_vector(DATA_WIDTH-1 downto 0);
      EX_ALU_VLD     : out std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture ALU_ARCH of ALU_ENT is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================
type state_type is (init_state, mult_first_state, mult_second_state);

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================
-- FSM signals 
signal state_reg, state_next : state_type;

-- ALU operation
signal sig_operand_A       : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_operand_B       : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_mult_start      : std_logic;
signal sig_mult_result     : std_logic_vector(DATA_WIDTH*2-1 downto 0);
signal sig_mult_result_red : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_mult_vld        : std_logic;
signal sig_alu_result      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_alu_rdy         : std_logic;
signal sig_higher          : std_logic;
signal sig_output_sel      : std_logic; 
signal sig_ex_alu_vld      : std_logic; 

begin

   sig_operand_A <= REG_A;

-- operand B selection 
   mux1 : process (MOVI, REG_B, MEM, IMM)
   begin
      sig_operand_B <= (others => '0');

      case MOVI is
         when "00"   => sig_operand_B <= REG_B;
         when "01"   => sig_operand_B <= MEM;
         when "10"   => sig_operand_B <= IMM;
         when others => null;   
      end case;   
   end process;

-- operation selection   
   mux2 : process (OP, sig_alu_rdy, sig_operand_A, sig_operand_B)
   begin
      sig_alu_result <= (others => '0');
      sig_mult_start <= '0';
      
      if (sig_alu_rdy = '1') then
        case OP is
           -- plus --
           when "0000"  => sig_alu_result <= sig_operand_A + sig_operand_B; 
           -- minus --
           when "0001"  => sig_alu_result <= sig_operand_A - sig_operand_B;
           -- mult --
           when "0010"  => sig_mult_start <= '1';
           -- shift right --
           when "0011"  => sig_alu_result <= '0' & sig_operand_B(7 downto 1);
           -- shift left --
           when "0100"  => sig_alu_result <= sig_operand_B(6 downto 0) & '0';
           -- rotate right --
           when "0101"  => sig_alu_result <= sig_operand_B(0) & sig_operand_B(7 downto 1);
           -- rotate left --
           when "0110"  => sig_alu_result <= sig_operand_B(6 downto 0) & sig_operand_B(7);
           -- not --
           when "0111"  => sig_alu_result <=  not sig_operand_B;
           -- and --
           when "1000"  => sig_alu_result <=  sig_operand_A and sig_operand_B;
           -- or --
           when "1001"  => sig_alu_result <=  sig_operand_A or sig_operand_B;
           -- xor --
           when "1010"  => sig_alu_result <=  sig_operand_A xor sig_operand_B;
           -- nand --
           when "1011"  => sig_alu_result <=  sig_operand_A nand sig_operand_B;
           -- nor --
           when "1100"  => sig_alu_result <=  sig_operand_A nor sig_operand_B;
           -- xnor --
           when "1101"  => sig_alu_result <=  sig_operand_A xnor sig_operand_B;
           -- inc --
           when "1110"  => sig_alu_result <=  sig_operand_B + 1;
           -- dec --
           when "1111"  => sig_alu_result <=  sig_operand_B - 1;
           when others => null;   
        end case; 
      end if;  
        
   end process;   
   
-- Booth's multiplication   
   booth_mult_i : entity work.mult
   
   generic map(
      DATA_WIDTH  => DATA_WIDTH
   )
      
   port map(
      CLK           => CLK,
      RST           => RST,

      -- input interface
      INPUT_A       => sig_operand_A, 
      INPUT_B       => sig_operand_B, 
      START         => sig_mult_start, 
           
      -- output interface      
      MULT_RESULT   => sig_mult_result,
      MULT_VLD      => sig_mult_vld
   );

-- multiplexer for sending results to output interface (low byte first)   
   mux3 : process (sig_higher, sig_mult_result)
   begin
      sig_mult_result_red <= (others => '0');

      case sig_higher is
         when '0'   => sig_mult_result_red <= sig_mult_result(DATA_WIDTH-1 downto 0);
         when '1'   => sig_mult_result_red <= sig_mult_result(DATA_WIDTH*2-1 downto DATA_WIDTH);
         when others => null;   
      end case;   
   end process;  
   
-- multiplexer for final result
   mux4 : process (sig_output_sel, sig_alu_result, sig_mult_result_red)
   begin
      case sig_output_sel is
         when '0'   => EX_ALU <= sig_alu_result;
         when '1'   => EX_ALU <= sig_mult_result_red;
         when others => null;   
      end case;   
   end process;
   
-- ------------------------- FSM --------------------------------------------   
   -- state logic
   fsm_state_logic : process (CLK)
   begin
     if (rising_edge(CLK)) then
        if (RST = '1') then
          state_reg <= init_state;
        else
          state_reg <= state_next;
        end if;   
     end if;   
   end process;
   
   -- next state logic
   fsm_next_state_logic : process (state_reg, ACT, OP, sig_mult_vld)
   begin
     state_next <= state_reg;  
     
     case state_reg is
        when init_state =>
          if (OP = "0010" and ACT = '1') then 
             state_next <= mult_first_state;
             sig_mult_start <= '1'; 
             sig_ex_alu_vld <= '0';
          else 
             state_next <= init_state;
             sig_mult_start <= '0'; 
             sig_ex_alu_vld <= ACT;
          end if;                
        
        when mult_first_state => 
          if (sig_mult_vld = '1') then 
             state_next <= mult_second_state;
             sig_mult_start <= '0'; 
             sig_ex_alu_vld <= '1';
          else 
             state_next <= mult_first_state; 
             sig_mult_start <= '0';
             sig_ex_alu_vld <= '0';
          end if;
        
        when mult_second_state =>
             state_next <= init_state;
             sig_mult_start <= '0'; 
             sig_ex_alu_vld <= '1';
      end case;      
   end process;  

   EX_ALU_VLD <= sig_ex_alu_vld;
   
-- Moore output logic
   moore_output : process (state_reg)
   begin
      -- default values
      sig_alu_rdy    <= '0';
      sig_higher     <= '0';
      sig_output_sel <= '0'; 
            
      case state_reg is
         when init_state         => sig_alu_rdy    <= '1';
                                    sig_higher     <= '0';
                                    sig_output_sel <= '0';
         when mult_first_state   => sig_alu_rdy    <= '0';
                                    sig_higher     <= '0';
                                    sig_output_sel <= '1';
         when mult_second_state  => sig_alu_rdy    <= '0';
                                    sig_higher     <= '1';
                                    sig_output_sel <= '1';
      end case;   
   end process moore_output;
   
   ALU_RDY <= sig_alu_rdy;

end architecture;
