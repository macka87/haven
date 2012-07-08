-- --------------------------------------------------------------------------
-- Project Name: HAVEN
-- File Name:    tx_delay_proc_unit.vhd  
-- Description:  TX Delay Processing Unit
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         19.4.2012 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity TX_DELAY_PROC_UNIT is

   generic
   (
      -- delay width
      DELAY_WIDTH    : integer := 9
   );

   port
   (
      -- common signals
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- inputs
      DELAY_DATA     : in  std_logic_vector(DELAY_WIDTH-1 downto 0);
      DELAY_READ     : out std_logic;
      DELAY_EMPTY    : in  std_logic;

      -- outputs
      DST_RDY        : in  std_logic;
      SRC_RDY        : out std_logic
   );
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of TX_DELAY_PROC_UNIT is
-- ==========================================================================
--                                      TYPES
-- ==========================================================================


-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- the width of the delay counter
constant CNT_WIDTH         : integer := DELAY_WIDTH-1;

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- inputs
signal sig_delay_data    : std_logic_vector(DELAY_WIDTH-1 downto 0);
signal sig_delay_read    : std_logic;
signal sig_delay_empty   : std_logic;

-- outputs
signal sig_src_rdy       : std_logic;
signal sig_dst_rdy       : std_logic;

-- misc signals
signal sig_delay_data_trimmed     : std_logic_vector(CNT_WIDTH-1 downto 0);
signal sig_delay_data_trimmed_dec : std_logic_vector(CNT_WIDTH-1 downto 0);
signal sig_will_be_sent           : std_logic;
signal sig_is_immediate           : std_logic;

-- the input multiplexer
signal mux_input_out              : std_logic_vector(CNT_WIDTH-1 downto 0);
signal mux_input_sel              : std_logic;

-- the input data zero comparer
signal cmp_input_zero_out         : std_logic;

-- register for the 'will_be_sent' signal
signal reg_will_be_sent           : std_logic;
signal reg_will_be_sent_en        : std_logic;
signal reg_will_be_sent_in        : std_logic;

-- the 'will_be_sent' multiplexer
signal mux_will_be_sent_out       : std_logic;
signal mux_will_be_sent_sel       : std_logic;

-- register keeping value whether it should be read from the FIFO
signal reg_next_read     : std_logic;
signal reg_next_read_set : std_logic;
signal reg_next_read_clr : std_logic;

-- the impulse_counter component
signal impulse_cnt_data         : std_logic_vector(CNT_WIDTH-1 downto 0);
signal impulse_cnt_load         : std_logic;
signal impulse_cnt_zero_impulse : std_logic;

-- the output_reg component
signal output_reg_rdy_in        : std_logic;
signal output_reg_write         : std_logic;
signal output_reg_src_rdy       : std_logic;
signal output_reg_dst_rdy       : std_logic;

-- ==========================================================================
--                           ARCHITECTURE BODY
-- ==========================================================================
begin

   -- mapping input signals
   sig_delay_data  <= DELAY_DATA;
   sig_delay_empty <= DELAY_EMPTY;
   DELAY_READ      <= sig_delay_read;

   -- decomposition of the input data signal
   sig_delay_data_trimmed <= sig_delay_data(CNT_WIDTH-1 downto 0);
   sig_will_be_sent       <= NOT sig_delay_data(CNT_WIDTH);

   -- decrement of the input data
   sig_delay_data_trimmed_dec <= sig_delay_data_trimmed - 1;

   --
   mux_input_sel <= sig_will_be_sent;

   -- the input data multiplexer
   mux_input_p: process(mux_input_sel, sig_delay_data_trimmed,
      sig_delay_data_trimmed_dec)
   begin
      mux_input_out <= sig_delay_data_trimmed;

      case (mux_input_sel) is
         when '0'     => mux_input_out <= sig_delay_data_trimmed_dec;
         when '1'     => mux_input_out <= sig_delay_data_trimmed;
         when others  => null;
      end case;
   end process;

   -- comparer whether the input data is zero
   cmp_input_zero_p: process(mux_input_out)
   begin
      cmp_input_zero_out <= '0';

      if (mux_input_out = 0) then
         cmp_input_zero_out <= '1';
      end if;
   end process;

   sig_is_immediate <= cmp_input_zero_out AND sig_delay_read;

   --
   impulse_cnt_data  <= mux_input_out;
   impulse_cnt_load  <= sig_delay_read;

   -- the impulse counter that counts down the delay
   impulse_counter_i: entity work.IMPULSE_COUNTER
   generic map(
      DATA_WIDTH => CNT_WIDTH
   )
   port map(
      
      CLK            => CLK,
      RESET          => RESET,
      -- ----------- INPUT -----------
      -- the number of clock cycles to wait (aka 'the delay')
      DATA           => impulse_cnt_data,
      -- load the data into the counter and starts counting
      LOAD           => impulse_cnt_load,

      -- ----------- OUTPUT -----------
      -- produces an impulse when the counter reaches zero
      ZERO_IMPULSE   => impulse_cnt_zero_impulse
   );

   --
   reg_will_be_sent_en <= sig_delay_read;
   reg_will_be_sent_in <= sig_will_be_sent;

   -- register for the sig_will_be_sent signal
   reg_will_be_sent_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (reg_will_be_sent_en = '1') then
            reg_will_be_sent <= reg_will_be_sent_in;
         end if;
      end if;
   end process;

   --
   mux_will_be_sent_sel <= sig_is_immediate;

   -- the multiplexer for the value of the 'will_be_sent' signal
   mux_will_be_sent_p: process(mux_will_be_sent_sel, sig_will_be_sent,
      reg_will_be_sent)
   begin
      mux_will_be_sent_out <= sig_will_be_sent;

      case (mux_will_be_sent_sel) is
         when '0'    => mux_will_be_sent_out <= reg_will_be_sent;
         when '1'    => mux_will_be_sent_out <= sig_will_be_sent;
         when others => null;
      end case;
   end process;

   --
   output_reg_rdy_in <= mux_will_be_sent_out;
   output_reg_write  <=     (sig_is_immediate OR impulse_cnt_zero_impulse)
                        AND (NOT sig_delay_empty);

   -- the output register
   output_reg_i: entity work.OUTPUT_REG
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- ----------- INPUT -----------
      -- the value of the ready signal (which should be put at the output
      RDY_IN         => output_reg_rdy_in,
      -- write into the register (when active, the RDY_IN signal is directly
      -- passed to SRC_RDY)
      WRITE          => output_reg_write,

      -- ----------- OUTPUT -----------
      SRC_RDY        => output_reg_src_rdy,
      DST_RDY        => output_reg_dst_rdy
   );

   sig_src_rdy        <= output_reg_src_rdy;
   output_reg_dst_rdy <= sig_dst_rdy;

   --
   reg_next_read_set <= sig_src_rdy AND sig_dst_rdy;
   reg_next_read_clr <= reg_next_read AND (NOT sig_delay_empty);

   -- register being set when there should be a read from the FIFO in the
   -- following clock cycle
   reg_next_read_p: process(CLK, RESET)
   begin
      if (RESET = '1') then
         reg_next_read <= '1';
      elsif (rising_edge(CLK)) then
         if (reg_next_read_set = '1') then
            reg_next_read <= '1';
         elsif (reg_next_read_clr = '1') then
            reg_next_read <= '0';
         end if;
      end if;
   end process;

   sig_delay_read <= reg_next_read;


   -- mapping output signals
   SRC_RDY         <= sig_src_rdy;
   sig_dst_rdy     <= DST_RDY;

end architecture;
