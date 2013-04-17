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
      RX_REM         : in  std_logic_vector(2 downto 0);
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;

      --           halt signal from processor
      HALT           : in  std_logic;
      
      --           output interface - codix - memory write
      dbg_mode_mem      : out std_logic;
      dbg_mode_mem_D0   : out std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      dbg_mode_mem_WA0  : out std_logic_vector(18 downto 0);
      dbg_mode_mem_WE0  : out std_logic;
      dbg_mode_mem_WSC0 : out std_logic_vector(2 downto 0);
      dbg_mode_mem_WSI0 : out std_logic_vector(1 downto 0)

   );
   
end entity;

-- ----------------------------------------------------------
--                 architecture
-- ----------------------------------------------------------
architecture arch of PROGRAM_DRIVER is

-- ----------------------------------------------------------
--                 FSM states
-- ----------------------------------------------------------
type state_type is (init_state, data_1half, data_2half, stop_state);

-- ----------------------------------------------------------
--                 constants
-- ----------------------------------------------------------
constant DATA_TYPE  : std_logic_vector(7 downto 0) := X"00";
constant START_TYPE : std_logic_vector(7 downto 0) := X"01";
constant STOP_TYPE  : std_logic_vector(7 downto 0) := X"04";

-- ----------------------------------------------------------
--                 signals
-- ----------------------------------------------------------

-- FSM signals
signal state_reg, state_next   : state_type;
signal is_header, is_stop, is_half : std_logic;

-- trasaction type
signal sig_trans_type    : std_logic_vector(7 downto 0);

-- output interface signals
signal cnt_addr          : std_logic_vector(18 downto 0);                 -- address counter 19b
signal sig_out_dbg_mode  : std_logic;                                     -- debug mode memory
signal sig_out_we        : std_logic;                                     -- write enable
signal sig_out_sb_cnt    : std_logic_vector(2 downto 0);                  -- subblock count
signal sig_out_sb_idx    : std_logic_vector(1 downto 0);                  -- subblock index
signal sig_out_d0        : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);   -- data out 32b
signal sig_half_out      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);

signal sig_out_dst_rdy_n : std_logic;

signal output_reg        : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);

signal data_ready : std_logic;

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
   fsm_next_state_logic : process (state_reg, data_ready, RX_SOF_N, 
                                   sig_trans_type, RX_EOF_N, RX_SRC_RDY_N)

   begin
     state_next         <= state_reg;   

     sig_out_dbg_mode   <= '1';        -- memory debug mode port
     sig_out_sb_cnt     <= "100";      -- subblock count - 4
     sig_out_sb_idx     <= "00";       -- subblock index

     case state_reg is
        
        -- init state
        when init_state =>

          -- address counter set to zero
          cnt_addr <= (others => '0');

          -- src and dst ready, data transaction and active halt
          if data_ready='1' then
            if sig_trans_type=DATA_TYPE and HALT='1' then
              -- write first half of data
              state_next <= data_1half;
            elsif sig_trans_type=STOP_TYPE then
              state_next <= stop_state;
            elsif sig_trans_type=START_TYPE then 
              state_next <= init_state; 
            end if;

          else
            state_next <= init_state;
          end if;

        -- first half of data write to memory
        when data_1half =>

          -- increment address
          cnt_addr <= cnt_addr + "0000000000000000100";
          report "signal cnt_addr is incremented at time " & time'image(now);

          -- write second half of data
          state_next <= data_2half;

        -- data trasaction transfer
        when data_2half =>

          -- end of data
          if RX_EOF_N = '0' and data_ready = '1' then
            if sig_trans_type = STOP_TYPE then
              state_next <= stop_state;
            else 
              state_next <= init_state;
            end if;

          -- data ready - continue with transfer
          elsif RX_EOP_N = '1' and data_ready = '1' then
              -- increment address
              --cnt_addr <= cnt_addr + 4;

              state_next <= data_1half;

          -- data not ready - wait
          else
              state_next <= data_2half;
          end if;

        when stop_state => 
          if sig_trans_type = START_TYPE then 
            state_next <= init_state;
          else 
            state_next <= stop_state;
          end if;
          
     end case;      
  end process;

  -- Moore output logic
  moore_output : process (state_reg)
  begin
     -- default values
     is_header    <= '0';
     is_stop      <= '0'; -- ??
     is_half      <= '0';
      
     case state_reg is
        when init_state => is_header <= '1';
        when data_1half => is_half   <= '1';
        when stop_state => is_stop   <= '1';
        when data_2half => is_half   <= '0';
     end case;   
  end process moore_output;

   mux_we : process (is_header, is_half, RX_REM, data_ready, is_stop)
   begin
      sig_out_we <= '0';

      -- data transfer
      if    (is_half = '1' )                   then sig_out_we <= '1';

      -- init state
      elsif (is_header = '1')                  then sig_out_we <= '0';

      -- do not write second half of input data when REM is 011
      elsif (is_half = '0' and RX_REM = "011") then sig_out_we <= '0';

      -- write enable when second half data is valid
      elsif (is_half = '0' and RX_REM = "111") then sig_out_we <= '1';

      -- stop transaction
      elsif (is_stop = '1')                    then sig_out_we <= '0';

      end if;

   end process;

   mux_dst_rdy : process (is_half, state_reg)
   begin
     -- first half of data - destination not ready
     if    (is_half   = '1') then sig_out_dst_rdy_n <= '1';
     elsif (is_half   = '0') then sig_out_dst_rdy_n <= '0';
     elsif (is_header = '1') then sig_out_dst_rdy_n <= '0';
     elsif (is_stop   = '1') then sig_out_dst_rdy_n <= '0';
     end if;
   end process mux_dst_rdy;

   reg_half : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then 
            output_reg    <= X"00000000";
         elsif (is_half = '1') then
            output_reg <= RX_DATA(63 downto 32);
         end if;
      end if;
   end process;

   mux_half : process (is_half, RX_DATA, output_reg)
   begin
     if (is_half = '1') then sig_half_out <= RX_DATA(31 downto 0);
     else                    sig_half_out <= output_reg;
     end if;
   end process;

  mux_out : process (is_header, sig_half_out)
  begin
     if (is_header = '0') then sig_out_d0 <= sig_half_out;
     else                      sig_out_d0 <= X"00000000";
     end if;   
  end process;

--  sig_out_dst_rdy_n <= (is_header or is_stop) or (not is_half);
  sig_trans_type <= RX_DATA(39 downto 32);
  RX_DST_RDY_N <= sig_out_dst_rdy_n;
  data_ready <= RX_SRC_RDY_N nor sig_out_dst_rdy_n;

  -- 
  -- output processing
  dbg_mode_mem      <= sig_out_dbg_mode;
  dbg_mode_mem_WE0  <= sig_out_we;
  dbg_mode_mem_WA0  <= cnt_addr;
  dbg_mode_mem_WSC0 <= sig_out_sb_cnt;
  dbg_mode_mem_WSI0 <= sig_out_sb_idx;
  dbg_mode_mem_D0   <= sig_out_d0;

end architecture;

