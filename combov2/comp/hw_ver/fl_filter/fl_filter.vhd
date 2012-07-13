--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Filter
-- Description:  Filters frames with specific byte in the first word into
--               a separate output.
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity FL_FILTER is

   generic
   (
      -- data width
      DATA_WIDTH     : integer := 64;
      -- the value of the observed byte that is to be filtered
      FILTERED_BYTE  : std_logic_vector(7 downto 0) := X"FF"
   );

   port
   (
      CLK       : in std_logic;
      RESET     : in std_logic;

      -- Input FrameLink Interface
      RX_DATA      :  in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM       :  in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP_N     :  in std_logic;
      RX_EOP_N     :  in std_logic;
      RX_SOF_N     :  in std_logic;
      RX_EOF_N     :  in std_logic;
      RX_SRC_RDY_N :  in std_logic;
      RX_DST_RDY_N : out std_logic;

      -- Main output FrameLink Interface
      TX_MAIN_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_MAIN_REM       : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_MAIN_SOP_N     : out std_logic;
      TX_MAIN_EOP_N     : out std_logic;
      TX_MAIN_SOF_N     : out std_logic;
      TX_MAIN_EOF_N     : out std_logic;
      TX_MAIN_SRC_RDY_N : out std_logic;
      TX_MAIN_DST_RDY_N :  in std_logic;

      -- Side output FrameLink Interface
      TX_SIDE_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SIDE_REM       : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SIDE_SOP_N     : out std_logic;
      TX_SIDE_EOP_N     : out std_logic;
      TX_SIDE_SOF_N     : out std_logic;
      TX_SIDE_EOF_N     : out std_logic;
      TX_SIDE_SRC_RDY_N : out std_logic;
      TX_SIDE_DST_RDY_N :  in std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of FL_FILTER is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================
type state_type is (init_state, filtering_state, passing_state);

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- width of the REM signal
constant DREM_WIDTH       : integer := log2(DATA_WIDTH/8);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- input signals
signal sig_rx_data            : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_rx_rem             : std_logic_vector(DREM_WIDTH-1 downto 0);
signal sig_rx_sof_n           : std_logic;
signal sig_rx_eof_n           : std_logic;
signal sig_rx_sop_n           : std_logic;
signal sig_rx_eop_n           : std_logic;
signal sig_rx_src_rdy_n       : std_logic;
signal sig_rx_dst_rdy_n       : std_logic;

-- main output signals
signal sig_tx_main_data            : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_tx_main_rem             : std_logic_vector(DREM_WIDTH-1 downto 0);
signal sig_tx_main_sof_n           : std_logic;
signal sig_tx_main_eof_n           : std_logic;
signal sig_tx_main_sop_n           : std_logic;
signal sig_tx_main_eop_n           : std_logic;
signal sig_tx_main_src_rdy_n       : std_logic;
signal sig_tx_main_dst_rdy_n       : std_logic;

-- side output signals
signal sig_tx_side_data            : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_tx_side_rem             : std_logic_vector(DREM_WIDTH-1 downto 0);
signal sig_tx_side_sof_n           : std_logic;
signal sig_tx_side_eof_n           : std_logic;
signal sig_tx_side_sop_n           : std_logic;
signal sig_tx_side_eop_n           : std_logic;
signal sig_tx_side_src_rdy_n       : std_logic;
signal sig_tx_side_dst_rdy_n       : std_logic;

-- the FSM
signal reg_state       : state_type;
signal next_state      : state_type;

-- the data match comparer
signal data_match      : std_logic;
signal data_match_in   : std_logic_vector(7 downto 0);

-- the dst_rdy_n multiplexor
signal mux_dst_rdy_n_out : std_logic;
signal mux_dst_rdy_n_sel : std_logic;

-- misc signals
signal filtering         : std_logic;

begin

   -- mapping input signals
   sig_rx_data          <= RX_DATA;
   sig_rx_rem           <= RX_REM;
   sig_rx_sof_n         <= RX_SOF_N;
   sig_rx_sop_n         <= RX_SOP_N;
   sig_rx_eof_n         <= RX_EOF_N; 
   sig_rx_eop_n         <= RX_EOP_N;
   sig_rx_src_rdy_n     <= RX_SRC_RDY_N;
   RX_DST_RDY_N         <= sig_rx_dst_rdy_n;

   --
   data_match_in        <= sig_rx_data(7 downto 0);

   -- the comparer of the byte
   data_match_p: process(data_match_in)
   begin
      data_match <= '0';

      if (data_match_in = FILTERED_BYTE) then
         data_match <= '1';
      end if;
   end process;

   -- -- CONTROL FINITE STATE MACHINE --  

   -- -- state logic
   fsm_state_logic : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
           reg_state <= init_state;
         else
           reg_state <= next_state;
         end if;   
      end if;   
   end process;
   
   -- next state logic
   fsm_next_state_logic : process (reg_state, sig_rx_src_rdy_n,
      sig_tx_main_dst_rdy_n, sig_tx_side_dst_rdy_n, data_match, sig_rx_eof_n)
   begin
      next_state <= reg_state;  
      filtering  <= '0';
      
      case reg_state is
         when init_state =>
            if (sig_rx_src_rdy_n = '0') then
               if (data_match = '1') then
                  filtering <= '1';
                  next_state <= filtering_state;
               else
                  filtering <= '0';
                  next_state <= passing_state;
               end if;
            end if;
           
         when filtering_state =>
            filtering <= '1';
            if ((sig_rx_src_rdy_n = '0') AND (sig_tx_side_dst_rdy_n = '0')
               AND (sig_rx_eof_n = '0')) then
               next_state <= init_state;
            end if;
 
         when passing_state =>
            filtering <= '0';
            if ((sig_rx_src_rdy_n = '0') AND (sig_tx_main_dst_rdy_n = '0')
               AND (sig_rx_eof_n = '0')) then
               next_state <= init_state;
            end if;
      end case;      
   end process;
   
   --
   mux_dst_rdy_n_sel <= filtering;

   -- the multiplexer of DST_RDY_N
   mux_dst_rdy_n_p: process (mux_dst_rdy_n_sel, sig_tx_main_dst_rdy_n,
      sig_tx_side_dst_rdy_n)
   begin
      mux_dst_rdy_n_out <= sig_tx_main_dst_rdy_n;

      case (mux_dst_rdy_n_sel) is
         when '0'    => mux_dst_rdy_n_out <= sig_tx_main_dst_rdy_n;
         when '1'    => mux_dst_rdy_n_out <= sig_tx_side_dst_rdy_n;
         when others => null;
      end case;
   end process;

   -- connecting the FrameLink
   sig_tx_main_data          <= sig_rx_data;
   sig_tx_main_rem           <= sig_rx_rem;
   sig_tx_main_sof_n         <= sig_rx_sof_n;
   sig_tx_main_sop_n         <= sig_rx_sop_n;
   sig_tx_main_eof_n         <= sig_rx_eof_n; 
   sig_tx_main_eop_n         <= sig_rx_eop_n;
   sig_tx_main_src_rdy_n     <= sig_rx_src_rdy_n OR filtering;

   sig_tx_side_data          <= sig_rx_data;
   sig_tx_side_rem           <= sig_rx_rem;
   sig_tx_side_sof_n         <= sig_rx_sof_n;
   sig_tx_side_sop_n         <= sig_rx_sop_n;
   sig_tx_side_eof_n         <= sig_rx_eof_n; 
   sig_tx_side_eop_n         <= sig_rx_eop_n;
   sig_tx_side_src_rdy_n     <= sig_rx_src_rdy_n OR (NOT filtering);

   sig_rx_dst_rdy_n          <= mux_dst_rdy_n_out;

   -- mapping output signals
   TX_MAIN_DATA          <= sig_tx_main_data;
   TX_MAIN_REM           <= sig_tx_main_rem;
   TX_MAIN_SOF_N         <= sig_tx_main_sof_n;
   TX_MAIN_SOP_N         <= sig_tx_main_sop_n;
   TX_MAIN_EOF_N         <= sig_tx_main_eof_n; 
   TX_MAIN_EOP_N         <= sig_tx_main_eop_n;
   TX_MAIN_SRC_RDY_N     <= sig_tx_main_src_rdy_n;
   sig_tx_main_dst_rdy_n <= TX_MAIN_DST_RDY_N;

   TX_SIDE_DATA          <= sig_tx_side_data;
   TX_SIDE_REM           <= sig_tx_side_rem;
   TX_SIDE_SOF_N         <= sig_tx_side_sof_n;
   TX_SIDE_SOP_N         <= sig_tx_side_sop_n;
   TX_SIDE_EOF_N         <= sig_tx_side_eof_n; 
   TX_SIDE_EOP_N         <= sig_tx_side_eop_n;
   TX_SIDE_SRC_RDY_N     <= sig_tx_side_src_rdy_n;
   sig_tx_side_dst_rdy_n <= TX_SIDE_DST_RDY_N;

end architecture;

