--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Scoreboard Sender
-- Description: 
-- Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================

-- This component sends a frame with the header 
entity SCOREBOARD_SENDER is

   generic
   (
      -- data width
      DATA_WIDTH  : integer := 64;
      -- the ID of the endpoint
      ENDPOINT_ID    : std_logic_vector(7 downto 0);
      -- the ID of the protocol
      PROTOCOL_ID    : std_logic_vector(7 downto 0)
   );

   port
   (
      -- common signals
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- the command to send a frame
      SEND           : in  std_logic;
      -- the data to be sent in the data word of the frame
      DATA_CONTENT   : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of SCOREBOARD_SENDER is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================
type state_type is (
   idle_state,
   sending_header_state,
   sending_data_state);

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- input signals
signal sig_send           : std_logic;
signal sig_data_content   : std_logic_vector(DATA_WIDTH-1 downto 0);

-- output signals
signal sig_tx_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_tx_rem         : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal sig_tx_src_rdy_n   : std_logic;
signal sig_tx_dst_rdy_n   : std_logic;
signal sig_tx_sop_n       : std_logic;
signal sig_tx_eop_n       : std_logic;
signal sig_tx_sof_n       : std_logic;
signal sig_tx_eof_n       : std_logic;

-- the states of the FSM
signal reg_state          : state_type;
signal next_state         : state_type;

-- the data multiplexer
signal mux_data_out       : std_logic_vector(DATA_WIDTH-1 downto 0);
signal mux_data_sel       : std_logic;

-- misc signals
signal is_sending_data    : std_logic;

-- the header
signal header             : std_logic_vector(DATA_WIDTH-1 downto 0);

begin

   -- Assertions
   assert (DATA_WIDTH = 64)
      report "Unsupported output FrameLink width!"
      severity failure;

   -- mapping input signals
   sig_send           <= SEND;
   sig_data_content   <= DATA_CONTENT;

   -- the header
   header(63 downto 56)   <= X"00";
   header(55 downto 48)   <= X"00";
   header(47 downto 40)   <= X"00";
   header(39 downto 32)   <= X"00";
   header(31 downto 24)   <= X"00";
   header(23 downto 16)   <= X"00";
   header(15 downto  8)   <= PROTOCOL_ID;
   header( 7 downto  0)   <= ENDPOINT_ID;

   --
   mux_data_sel   <= is_sending_data;

   -- the data multiplexer
   mux_data_p: process (mux_data_sel, header, sig_data_content)
   begin
      mux_data_out <= header;

      case (mux_data_sel) is
         when '0'    => mux_data_out <= header;
         when '1'    => mux_data_out <= sig_data_content;
         when others => null;
      end case;
   end process;

   -- ---------------------- CONTROL FSM ------------------------------------
   -- state register logic
   fsm_state_logic : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_state <= idle_state;
         else
            reg_state <= next_state;
         end if;   
      end if;   
   end process;

   -- next state logic
   fsm_next_state_logic : process (reg_state, sig_send, sig_tx_dst_rdy_n)
   begin
      next_state       <= reg_state;
      is_sending_data  <= '0';
      sig_tx_src_rdy_n <= '1';
 
      case reg_state is
         when idle_state => 
            if (sig_send = '1') then
               next_state <= sending_header_state;
            end if;
 
         when sending_header_state =>
            sig_tx_src_rdy_n <= '0';
 
            if (sig_tx_dst_rdy_n = '0') then
               next_state <= sending_data_state;
            end if;
 
         when sending_data_state =>
            sig_tx_src_rdy_n <= '0';
            is_sending_data  <= '1';
 
            if (sig_tx_dst_rdy_n = '0') then
               next_state <= idle_state;
            end if;
 
      end case;      
   end process;


   -- creating the output framelink
   sig_tx_data       <= mux_data_out;
   sig_tx_rem        <= (others => '1');
   sig_tx_sof_n      <= is_sending_data;
   sig_tx_sop_n      <= is_sending_data;
   sig_tx_eof_n      <= NOT is_sending_data;
   sig_tx_eop_n      <= NOT is_sending_data;

   -- mapping output signals
   TX_DATA           <= sig_tx_data;
   TX_REM            <= sig_tx_rem;
   TX_SOF_N          <= sig_tx_sof_n;
   TX_EOF_N          <= sig_tx_eof_n;
   TX_SOP_N          <= sig_tx_sop_n;
   TX_EOP_N          <= sig_tx_eop_n;
   TX_SRC_RDY_N      <= sig_tx_src_rdy_n;
   sig_tx_dst_rdy_n  <= TX_DST_RDY_N;

end architecture;

