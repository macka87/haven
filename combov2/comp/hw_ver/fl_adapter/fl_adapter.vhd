--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Adapter
-- Description:  Drives and processes the bitflow from generator according to
--               request from software.
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         19.6.2013 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity FL_ADAPTER_UNIT is

   generic
   (
      -- data width
      DATA_WIDTH  : integer := 64;
      -- endpoint id
      ENDPOINT_ID : integer := 0
   );

   port
   (
      CLK       : in std_logic;
      RESET     : in std_logic;

      -- MI32 Interface
      MI_DWR    :  in std_logic_vector(31 downto 0);
      MI_ADDR   :  in std_logic_vector(31 downto 0);
      MI_RD     :  in std_logic;
      MI_WR     :  in std_logic;
      MI_BE     :  in std_logic_vector( 3 downto 0);
      MI_DRD    : out std_logic_vector(31 downto 0);
      MI_ARDY   : out std_logic;
      MI_DRDY   : out std_logic;
      
      -- Generator Interface
      GEN_FLOW  :  in std_logic_vector(DATA_WIDTH-1 downto 0);
      
      -- Output FrameLink Interface
      TX_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM       : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N : out std_logic;
      TX_DST_RDY_N : in  std_logic;
      TX_SOP_N     : out std_logic;
      TX_EOP_N     : out std_logic;
      TX_SOF_N     : out std_logic;
      TX_EOF_N     : out std_logic
   );       
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of FL_ADAPTER_UNIT is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================
type state_type is (header_state, data_state);

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- the maximum number of parts in a frame
constant MAX_PARTS        : integer := 8;

-- endpoint tag
constant ENDPOINT_TAG     : std_logic_vector(7 downto 0) :=
   conv_std_logic_vector(ENDPOINT_ID, 8);
      
-- FrameLink protocol ID
constant FL_PROTOCOL_ID   : std_logic_vector(7 downto 0) := X"90";   
   
-- data transaction type 
constant DATA_TRANS_TYPE  : std_logic_vector(7 downto 0) := X"00";     

-- width of the REM signal
constant DREM_WIDTH       : integer := log2(DATA_WIDTH/8);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- input signals
signal sig_gen_flow           : std_logic_vector(DATA_WIDTH-1 downto 0);

-- output signals
signal sig_tx_data            : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_tx_rem             : std_logic_vector(DREM_WIDTH-1 downto 0);
signal sig_tx_sof_n           : std_logic;
signal sig_tx_eof_n           : std_logic;
signal sig_tx_sop_n           : std_logic;
signal sig_tx_eop_n           : std_logic;
signal sig_tx_src_rdy_n       : std_logic;
signal sig_tx_dst_rdy_n       : std_logic;

-- size_proc_cover signals
signal sig_frame_rdy           : std_logic;
signal sig_frame_last_word     : std_logic;
signal sig_frame_rem           : std_logic_vector(DREM_WIDTH-1 downto 0);
signal sig_frame_last_in_part  : std_logic;
signal sig_frame_last_in_frame : std_logic;
signal sig_frame_take          : std_logic;

-- FSM signals 
signal state_reg, state_next  : state_type;
signal is_header              : std_logic;

-- Header signals
signal sig_header             : std_logic_vector(DATA_WIDTH-1 downto 0);

-- the output data multiplexor
signal mux_data_out           : std_logic_vector(DATA_WIDTH-1 downto 0);

-- signal active when a word is being sent
signal sig_sent               : std_logic;

-- signal for the start of a FL frame
signal sig_start              : std_logic;

-- signal for the end of a FL frame
signal sig_end                : std_logic;

begin

   -- mapping input signals
   sig_gen_flow      <= GEN_FLOW;

   -- size processing cover
   size_proc_cover_i: entity work.size_proc_cover
   generic map(
      DATA_WIDTH => DATA_WIDTH
   )
   port map(
      -- common signals
      CLK        => CLK,
      RESET      => RESET,

      -- MI32 interface
      MI_DWR   => MI_DWR, 
      MI_ADDR  => MI_ADDR, 
      MI_RD    => MI_RD,
      MI_WR    => MI_WR, 
      MI_BE    => MI_BE, 
      MI_DRD   => MI_DRD, 
      MI_ARDY  => MI_ARDY, 
      MI_DRDY  => MI_DRDY, 
      
      -- Generator interface
      GEN_FLOW => sig_gen_flow,

      -- Output interface
      FRAME_RDY             => sig_frame_rdy,
      FRAME_LAST_WORD       => sig_frame_last_word,
      FRAME_REM             => sig_frame_rem,
      FRAME_LAST_IN_PART    => sig_frame_last_in_part,
      FRAME_LAST_IN_FRAME   => sig_frame_last_in_frame,
      FRAME_TAKE            => sig_frame_take
   );

   sig_frame_take <= NOT (is_header OR sig_tx_dst_rdy_n);
   sig_sent       <= NOT (sig_tx_src_rdy_n OR sig_tx_dst_rdy_n);

   -- -- CONTROL FINITE STATE MACHINE --  

   -- -- state logic
   fsm_state_logic : process (CLK)
   begin
     if (rising_edge(CLK)) then
        if (RESET='1') then
          state_reg <= header_state;
        else
          state_reg <= state_next;
        end if;   
     end if;   
   end process;
   
   -- next state logic
   fsm_next_state_logic : process (state_reg, sig_sent, sig_frame_last_word)
   begin
     state_next <= state_reg;  
     
     case state_reg is
        when header_state =>
           if (sig_sent = '1') then
              state_next <= data_state;
           end if;
          
        when data_state =>
          if ((sig_sent = '1') AND (sig_frame_last_word = '1')) then
             state_next <= header_state; 
          end if; 
     end case;      
   end process;
   
   -- Moore output logic
   moore_output : process (state_reg)
   begin
      -- default values
      is_header    <= '0';
                  
      case state_reg is
         when header_state => is_header <= '1';
         when data_state   => is_header <= '0';
      end case;   
   end process moore_output; 
     
   -- -- OUTPUT FRAMELINK SETTINGS --

   -- data - header multiplexer
   mux_data_p: process (is_header, sig_gen_flow, sig_header)
   begin
      mux_data_out <= sig_gen_flow;

      case is_header is
         when '0'    => mux_data_out <= sig_gen_flow;
         when '1'    => mux_data_out <= sig_header;
         when others => null;   
      end case;   
   end process; 
   
   -- the header
   sig_header(63 downto 50) <= (others => '0');
   sig_header(49)           <= sig_frame_last_in_frame;
   sig_header(48)           <= sig_frame_last_in_part;
   sig_header(47 downto 40) <= X"00";
   sig_header(39 downto 32) <= DATA_TRANS_TYPE;
   sig_header(31 downto 24) <= X"00";
   sig_header(23 downto 16) <= X"00";
   sig_header(15 downto 8)  <= FL_PROTOCOL_ID;
   sig_header( 7 downto 0)  <= ENDPOINT_TAG;

   --
   sig_start <= NOT is_header;
   sig_end   <= NOT (sig_frame_last_word AND (NOT is_header));

   -- handling the output FrameLink
   sig_tx_data            <= mux_data_out;
   sig_tx_rem             <= sig_frame_rem;
   sig_tx_src_rdy_n       <= NOT sig_frame_rdy;
   sig_tx_sof_n           <= sig_start;
   sig_tx_sop_n           <= sig_start;
   sig_tx_eop_n           <= sig_end;
   sig_tx_eof_n           <= sig_end;

   -- mapping output signals
   TX_DATA          <= sig_tx_data;
   TX_REM           <= sig_tx_rem;
   TX_SOF_N         <= sig_tx_sof_n;
   TX_SOP_N         <= sig_tx_sop_n;
   TX_EOF_N         <= sig_tx_eof_n; 
   TX_EOP_N         <= sig_tx_eop_n;
   TX_SRC_RDY_N     <= sig_tx_src_rdy_n;
   sig_tx_dst_rdy_n <= TX_DST_RDY_N;

end architecture;
