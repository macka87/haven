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
type state_type is (data_header_state, data_content_state, delay_header_state,
   delay_content_state);

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

-- delay transaction type 
constant DELAY_TRANS_TYPE : std_logic_vector(7 downto 0) := X"05";

-- width of the REM signal
constant DREM_WIDTH       : integer := log2(DATA_WIDTH/8);

-- the size of the counter for outputting data (also determines the maximum
-- size of the output data block)
constant DATA_SIZE_CNT_WIDTH   : integer := 11;

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

signal sig_data_size           : std_logic_vector(DATA_SIZE_CNT_WIDTH-1 downto 0);
signal sig_data_size_vld       : std_logic;
signal sig_data_size_take      : std_logic;

-- delay proc unit signals
signal sig_delay_rdy           : std_logic;
signal sig_delay_rem           : std_logic_vector(DREM_WIDTH-1 downto 0);
signal sig_delay_last          : std_logic;
signal sig_delay_take          : std_logic;

-- FSM signals 
signal state_reg, state_next  : state_type;
signal is_data_header         : std_logic;
signal is_data_content        : std_logic;
signal is_delay_header        : std_logic;
signal is_delay_content       : std_logic;

-- misc signals
signal is_header              : std_logic;
signal is_data                : std_logic;
signal sig_accept             : std_logic;

-- Header signals
signal sig_header             : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_data_header        : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_delay_header       : std_logic_vector(DATA_WIDTH-1 downto 0);

-- the delay transformer
signal delay_transformer_in   : std_logic_vector(DATA_WIDTH-1 downto 0);
signal delay_transformer_out  : std_logic_vector(DATA_WIDTH-1 downto 0);

-- the output REM multiplexor
signal mux_rem_out            : std_logic_vector(DREM_WIDTH-1 downto 0);

-- the output RDY multiplexor
signal mux_rdy_out            : std_logic;

-- the output LAST multiplexor
signal mux_last_out           : std_logic;

-- the data word for a delay
signal sig_delay_word         : std_logic_vector(DATA_WIDTH-1 downto 0);

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

   -- size processing cover -------------------------------------------------
   size_proc_cover_i: entity work.size_proc_cover
   generic map(
      DATA_WIDTH          => DATA_WIDTH,
      DATA_SIZE_CNT_WIDTH => DATA_SIZE_CNT_WIDTH
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

      -- Data size interface (to connect delay_proc_unit)
      DATA_SIZE             => sig_data_size,
      DATA_SIZE_VLD         => sig_data_size_vld,
      DATA_SIZE_TAKE        => sig_data_size_take,

      -- Output interface
      FRAME_RDY             => sig_frame_rdy,
      FRAME_LAST_WORD       => sig_frame_last_word,
      FRAME_REM             => sig_frame_rem,
      FRAME_LAST_IN_PART    => sig_frame_last_in_part,
      FRAME_LAST_IN_FRAME   => sig_frame_last_in_frame,
      FRAME_TAKE            => sig_frame_take
   );

   sig_frame_take <= sig_accept AND is_data;

   sig_accept     <= NOT (is_header OR sig_tx_dst_rdy_n);
   sig_sent       <= NOT (sig_tx_src_rdy_n OR sig_tx_dst_rdy_n);

   -- -- DELAY PROCESSING UNIT INSTANCE --
   delay_proc_unit_i : entity work.delay_proc_unit
   generic map(
      DATA_WIDTH => DATA_WIDTH,
      SIZE_WIDTH => DATA_SIZE_CNT_WIDTH
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
   
      -- Data Part processing interface
      DATA_SIZE      => sig_data_size,
      DATA_SIZE_VLD  => sig_data_size_vld,
      DATA_SIZE_TAKE => sig_data_size_take,
      
      -- Delay processing interface
      DELAY_RDY      => sig_delay_rdy,
      DELAY_REM      => sig_delay_rem,
      DELAY_LAST     => sig_delay_last,
      DELAY_TAKE     => sig_delay_take
   ); 

   sig_delay_take <= sig_accept AND (NOT is_data);

   -- the REM multiplexer
   mux_rem_p: process(sig_frame_rem, sig_delay_rem, is_data)
   begin
      mux_rem_out <= sig_frame_rem;

      case is_data is
         when '0'    => mux_rem_out <= sig_delay_rem;
         when '1'    => mux_rem_out <= sig_frame_rem;
         when others => null;
      end case;
   end process;

   -- the RDY multiplexer
   mux_rdy_p: process(sig_frame_rdy, sig_delay_rdy, is_data)
   begin
      mux_rdy_out <= sig_frame_rdy;

      case is_data is
         when '0'    => mux_rdy_out <= sig_delay_rdy;
         when '1'    => mux_rdy_out <= sig_frame_rdy;
         when others => null;
      end case;
   end process;

   -- the LAST_WORD multiplexer
   mux_last_p: process(sig_frame_last_word, sig_delay_last, is_data)
   begin
      mux_last_out <= sig_frame_last_word;

      case is_data is
         when '0'    => mux_last_out <= sig_delay_last;
         when '1'    => mux_last_out <= sig_frame_last_word;
         when others => null;
      end case;
   end process;

   --
   delay_transformer_in <= sig_gen_flow;

   -- the delay transformer
   delay_transformer_i: entity work.delay_transformer
   generic map(
      DATA_WIDTH => DATA_WIDTH
   )
   port map(
      INPUT      => delay_transformer_in,
      OUTPUT     => delay_transformer_out
   );

   sig_delay_word   <= delay_transformer_out;


   -- -- CONTROL FINITE STATE MACHINE --  

   -- -- state logic
   fsm_state_logic : process (CLK)
   begin
     if (rising_edge(CLK)) then
        if (RESET='1') then
          state_reg <= data_header_state;
        else
          state_reg <= state_next;
        end if;   
     end if;   
   end process;
   
   -- next state logic
   fsm_next_state_logic : process (state_reg, sig_sent, sig_frame_last_word,
      sig_delay_last)
   begin
     state_next <= state_reg;  
     
     case state_reg is
        when data_header_state =>
           if (sig_sent = '1') then
              state_next <= data_content_state;
           end if;
          
        when data_content_state =>
          if ((sig_sent = '1') AND (sig_frame_last_word = '1')) then
             state_next <= delay_header_state; 
          end if; 

        when delay_header_state =>
           if (sig_sent = '1') then
              state_next <= delay_content_state;
           end if;
          
        when delay_content_state =>
          if ((sig_sent = '1') AND (sig_delay_last = '1')) then
             state_next <= data_header_state; 
          end if; 
     end case;      
   end process;
   
   -- Moore output logic
   moore_output : process (state_reg)
   begin
      -- default values
      is_data_header    <= '0';
      is_data_content   <= '0';
      is_delay_header   <= '0';
      is_delay_content  <= '0';
                  
      case state_reg is
         when data_header_state   => is_data_header   <= '1';
         when data_content_state  => is_data_content  <= '1';
         when delay_header_state  => is_delay_header  <= '1';
         when delay_content_state => is_delay_content <= '1';
      end case;   
   end process; 

   is_data   <= is_data_header OR is_data_content;
   is_header <= is_data_header OR is_delay_header;
     
   -- -- OUTPUT FRAMELINK SETTINGS --

   -- data - header multiplexer
   mux_data_p: process (is_header, is_data, sig_gen_flow, sig_delay_word,
      sig_data_header, sig_delay_header)
      variable sel : std_logic_vector(1 downto 0);
   begin
      mux_data_out <= sig_gen_flow;

      sel := is_data & is_header;
      case sel is
         when "00"    => mux_data_out <= sig_delay_word;
         when "01"    => mux_data_out <= sig_delay_header;
         when "10"    => mux_data_out <= sig_gen_flow;
         when "11"    => mux_data_out <= sig_data_header;
         when others => null;   
      end case;   
   end process; 
   
   -- the universal header
   sig_header(63 downto 50) <= (others => '0');
   sig_header(49)           <= sig_frame_last_in_frame;
   sig_header(48)           <= sig_frame_last_in_part;
   sig_header(47 downto 40) <= X"00";
   sig_header(39 downto 32) <= X"00";    -- for the transaction type
   sig_header(31 downto 24) <= X"00";
   sig_header(23 downto 16) <= X"00";
   sig_header(15 downto 8)  <= FL_PROTOCOL_ID;
   sig_header( 7 downto 0)  <= ENDPOINT_TAG;

   -- the data header
   sig_data_header(63 downto 40) <= sig_header(63 downto 40);
   sig_data_header(39 downto 32) <= DATA_TRANS_TYPE;
   sig_data_header(31 downto  0) <= sig_header(31 downto  0);

   sig_delay_header(63 downto 40) <= sig_header(63 downto 40);
   sig_delay_header(39 downto 32) <= DELAY_TRANS_TYPE;
   sig_delay_header(31 downto  0) <= sig_header(31 downto  0);

   --
   sig_start <= NOT is_header;
   sig_end   <= NOT (mux_last_out AND (NOT is_header));

   -- handling the output FrameLink
   sig_tx_data            <= mux_data_out;
   sig_tx_rem             <= mux_rem_out;
   sig_tx_src_rdy_n       <= NOT mux_rdy_out;
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
