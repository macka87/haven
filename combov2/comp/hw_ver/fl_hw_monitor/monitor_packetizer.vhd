--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    Smart FrameLink Monitor input packetizer 
-- Description: 
-- Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
-- Date:         15.4.2011 
-- TODO:         This component is not ready for sending multi-part frames!!!
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity MONITOR_PACKETIZER is

   generic
   (
      -- data width
      DATA_WIDTH  : integer := 64;
      ENDPOINT_ID : integer
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
      TX_EOF_N       : out std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of MONITOR_PACKETIZER is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================
type state_type is (header_state, not_header_state);

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================
constant HEADER_WIDTH : integer := 8;

-- output transaction type
constant DATA_TYPE   :  std_logic_vector(7 downto 0) := X"00";

-- FrameLink protocol ID
constant FRAMELINK_PROTOCOL_ID :  std_logic_vector(7 downto 0) := X"80";

-- endpoint tag
constant ENDPOINT_TAG : std_logic_vector(7 downto 0) :=
   conv_std_logic_vector(ENDPOINT_ID, 8);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================
-- input
signal sig_rx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_rx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal sig_rx_sof_n     : std_logic;
signal sig_rx_sop_n     : std_logic;
signal sig_rx_eof_n     : std_logic;
signal sig_rx_eop_n     : std_logic;
signal sig_rx_src_rdy_n : std_logic;
signal sig_rx_dst_rdy_n : std_logic;

-- output
signal sig_tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_tx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal sig_tx_sof_n     : std_logic;
signal sig_tx_sop_n     : std_logic;
signal sig_tx_eof_n     : std_logic;
signal sig_tx_eop_n     : std_logic;
signal sig_tx_src_rdy_n : std_logic;
signal sig_tx_dst_rdy_n : std_logic;

-- FRAME FIFO input
signal rx_frame_fifo_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal rx_frame_fifo_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal rx_frame_fifo_sof_n     : std_logic;
signal rx_frame_fifo_sop_n     : std_logic;
signal rx_frame_fifo_eof_n     : std_logic;
signal rx_frame_fifo_eop_n     : std_logic;
signal rx_frame_fifo_src_rdy_n : std_logic;
signal rx_frame_fifo_dst_rdy_n : std_logic;

-- FRAME FIFO output
signal tx_frame_fifo_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal tx_frame_fifo_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal tx_frame_fifo_sof_n     : std_logic;
signal tx_frame_fifo_sop_n     : std_logic;
signal tx_frame_fifo_eof_n     : std_logic;
signal tx_frame_fifo_eop_n     : std_logic;
signal tx_frame_fifo_src_rdy_n : std_logic;
signal tx_frame_fifo_dst_rdy_n : std_logic;

-- HEADER FIFO input
signal rx_header_fifo_data      : std_logic_vector(HEADER_WIDTH-1 downto 0);
signal rx_header_fifo_rem       : std_logic_vector(log2(HEADER_WIDTH/8)-1 downto 0);
signal rx_header_fifo_sof_n     : std_logic;
signal rx_header_fifo_sop_n     : std_logic;
signal rx_header_fifo_eof_n     : std_logic;
signal rx_header_fifo_eop_n     : std_logic;
signal rx_header_fifo_src_rdy_n : std_logic;
signal rx_header_fifo_dst_rdy_n : std_logic;

-- HEADER FIFO output
signal tx_header_fifo_data      : std_logic_vector(HEADER_WIDTH-1 downto 0);
signal tx_header_fifo_rem       : std_logic_vector(log2(HEADER_WIDTH/8)-1 downto 0);
signal tx_header_fifo_sof_n     : std_logic;
signal tx_header_fifo_sop_n     : std_logic;
signal tx_header_fifo_eof_n     : std_logic;
signal tx_header_fifo_eop_n     : std_logic;
signal tx_header_fifo_src_rdy_n : std_logic;
signal tx_header_fifo_dst_rdy_n : std_logic;

-- FSM signals ---------------------------------------------------------------
signal state_reg    : state_type;
signal state_next   : state_type;

-- header output signals
signal header_data    : std_logic_vector(DATA_WIDTH-1 downto 0);
signal header_rem     : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

-- miscellaneous signals
signal sending_header : std_logic;

begin

   -- Assertions
   assert (DATA_WIDTH = 64)
      report "Unsupported OUT_DATA_WIDTH!"
      severity failure;

   -- map input ports
   sig_rx_data         <= RX_DATA;
   sig_rx_rem          <= RX_REM;
   sig_rx_sof_n        <= RX_SOF_N;
   sig_rx_eof_n        <= RX_EOF_N;
   sig_rx_sop_n        <= RX_SOP_N;
   sig_rx_eop_n        <= RX_EOP_N;
   sig_rx_src_rdy_n    <= RX_SRC_RDY_N;
   RX_DST_RDY_N        <= sig_rx_dst_rdy_n;

   -- component readiness
   sig_rx_dst_rdy_n    <= rx_frame_fifo_dst_rdy_n OR rx_header_fifo_dst_rdy_n;

   -- FRAME FIFO input
   rx_frame_fifo_data         <= sig_rx_data;
   rx_frame_fifo_rem          <= sig_rx_rem;
   rx_frame_fifo_sof_n        <= sig_rx_sof_n;
   rx_frame_fifo_eof_n        <= sig_rx_eof_n;
   rx_frame_fifo_sop_n        <= sig_rx_sop_n;
   rx_frame_fifo_eop_n        <= sig_rx_eop_n;
   rx_frame_fifo_src_rdy_n    <= sig_rx_src_rdy_n OR rx_header_fifo_dst_rdy_n;

   -- --------------- FRAME FIFO INSTANCE -----------------------------------
   frame_fifo : entity work.fl_fifo
   generic map(
      DATA_WIDTH  => DATA_WIDTH,
      USE_BRAMS   => true,
      ITEMS       => 1024,
      PARTS       => 1
   )
   port map (
      RESET       => RESET,
      CLK         => CLK,

      -- Write interface
      RX_DATA        => rx_frame_fifo_data,
      RX_REM         => rx_frame_fifo_rem,
      RX_SRC_RDY_N   => rx_frame_fifo_src_rdy_n, 
      RX_DST_RDY_N   => rx_frame_fifo_dst_rdy_n,
      RX_SOP_N       => rx_frame_fifo_sop_n,
      RX_EOP_N       => rx_frame_fifo_eop_n,
      RX_SOF_N       => rx_frame_fifo_sof_n,
      RX_EOF_N       => rx_frame_fifo_eof_n,
     
      -- Read interface
      TX_DATA        => tx_frame_fifo_data,
      TX_REM         => tx_frame_fifo_rem,
      TX_SRC_RDY_N   => tx_frame_fifo_src_rdy_n, 
      TX_DST_RDY_N   => tx_frame_fifo_dst_rdy_n,
      TX_SOP_N       => tx_frame_fifo_sop_n,
      TX_EOP_N       => tx_frame_fifo_eop_n,
      TX_SOF_N       => tx_frame_fifo_sof_n,
      TX_EOF_N       => tx_frame_fifo_eof_n,
      
      -- FIFO state signals
      LSTBLK         => open,
      FULL           => open,
      EMPTY          => open,
      STATUS         => open,
      FRAME_RDY      => open
   );


   rx_header_fifo_data        <= "0000000" & (NOT sig_rx_eof_n);
   rx_header_fifo_rem         <= "";
   rx_header_fifo_sop_n       <= '0';
   rx_header_fifo_eop_n       <= '1';
   rx_header_fifo_sof_n       <= '0';
   rx_header_fifo_eof_n       <= '1';
   rx_header_fifo_src_rdy_n   <= rx_frame_fifo_dst_rdy_n OR  sig_rx_src_rdy_n
                                 OR sig_rx_eop_n;

   -- --------------- HEADER FIFO INSTANCE ----------------------------------
   header_fifo : entity work.fl_fifo
   generic map(
      DATA_WIDTH  => HEADER_WIDTH,
      USE_BRAMS   => false,
      ITEMS       => 16,
      PARTS       => 1
   )
   port map(
      RESET       => RESET,
      CLK         => CLK,

      -- Write interface
      RX_DATA        => rx_header_fifo_data,
      RX_REM         => rx_header_fifo_rem,
      RX_SRC_RDY_N   => rx_header_fifo_src_rdy_n, 
      RX_DST_RDY_N   => rx_header_fifo_dst_rdy_n,
      RX_SOP_N       => rx_header_fifo_sop_n,
      RX_EOP_N       => rx_header_fifo_eop_n,
      RX_SOF_N       => rx_header_fifo_sof_n,
      RX_EOF_N       => rx_header_fifo_eof_n,
     
      -- Read interface
      TX_DATA        => tx_header_fifo_data,
      TX_REM         => tx_header_fifo_rem,
      TX_SRC_RDY_N   => tx_header_fifo_src_rdy_n, 
      TX_DST_RDY_N   => tx_header_fifo_dst_rdy_n,
      TX_SOP_N       => tx_header_fifo_sop_n,
      TX_EOP_N       => tx_header_fifo_eop_n,
      TX_SOF_N       => tx_header_fifo_sof_n,
      TX_EOF_N       => tx_header_fifo_eof_n,
      
      -- FIFO state signals
      LSTBLK         => open,
      FULL           => open,
      EMPTY          => open,
      STATUS         => open,
      FRAME_RDY      => open
   );


   header_data(63 downto 56) <= X"00";
   header_data(55 downto 48) <= tx_header_fifo_data;
   header_data(47 downto 40) <= X"00";
   header_data(39 downto 32) <= DATA_TYPE;
   header_data(31 downto 24) <= X"00";
   header_data(23 downto 16) <= X"00";
   header_data(15 downto  8) <= FRAMELINK_PROTOCOL_ID;
   header_data( 7 downto  0) <= ENDPOINT_TAG;
   header_rem  <= (others => '1');

   -- output signal multiplexer
   mux3 : process (sending_header, tx_frame_fifo_data, header_data,
      tx_frame_fifo_rem, header_rem, tx_frame_fifo_eof_n, tx_frame_fifo_eop_n,
      tx_frame_fifo_src_rdy_n, tx_header_fifo_src_rdy_n, sig_tx_dst_rdy_n)
   begin
      sig_tx_data  <= tx_frame_fifo_data;
      sig_tx_rem   <= tx_frame_fifo_rem;
      sig_tx_sof_n <= '1';
      sig_tx_sop_n <= '1';
      sig_tx_eof_n <= tx_frame_fifo_eof_n;
      sig_tx_eop_n <= tx_frame_fifo_eop_n;
      sig_tx_src_rdy_n <= tx_frame_fifo_src_rdy_n;
      tx_frame_fifo_dst_rdy_n  <= '1';
      tx_header_fifo_dst_rdy_n <= '1';


      case sending_header is
         when '0'    => sig_tx_data  <= tx_frame_fifo_data;
                        sig_tx_rem   <= tx_frame_fifo_rem;
                        sig_tx_sof_n <= '1';
                        sig_tx_sop_n <= '1';
                        sig_tx_eof_n <= tx_frame_fifo_eof_n;
                        sig_tx_eop_n <= tx_frame_fifo_eop_n;
                        sig_tx_src_rdy_n <= tx_frame_fifo_src_rdy_n;
                        tx_frame_fifo_dst_rdy_n  <= sig_tx_dst_rdy_n;

         when '1'    => sig_tx_data  <= header_data; 
                        sig_tx_rem   <= header_rem; 
                        sig_tx_sof_n <= '0';
                        sig_tx_sop_n <= '0';
                        sig_tx_eof_n <= '1';
                        sig_tx_eop_n <= '1';
                        sig_tx_src_rdy_n <= tx_header_fifo_src_rdy_n;
                        tx_header_fifo_dst_rdy_n  <= sig_tx_dst_rdy_n;

         when others => null;
      end case;   
   end process;

   -- ---------------------- CONTROL FSM ------------------------------------
   -- state register logic
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
   fsm_next_state_logic : process (state_reg, tx_header_fifo_src_rdy_n,
      tx_frame_fifo_src_rdy_n, sig_tx_dst_rdy_n, tx_frame_fifo_eof_n)
   begin
     state_next <= state_reg;  

     case state_reg is
        when header_state => 
           if (tx_header_fifo_src_rdy_n = '0' and sig_tx_dst_rdy_n = '0') then 
              state_next <= not_header_state;
           end if;
        when not_header_state =>
           if (tx_frame_fifo_src_rdy_n = '0' and sig_tx_dst_rdy_n = '0' and
              tx_frame_fifo_eof_n = '0') then  
              state_next <= header_state;  
           end if;   
        end case;      
   end process;

   -- Moore output logic
   moore_output : process (state_reg)
   begin
      sending_header <= '1'; -- default value
      case state_reg is
         when header_state     => sending_header <= '1';
         when not_header_state => sending_header <= '0';
      end case;   
   end process; 
   
   -- map output ports
   TX_DATA         <= sig_tx_data;
   TX_REM          <= sig_tx_rem;
   TX_SOF_N        <= sig_tx_sof_n;
   TX_EOF_N        <= sig_tx_eof_n;
   TX_SOP_N        <= sig_tx_sop_n;
   TX_EOP_N        <= sig_tx_eop_n;
   TX_SRC_RDY_N    <= sig_tx_src_rdy_n;
   sig_tx_dst_rdy_n<= TX_DST_RDY_N;


end architecture;
