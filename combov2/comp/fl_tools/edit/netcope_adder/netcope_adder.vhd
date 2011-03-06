-- fl_component.vhd: Popis komponenty 
-- Copyright (C) 2011
-- Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity FL_NETCOPE_ADDER is

   generic
   (
      -- data width
      DATA_WIDTH    : integer := 128
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- write interface
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      
      -- read interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic
   );
end entity FL_NETCOPE_ADDER;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of FL_NETCOPE_ADDER is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================
type state_type is (header_state, not_header_state);

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================
constant HEADER_WIDTH : integer := 32;
constant FRAME_WIDTH  : integer := DATA_WIDTH;

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================
-- header RX signals ---------------------------------------------------------
signal sig_part_width          : std_logic_vector(HEADER_WIDTH-1 downto 0); --?
signal sig_part_sum            : std_logic_vector(HEADER_WIDTH-1 downto 0); --?
signal sig_reg_out             : std_logic_vector(HEADER_WIDTH-1 downto 0); --?
signal sig_header_rx_data      : std_logic_vector(HEADER_WIDTH-1 downto 0);
signal sig_rx_src_and_dst_rdy  : std_logic;
signal sig_header_rx_src_rdy_n : std_logic; 
signal sig_header_rx_dst_rdy_n : std_logic; 
signal out_rx_dst_rdy_n        : std_logic;
-- header TX signals ---------------------------------------------------------
signal sig_header_tx_data      : std_logic_vector(HEADER_WIDTH-1 downto 0);
signal sig_ful_header_tx_data  : std_logic_vector(FRAME_WIDTH-1 downto 0);
signal sig_header_tx_src_rdy_n : std_logic;
signal sig_header_tx_dst_rdy_n : std_logic;
signal sig_header_tx_sop_n     : std_logic;
signal sig_header_tx_eop_n     : std_logic;
-- frame RX signals ----------------------------------------------------------
signal sig_frame_rx_dst_rdy_n  : std_logic;
-- frame TX signals ----------------------------------------------------------
signal sig_frame_tx_data       : std_logic_vector(FRAME_WIDTH-1 downto 0);
signal sig_frame_tx_rem        : std_logic_vector(log2(FRAME_WIDTH/8)-1 downto 0);
signal sig_frame_tx_src_rdy_n  : std_logic;
signal sig_frame_tx_dst_rdy_n  : std_logic;
signal sig_frame_tx_sop_n      : std_logic; 
signal sig_frame_tx_eop_n      : std_logic;
signal sig_frame_tx_eof_n      : std_logic;
-- FSM signals ---------------------------------------------------------------
signal state_reg, state_next   : state_type;
signal is_header               : std_logic;

-- ==========================================================================
--                           ARCHITECTURE BODY
-- ==========================================================================
begin
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
      RX_DATA        => sig_header_rx_data,
      RX_REM         => (others => '0'),
      RX_SRC_RDY_N   => sig_header_rx_src_rdy_n, 
      RX_DST_RDY_N   => sig_header_rx_dst_rdy_n,
      RX_SOP_N       => '0',
      RX_EOP_N       => '0',
      RX_SOF_N       => '0',
      RX_EOF_N       => '0',
     
      -- Read interface
      TX_DATA        => sig_header_tx_data,
      TX_REM         => open,
      TX_SRC_RDY_N   => sig_header_tx_src_rdy_n, 
      TX_DST_RDY_N   => sig_header_tx_dst_rdy_n,
      TX_SOP_N       => sig_header_tx_sop_n,       
      TX_EOP_N       => sig_header_tx_eop_n,
      TX_SOF_N       => open,
      TX_EOF_N       => open,
      
      -- FIFO state signals
      LSTBLK         => open,
      FULL           => open,
      EMPTY          => open,
      STATUS         => open,
      FRAME_RDY      => open
   );
   
   -- --------------- FRAME FIFO INSTANCE -----------------------------------
   frame_fifo : entity work.fl_fifo
   generic map(
      DATA_WIDTH  => FRAME_WIDTH,
      USE_BRAMS   => true,
      ITEMS       => 16,
      PARTS       => 1
   )
   port map (
      RESET       => RESET,
      CLK         => CLK,

      -- Write interface
      RX_DATA        => RX_DATA,
      RX_REM         => RX_REM,
      RX_SRC_RDY_N   => RX_SRC_RDY_N, 
      RX_DST_RDY_N   => sig_frame_rx_dst_rdy_n,
      RX_SOP_N       => RX_SOP_N,
      RX_EOP_N       => RX_EOP_N,
      RX_SOF_N       => RX_SOF_N,
      RX_EOF_N       => RX_EOF_N,
     
      -- Read interface
      TX_DATA        => sig_frame_tx_data,
      TX_REM         => sig_frame_tx_rem,
      TX_SRC_RDY_N   => sig_frame_tx_src_rdy_n,
      TX_DST_RDY_N   => sig_frame_tx_dst_rdy_n,
      TX_SOP_N       => sig_frame_tx_sop_n, 
      TX_EOP_N       => sig_frame_tx_eop_n,
      TX_SOF_N       => open,
      TX_EOF_N       => sig_frame_tx_eof_n,
      
      -- FIFO state signals
      LSTBLK         => open,
      FULL           => open,
      EMPTY          => open,
      STATUS         => open,
      FRAME_RDY      => open
   );

   -- ==================== RX SIDE IMPLEMENTATION ====================
   sig_rx_src_and_dst_rdy  <= not(RX_SRC_RDY_N or out_rx_dst_rdy_n);
   sig_header_rx_src_rdy_n <= not((not RX_EOF_N) and sig_rx_src_and_dst_rdy);
   
   mux1 : process (RX_EOF_N, RX_REM)
   begin
      sig_part_width <= (others => '0');

      case RX_EOF_N is
         when '0'    => sig_part_width <= ((HEADER_WIDTH-1) downto (log2(DATA_WIDTH/8)+1) => '0') & (("0" & RX_REM) + 1);
         when '1'    => sig_part_width <=
            conv_std_logic_vector((DATA_WIDTH/8), HEADER_WIDTH);
         when others => null;   
      end case;   
   end process;
   
   mux2 : process (RX_SOF_N, sig_reg_out) 
   begin
      sig_part_sum <= (others => '0');

      case RX_SOF_N is
         when '0'    => sig_part_sum <= (others => '0'); 
         when '1'    => sig_part_sum <= sig_reg_out;
         when others => null;
      end case;   
   end process;
   
   sig_header_rx_data <= sig_part_sum + sig_part_width;
   
   reg : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then 
            sig_reg_out <= (others => '0');
         elsif (sig_rx_src_and_dst_rdy = '1') then
            sig_reg_out <= sig_header_rx_data;   
         end if;   
      end if;
   end process; 
   
   out_rx_dst_rdy_n <= sig_header_rx_dst_rdy_n or sig_frame_rx_dst_rdy_n;
   RX_DST_RDY_N <= out_rx_dst_rdy_n;
   
   -- ==================== TX SIDE IMPLEMENTATION ====================
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
   fsm_next_state_logic : process (state_reg, sig_header_tx_src_rdy_n, sig_frame_tx_src_rdy_n, TX_DST_RDY_N)
   begin
     state_next <= state_reg;  

     case state_reg is
        when header_state => 
           if (sig_header_tx_src_rdy_n = '0' and TX_DST_RDY_N = '0') then 
              state_next <= not_header_state;
           end if;
        when not_header_state =>
           if (sig_frame_tx_src_rdy_n = '0' and TX_DST_RDY_N = '0' and sig_frame_tx_eof_n = '0') then  
              state_next <= header_state;  
           end if;   
        end case;      
   end process;
   
   -- Moore output logic
   moore_output : process (state_reg)
   begin
      is_header <= '1'; -- default value
      case state_reg is
         when header_state     => is_header <= '1';
         when not_header_state => is_header <= '0';
      end case;   
   end process moore_output; 
   
   -- conversion to 16B from 4B
   sig_ful_header_tx_data <= ((FRAME_WIDTH-1) downto HEADER_WIDTH => '0') & sig_header_tx_data;
   
   mux3 : process (is_header, sig_ful_header_tx_data, sig_frame_tx_data)
   begin
      TX_DATA <= sig_ful_header_tx_data;

      case is_header is
         when '0'    => TX_DATA <= sig_frame_tx_data;
         when '1'    => TX_DATA <= sig_ful_header_tx_data; 
         when others => null;
      end case;   
   end process;
   
   mux4 : process (is_header, sig_frame_tx_rem)
   begin
      TX_REM <= sig_frame_tx_rem;

      case is_header is
         when '0'    => TX_REM <= sig_frame_tx_rem;
         when '1'    => TX_REM <= conv_std_logic_vector(3, log2(DATA_WIDTH/8));
         when others => null;
      end case;   
   end process;
   
   mux5 : process (is_header, sig_header_tx_src_rdy_n, sig_frame_tx_src_rdy_n)
   begin
      TX_SRC_RDY_N <= sig_header_tx_src_rdy_n; 

      case is_header is
         when '0'    => TX_SRC_RDY_N <= sig_frame_tx_src_rdy_n;
         when '1'    => TX_SRC_RDY_N <= sig_header_tx_src_rdy_n; 
         when others => null;
      end case;   
   end process;
   
   mux6 : process (is_header, sig_header_tx_sop_n, sig_frame_tx_sop_n)
   begin
      TX_SOP_N <= sig_header_tx_sop_n; 

      case is_header is
         when '0'    => TX_SOP_N <= sig_frame_tx_sop_n;
         when '1'    => TX_SOP_N <= sig_header_tx_sop_n; 
         when others => null;
      end case;   
   end process;
   
   mux7 : process (is_header, sig_header_tx_eop_n, sig_frame_tx_eop_n)
   begin
      TX_EOP_N <= sig_header_tx_eop_n; 

      case is_header is
         when '0'    => TX_EOP_N <= sig_frame_tx_eop_n;
         when '1'    => TX_EOP_N <= sig_header_tx_eop_n; 
         when others => null;
      end case;   
   end process;
   
   sig_header_tx_dst_rdy_n <= not(is_header) or TX_DST_RDY_N;
   sig_frame_tx_dst_rdy_n  <= is_header or TX_DST_RDY_N;
   TX_SOF_N <= not(is_header);
   TX_EOF_N <= sig_frame_tx_eof_n or is_header;

end architecture;
