--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    Signal Observer's Frame Sender
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
entity FRAME_SENDER is

   generic
   (
      -- data width
      DATA_WIDTH  : integer := 64
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input FrameLink interface
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;

      -- signal for sending next frame
      RX_SEND_NEXT   :  in std_logic;
      
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
architecture arch of FRAME_SENDER is

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================


-- input signals
signal sig_rx_fl_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_rx_fl_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal sig_rx_fl_sof_n     : std_logic;
signal sig_rx_fl_sop_n     : std_logic;
signal sig_rx_fl_eof_n     : std_logic;
signal sig_rx_fl_eop_n     : std_logic;
signal sig_rx_fl_src_rdy_n : std_logic;
signal sig_rx_fl_dst_rdy_n : std_logic;

signal sig_rx_send_next    : std_logic;

-- output signals
signal sig_tx_fl_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_tx_fl_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal sig_tx_fl_sof_n     : std_logic;
signal sig_tx_fl_sop_n     : std_logic;
signal sig_tx_fl_eof_n     : std_logic;
signal sig_tx_fl_eop_n     : std_logic;
signal sig_tx_fl_src_rdy_n : std_logic;
signal sig_tx_fl_dst_rdy_n : std_logic;

-- is_sending register
signal reg_is_sending      : std_logic;
signal reg_is_sending_set  : std_logic;
signal reg_is_sending_clr  : std_logic;


begin

   -- mapping of input signal
   sig_rx_fl_data             <= RX_DATA;
   sig_rx_fl_rem              <= RX_REM;
   sig_rx_fl_sof_n            <= RX_SOF_N;
   sig_rx_fl_sop_n            <= RX_SOP_N;
   sig_rx_fl_eof_n            <= RX_EOF_N;
   sig_rx_fl_eop_n            <= RX_EOP_N;
   sig_rx_fl_src_rdy_n        <= RX_SRC_RDY_N;
   RX_DST_RDY_N               <= sig_rx_fl_dst_rdy_n;

   sig_rx_send_next           <= RX_SEND_NEXT;

   -- mapping of ``data'' signals
   sig_tx_fl_data             <= sig_rx_fl_data;
   sig_tx_fl_rem              <= sig_rx_fl_rem;
   sig_tx_fl_sof_n            <= sig_rx_fl_sof_n;
   sig_tx_fl_sop_n            <= sig_rx_fl_sop_n;
   sig_tx_fl_eof_n            <= sig_rx_fl_eof_n;
   sig_tx_fl_eop_n            <= sig_rx_fl_eop_n;

   -- mapping of ``control'' signals
   sig_rx_fl_dst_rdy_n  <= sig_tx_fl_dst_rdy_n OR (NOT reg_is_sending);
   sig_tx_fl_src_rdy_n  <= sig_rx_fl_src_rdy_n OR (NOT reg_is_sending);


   -- is_sending register input signals
   reg_is_sending_clr <= NOT (sig_rx_fl_dst_rdy_n OR sig_tx_fl_src_rdy_n OR
      sig_rx_fl_eof_n);
   reg_is_sending_set <= sig_rx_send_next;

   -- the is_sending register
   reg_is_sending_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_is_sending <= '0';
         elsif (reg_is_sending_set = '1') then
            reg_is_sending <= '1';
         elsif (reg_is_sending_clr = '1') then
            reg_is_sending <= '0';
         end if;
      end if;
   end process;


   -- mapping of output signals
   TX_DATA             <= sig_tx_fl_data;
   TX_REM              <= sig_tx_fl_rem;
   TX_SOF_N            <= sig_tx_fl_sof_n;
   TX_SOP_N            <= sig_tx_fl_sop_n;
   TX_EOF_N            <= sig_tx_fl_eof_n;
   TX_EOP_N            <= sig_tx_fl_eop_n;
   TX_SRC_RDY_N        <= sig_tx_fl_src_rdy_n;
   sig_tx_fl_dst_rdy_n <= TX_DST_RDY_N;

end architecture;
