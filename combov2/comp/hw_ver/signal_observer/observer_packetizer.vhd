--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    Signal Observer's Packetizer
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
entity OBSERVER_PACKETIZER is

   generic
   (
      -- data width
      DATA_WIDTH       : integer := 64;
      MAX_FRAME_LENGTH : integer := 4096;
      ENDPOINT_ID      : integer
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_READ_NEXT   : out std_logic;
      RX_VALID       : in  std_logic;
      
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
architecture arch of OBSERVER_PACKETIZER is

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================


-- output signals
signal sig_tx_fl_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_tx_fl_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal sig_tx_fl_sof_n     : std_logic;
signal sig_tx_fl_sop_n     : std_logic;
signal sig_tx_fl_eof_n     : std_logic;
signal sig_tx_fl_eop_n     : std_logic;
signal sig_tx_fl_src_rdy_n : std_logic;
signal sig_tx_fl_dst_rdy_n : std_logic;


begin

   assert (DATA_WIDTH = 64)
      report "Unsupported DATA_WIDTH!"
      severity failure;

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
