--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    Erroneous FrameLink FIFO
-- Description:
-- Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
-- Date:         15.4.2011
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing the log2 function
use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity ERRONEOUS_FL_FIFO is
   generic(
      -- Data width
      -- Should be multiple of 16: only 16,32,64,128 supported
      DATA_WIDTH     : integer := 64;
      -- Number of items
      ITEMS          : integer := 16
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- write interface
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;

      -- read interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;

      -- FIFO state signals
      LSTBLK         : out std_logic;
      FULL           : out std_logic;
      EMPTY          : out std_logic;
      STATUS         : out std_logic_vector(STATUS_WIDTH-1 downto 0);
      FRAME_RDY      : out std_logic
   );
end entity;


-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture full of ERRONEOUS_FL_FIFO is

-- ==========================================================================
--                                   CONSTANTS
-- ==========================================================================

   constant FIFO_WIDTH : integer := DATA_WIDTH + log2(DATA_WIDTH/8) + 4;

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

   -- FIFO input signals
   signal rx_fifo_din    : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal rx_fifo_wr     : std_logic;
   signal rx_fifo_full   : std_logic;

   -- FIFO output signals
   signal tx_fifo_dout   : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal tx_fifo_rd     : std_logic;
   signal tx_fifo_empty  : std_logic;

-- ==========================================================================
--                                   COMPONENTS
-- ==========================================================================

   component sync_fifo_71
      port (
      clk: in std_logic;
      srst: in std_logic;
      din: in std_logic_vector(70 downto 0);
      wr_en: in std_logic;
      rd_en: in std_logic;
      dout: out std_logic_vector(70 downto 0);
      full: out std_logic;
      empty: out std_logic);
   end component;

begin

   -- Assertions
   assert(DATA_WIDTH == 64)
      report "Unsupported DATA_WIDTH!"
      severity failure;

   assert(ITEMS == 16)
      report "Unsupported ITEMS!"
      severity failure;

   -- mapping FIFO input ports
   rx_fifo_din(70 downto 7) <= RX_DATA;
   rx_fifo_din( 6 downto 4) <= RX_REM;
   rx_fifo_din(3)           <= RX_SOF_N;
   rx_fifo_din(2)           <= RX_SOP_N;
   rx_fifo_din(1)           <= RX_EOF_N;
   rx_fifo_din(0)           <= RX_EOP_N;

   -- --------------- Xilinx FIFO instance ----------------------------------
   fifo71 : sync_fifo_71
   port map (
      clk => CLK,
      srst => RESET,
      din => rx_fifo_din,
      wr_en => rx_fifo_wr,
      full => rx_fifo_full,
      dout => tx_fifo_dout,
      rd_en => tx_fifo_rd,
      empty => tx_fifo_empty
   );

   -- mapping FIFO output ports
   RX_DATA  <= rx_fifo_din(70 downto 7);
   RX_REM   <= rx_fifo_din( 6 downto 4);
   RX_SOF_N <= rx_fifo_din(3);
   RX_SOP_N <= rx_fifo_din(2);
   RX_EOF_N <= rx_fifo_din(1);
   RX_EOP_N <= rx_fifo_din(0);

end architecture;
