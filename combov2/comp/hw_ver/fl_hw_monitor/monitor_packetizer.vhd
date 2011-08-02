--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    Smart FrameLink Monitor input packetizer 
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
entity MONITOR_PACKETIZER is

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

begin

   -- Assertions
   assert (DATA_WIDTH = 64)
      report "Unsupported OUT_DATA_WIDTH!"
      severity failure;

   TX_DATA         <= RX_DATA;
   TX_REM          <= RX_REM;
   TX_SOF_N        <= RX_SOF_N;
   TX_EOF_N        <= RX_EOF_N;
   TX_SOP_N        <= RX_SOP_N;
   TX_EOP_N        <= RX_EOP_N;
   TX_SRC_RDY_N    <= RX_SRC_RDY_N;
   RX_DST_RDY_N    <= TX_DST_RDY_N;


end architecture;
