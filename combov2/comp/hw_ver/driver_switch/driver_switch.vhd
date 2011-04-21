-- -----------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    Driver Switch
-- Description: 
-- Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
-- Date:         15.4.2011 
-- -----------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity DRIVER_SWITCH is
   generic
   (
      -- input FrameLink data width
      INPUT_FL_DATA_WIDTH   : integer := 128;
      -- output FrameLink data width
      OUTPUT_FL_DATA_WIDTH  : integer := 128
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- input FrameLink interface
      RX_DATA        : in  std_logic_vector(INPUT_FL_DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(INPUT_FL_DATA_WIDTH/8) - 1 downto 0);
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      
      -- output FrameLink interface  !!! zatial len k jednemu driveru
      TX_DATA        : out std_logic_vector(OUTPUT_FL_DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(OUTPUT_FL_DATA_WIDTH/8) - 1 downto 0);
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic
   );
end entity FL_NETCOPE_ADDER;