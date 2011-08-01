--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Validity Checker
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
entity FL_VAL_CHECKER is
   generic
   (
      OUT_DATA_WIDTH : integer
   );
   port
   (
      -- probe interface
      PR_CLK         : in  std_logic;
      PR_RESET       : in  std_logic;

      PR_SRC_RDY_N   : in  std_logic;
      PR_DST_RDY_N   : in  std_logic;
      PR_SOP_N       : in  std_logic;
      PR_EOP_N       : in  std_logic;
      PR_SOF_N       : in  std_logic;
      PR_EOF_N       : in  std_logic;
      
      -- output interface
      OUT_CLK        : in  std_logic;
      OUT_RESET      : in  std_logic;

      OUT_DATA       : out std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      OUT_REM        : out std_logic_vector(log2(OUT_DATA_WIDTH/8) - 1 downto 0);
      OUT_SRC_RDY_N  : out std_logic;
      OUT_DST_RDY_N  : in  std_logic;
      OUT_SOP_N      : out std_logic;
      OUT_EOP_N      : out std_logic;
      OUT_SOF_N      : out std_logic;
      OUT_EOF_N      : out std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of FL_VAL_CHECKER is


-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

begin


end architecture;

