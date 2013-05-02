-- verification_engine_ent.vhd: Entity of verification engine
-- Author(s): Ondrej Lengal <ilengal@fit.vutbr.cz>
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity verification_engine is
   generic
   (
      -- data width 
      FL_DATA_WIDTH         : integer := 64;
      CODIX_DATA_WIDTH      : integer := 32
   );
   port
   (
      CLK                :  in std_logic;
      RESET              :  in std_logic;

      -- input interface
      RX_DATA            :  in std_logic_vector(FL_DATA_WIDTH-1 downto 0);
      RX_REM             :  in std_logic_vector(2 downto 0);
      RX_SOF_N           :  in std_logic;
      RX_EOF_N           :  in std_logic;
      RX_SOP_N           :  in std_logic;
      RX_EOP_N           :  in std_logic;
      RX_SRC_RDY_N       :  in std_logic;
      RX_DST_RDY_N       : out std_logic;

      -- output interface
      TX_DATA            : out std_logic_vector(FL_DATA_WIDTH-1 downto 0);
      TX_REM             : out std_logic_vector(2 downto 0);
      TX_SOF_N           : out std_logic;
      TX_EOF_N           : out std_logic;
      TX_SOP_N           : out std_logic;
      TX_EOP_N           : out std_logic;
      TX_SRC_RDY_N       : out std_logic;
      TX_DST_RDY_N       :  in std_logic
   );
end entity;
