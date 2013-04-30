-- verification_core_ent.vhd: Entity of verification core
-- Author(s): Martin Funiak - xfunia00(at)stud.fit.vutbr.cz
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
--use work.math_pack.all;

-- HAVEN constants
use work.haven_const.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity verification_core is
   generic
   (
      -- data width
      FL_DATA_WIDTH      : integer := 64;
      CODIX_DATA_WIDTH   : integer := 32; 

      -- the CORE_TYPE generic specifies the verified unit in the core
      CORE_TYPE          : core_type := core_fifo  --??
   );
   port
   (
      CLK                :  in std_logic;
      RESET              :  in std_logic;

      -- input interface - framelink
      RX_DATA            :  in std_logic_vector(FL_DATA_WIDTH-1 downto 0);
      RX_REM             :  in std_logic_vector(2 downto 0);
      RX_SOF_N           :  in std_logic;
      RX_EOF_N           :  in std_logic;
      RX_SOP_N           :  in std_logic;
      RX_EOP_N           :  in std_logic;
      RX_SRC_RDY_N       :  in std_logic;
      RX_DST_RDY_N       : out std_logic;

      DUT_RST_N          :  in std_logic;

      -- output interface - dut - codix
      port_error         : out std_logic_vector(31 downto 0);
      port_halt          : out std_logic;
      port_output        : out std_logic_vector(31 downto 0);
      port_output_en     : out std_logic
   );
end entity;
