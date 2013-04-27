-- 
-- Output side in hw part of verification environment
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
      CORE_TYPE          : core_type := core_fifo --?? core_codix?
   );
   port
   (
      CLK                :  in std_logic;
      RESET              :  in std_logic; --?? RST_N codix

      -- input interface - Codix processor
      dbg_mode_mem      : out std_logic;
      dbg_mode_mem_Q0   : in  std_logic_vector(31 downto 0);
      dbg_mode_mem_RA0  : out std_logic_vector(18 downto 0);
      dbg_mode_mem_RE0  : out std_logic;
      dbg_mode_mem_RSC0 : out std_logic_vector(2 downto 0);
      dbg_mode_mem_RSI0 : out std_logic_vector(1 downto 0);
      dbg_mode_regs     : out std_logic;
      dbg_mode_regs_Q0  : in  std_logic_vector(31 downto 0);
      dbg_mode_regs_RA0 : out std_logic_vector(4 downto 0);
      dbg_mode_regs_RE0 : out std_logic;
      port_halt         : in  std_logic;
      port_output       : in  std_logic_vector(31 downto 0);
      port_output_en    : in  std_logic;

      -- output interface - framelink binder output interface
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
