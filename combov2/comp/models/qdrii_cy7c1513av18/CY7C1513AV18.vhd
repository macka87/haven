-- CY7C1513AV18.vhd: CY7C1513AV18 VHDL cover of Verilog model
-- Copyright (C) 2009 CESNET
-- Author(s): Michal Kajan kajan@liberouter.org
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
-- 1. Redistributions of source code must retain the above copyright
--    notice, this list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright
--    notice, this list of conditions and the following disclaimer in
--    the documentation and/or other materials provided with the
--    distribution.
-- 3. Neither the name of the Company nor the names of its contributors
--    may be used to endorse or promote products derived from this
--    software without specific prior written permission.
--
-- This software is provided ``as is'', and any express or implied
-- warranties, including, but not limited to, the implied warranties of
-- merchantability and fitness for a particular purpose are disclaimed.
-- In no event shall the company or contributors be liable for any
-- direct, indirect, incidental, special, exemplary, or consequential
-- damages (including, but not limited to, procurement of substitute
-- goods or services; loss of use, data, or profits; or business
-- interruption) however caused and on any theory of liability, whether
-- in contract, strict liability, or tort (including negligence or
-- otherwise) arising in any way out of the use of this software, even
-- if advised of the possibility of such damage.
--
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity CY7C1513AV18 is
   port (
      -- data in
      D      : in  std_logic_vector(17 downto 0);

      -- data out
      Q      : inout std_logic_vector(17 downto 0);

      -- address
      SA     : in  std_logic_vector(19 downto 0);

      -- read enable
      R_N    : in  std_logic;

      -- write enable
      W_N    : in  std_logic;

      -- byte write select
      BW_N   : in  std_logic_vector(1 downto 0);


      K      : in  std_logic;
      K_N    : in  std_logic;
      C      : in  std_logic;
      C_N    : in  std_logic;
      CQ     : inout std_logic;
      CQ_N   : inout std_logic;

      -- DLL OFF
      DOFF_N : in  std_logic        
   );

end entity CY7C1513AV18;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture CY7C1513AV18_ARCH of CY7C1513AV18 is

   signal doff_neg : std_logic;

   -- Cypress QDR-II SRAM CY7C1513AV18 Burst Length Four memory model
   -- declaration
   component cyqdr2_b4
      port (
         -- JTAG purposes
         TCK   : in  std_logic;
         TMS   : in  std_logic;
         TDI   : in  std_logic;
         TDO   : out std_logic;
         
         -- data in
         D     : in  std_logic_vector(17 downto 0);

         -- clock inputs
         K     : in  std_logic;
         Kb    : in  std_logic;
         C     : in  std_logic;
         Cb    : in  std_logic;
         
         -- Read Port Select
         RPSb  : in  std_logic;

         -- Write Port Select
         WPSb  : in  std_logic;

         -- Byte Write Select
         BWS0b : in  std_logic;
         BWS1b : in  std_logic;

         -- Programmable Impedance Pin
         ZQ    : in  std_logic;

         -- DLL OFF
         DOFF  : in std_logic;

         -- Echo Clock Out
         CQ    : inout std_logic;
         CQb   : inout std_logic;

         -- data out
         Q     : inout std_logic_vector(17 downto 0);

         -- address input bus
         A     : in  std_logic_vector(19 downto 0)
      );
   end component;
   
begin

   CYPRESS_QDRII_MODEL_I : entity work.cyqdr2_b4
   port map (
         -- JTAG purposes
         TCK   => '0',
         TMS   => '0',
         TDI   => '0',
         TDO   => open,
         
         -- data in
         D     => D,

         -- clock inputs
         K     => K,
         Kb    => K_N,
         C     => C,
         Cb    => C_N,
         
         -- Read Port Select
         RPSb  => R_N,

         -- Write Port Select
         WPSb  => W_N,

         -- Byte Write Select
         BWS0b => BW_N(0),
         BWS1b => BW_N(1),

         -- Programmable Impedance Pin
         ZQ    => '0',

         CQ    => CQ,
         CQb   => CQ_N,

         DOFF  => doff_neg,

         -- data out
         Q     => Q,

         -- address input bus
         A     => SA            
   );
   
   doff_neg <= DOFF_N;

end architecture CY7C1513AV18_ARCH;
