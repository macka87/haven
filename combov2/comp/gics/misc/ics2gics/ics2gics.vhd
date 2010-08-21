--
-- ics2gics.vhd: ICS/GICS headers converter
-- Copyright (C) 2009 CESNET
-- Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--                             ENTITY DECLARATION                            --
-- ----------------------------------------------------------------------------

entity ICS2GICS is
   generic(
      -- Data Width (min 16)
      DATA_WIDTH        : integer := 64
   );   
   port(
      -- Common interface -----------------------------------------------------
      CLK               : in std_logic;
      RESET             : in std_logic;
      
      -- ICS interface --------------------------------------------------------
      ICS_IN_DATA         : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      ICS_IN_SOF_N        : in  std_logic;
      ICS_IN_EOF_N        : in  std_logic;
      ICS_IN_SRC_RDY_N    : in  std_logic;
      ICS_IN_DST_RDY_N    : out std_logic;
      
      ICS_OUT_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      ICS_OUT_SOF_N       : out std_logic;
      ICS_OUT_EOF_N       : out std_logic;
      ICS_OUT_SRC_RDY_N   : out std_logic;
      ICS_OUT_DST_RDY_N   : in  std_logic;
      
      -- GICS interface -------------------------------------------------------
      GICS_IN_DATA         : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      GICS_IN_SOF_N        : in  std_logic;
      GICS_IN_EOF_N        : in  std_logic;
      GICS_IN_SRC_RDY_N    : in  std_logic;
      GICS_IN_DST_RDY_N    : out std_logic;
      
      GICS_OUT_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      GICS_OUT_SOF_N       : out std_logic;
      GICS_OUT_EOF_N       : out std_logic;
      GICS_OUT_SRC_RDY_N   : out std_logic;
      GICS_OUT_DST_RDY_N   : in  std_logic
   );
end entity ICS2GICS;


-- ----------------------------------------------------------------------------
--                          ARCHITECTURE DECLARATION                         --
-- ----------------------------------------------------------------------------

architecture ics2gics_arch of ICS2GICS is

  signal gics_len_type  : std_logic_vector(15 downto 0);
  signal ics_len_type   : std_logic_vector(15 downto 0);
  
begin
  
  -- ---------------------------- ICS -> GICS ---------------------------------
  
  GICS_OUT_DATA(DATA_WIDTH-1 downto 16) <= ICS_IN_DATA(DATA_WIDTH-1 downto 16);
  GICS_OUT_SOF_N                        <= ICS_IN_SOF_N;
  GICS_OUT_EOF_N                        <= ICS_IN_EOF_N;
  GICS_OUT_SRC_RDY_N                    <= ICS_IN_SRC_RDY_N;
  ICS_IN_DST_RDY_N                      <= GICS_OUT_DST_RDY_N;
  
  gics_len_type <= ICS_IN_DATA(11 downto 0) & ICS_IN_DATA(15 downto 13) & 
                   (not ICS_IN_DATA(12) or ICS_IN_DATA(14));
  
  with ICS_IN_SOF_N select
     GICS_OUT_DATA(15 downto 0) <= ICS_IN_DATA(15 downto 0) when '1',
                                   gics_len_type            when others;
  
  -- ---------------------------- GICS -> ICS ---------------------------------
  
  ICS_OUT_DATA(DATA_WIDTH-1 downto 16) <= GICS_IN_DATA(DATA_WIDTH-1 downto 16);
  ICS_OUT_SOF_N                        <= GICS_IN_SOF_N;
  ICS_OUT_EOF_N                        <= GICS_IN_EOF_N;
  ICS_OUT_SRC_RDY_N                    <= GICS_IN_SRC_RDY_N;
  GICS_IN_DST_RDY_N                    <= ICS_OUT_DST_RDY_N;
  
  ics_len_type <= GICS_IN_DATA(3 downto 1) &
                  (not GICS_IN_DATA(0) or GICS_IN_DATA(2)) &
                  GICS_IN_DATA(15 downto 4);
  
  with GICS_IN_SOF_N select
     ICS_OUT_DATA(15 downto 0) <= GICS_IN_DATA(15 downto 0) when '1',
                                  ics_len_type              when others;
  
end ics2gics_arch;
