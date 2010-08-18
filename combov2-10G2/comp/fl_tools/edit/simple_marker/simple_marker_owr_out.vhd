-- simple_marker_owr_out.vhd: Implementation of simple FrameLink marker
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity SIMPLE_FL_MARKER_OWR_OUT is
   generic (
      DATA_WIDTH : integer := 32;
      OFFSET     : integer := 0;
      MARK_SIZE  : integer := 4;
      MARK_WORDS : integer := 1
   );
   port (
      MARK    : in std_logic_vector(MARK_SIZE*8-1 downto 0);
      MARK_POS : in std_logic_vector(max(log2(MARK_WORDS)-1, 0) downto 0);
      IS_MARKING : in std_logic;

      RX_DATA : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM  : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

      TX_DATA : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM  : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0)
   );
end entity;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

architecture impl of SIMPLE_FL_MARKER_OWR_OUT is

   constant MARK_WIDTH : integer := MARK_SIZE*8;
   constant DATA_SIZE : integer := DATA_WIDTH/8;
   --
   -- padding from begin of the first mark part (MARK_PART), aligns the mask
   --
   constant BEG_PAD : integer := (OFFSET mod DATA_SIZE) * 8;
   --
   -- padding after mark, aligns the mask
   --
   constant END_PAD : integer := ((DATA_WIDTH - ((BEG_PAD + MARK_WIDTH) mod DATA_WIDTH)) mod DATA_WIDTH); 

   -- size of mark at the begin
   constant MARK_BEG : integer := (DATA_WIDTH - BEG_PAD) mod DATA_WIDTH;
   -- size of mark at the end
   constant MARK_END : integer := (DATA_WIDTH - END_PAD) mod DATA_WIDTH;
   -- size of mark in the middle
   constant MARK_MID : integer := MARK_WIDTH - MARK_BEG - MARK_END;

   constant MUX_DATA_WIDTH : integer := MARK_WIDTH + BEG_PAD + END_PAD + DATA_WIDTH;
   constant MUX_SEL_WIDTH : integer := log2(MUX_DATA_WIDTH/DATA_WIDTH);

   -- input to MUX
   -- |       one or more of these     | always  |
   -- | MARK_BEG | MARK_MID | MARK_END | RX_DATA |
   signal mux_data : std_logic_vector(MUX_DATA_WIDTH - 1 downto 0);
   signal mux_sel : std_logic_vector(MUX_SEL_WIDTH - 1 downto 0);

begin

-- ----------------------------------------------------------------------------
--                        Output generic multiplexor
-- ----------------------------------------------------------------------------

   mux : entity work.GEN_MUX
   generic map (
      DATA_WIDTH => DATA_WIDTH,
      MUX_WIDTH => MUX_DATA_WIDTH/DATA_WIDTH
   )
   port map (
      DATA_IN => mux_data,
      SEL => mux_sel,
      DATA_OUT => TX_DATA
   );
   
   -- whem not marking, send RX_DATA directly, otherwise pass MARK
   mux_sel <= ext(MARK_POS, MUX_SEL_WIDTH) when IS_MARKING = '1' else 
              conv_std_logic_vector(MUX_DATA_WIDTH/DATA_WIDTH - 1, MUX_SEL_WIDTH);
   
   TX_REM <= RX_REM;


-- ----------------------------------------------------------------------------
--                      Counting of DATA_IN to multiplexor
-- ----------------------------------------------------------------------------

   -- statically counted:
   fill_mux_data : process(RX_DATA, MARK)
   begin
      if MARK_BEG > 0 then
         --                      target               optional
         -- mux_data: | BEG_PAD BEG_PAD BEG_MARK |       ...      |
         --           | RX_DATA RX_DATA MARK     |       ...      |
         mux_data(BEG_PAD - 1 downto 0) <= RX_DATA(BEG_PAD-1 downto 0);
         mux_data(DATA_WIDTH - 1 downto BEG_PAD) <= MARK(MARK_BEG - 1 downto 0);
      end if;
      
      if MARK_MID > 0 then
         -- must be of that size (else it is wrong coded)
         assert MARK_MID mod DATA_WIDTH = 0 report "Wrong MARK_MID: " & integer'image(MARK_MID) severity error;

         --                      optional                   target                  optional  
         -- mux_data: | BEG_PAD BEG_PAD BEG_MARK | MARK_MID MARK_MID MARK_MID |        ...      |
         --           | RX_DATA RX_DATA MARK     | MARK     MARK     MARK     |        ...      |
         mux_data(BEG_PAD + MARK_BEG + MARK_MID - 1 downto BEG_PAD + MARK_BEG) 
            <= MARK(MARK_BEG + MARK_MID - 1 downto MARK_BEG);
      end if;

      if MARK_END > 0 then
         --                      optional                   optional                   target
         -- mux_data: | BEG_PAD BEG_PAD BEG_MARK | MARK_MID MARK_MID MARK_MID | MARK_END END_PAD END_PAD |
         --           | RX_DATA RX_DATA MARK     | MARK     MARK     MARK     | MARK     RX_DATA RX_DATA |
         mux_data(BEG_PAD + MARK_WIDTH + END_PAD - 1 downto BEG_PAD + MARK_WIDTH)
            <= RX_DATA(DATA_WIDTH-1 downto DATA_WIDTH - END_PAD);
         mux_data(BEG_PAD + MARK_WIDTH - 1 downto BEG_PAD + MARK_WIDTH - MARK_END) 
            <= MARK(MARK_WIDTH-1 downto MARK_WIDTH - MARK_END);
      end if;

      -- append RX_DATA (always)
      mux_data(MUX_DATA_WIDTH-1 downto MUX_DATA_WIDTH - DATA_WIDTH) <= RX_DATA;
   end process;

end architecture;
