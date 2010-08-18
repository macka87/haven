--
-- addr_splitter.vhd : Address Splitter
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
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

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                    ENTITY DECLARATION -- Address Splitter                 -- 
-- ----------------------------------------------------------------------------

entity ADDR_SPLITTER is 
   generic(
      INPUT_WIDTH  : integer:= 32;
      OUTPUT_WIDTH : integer:= 16      
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK       : in std_logic;
      
      -- Input interface ------------------------------------------------------
      ADDR_IN   : in std_logic_vector(INPUT_WIDTH-1 downto 0);
      ADDR_WE   : in std_logic;
      --ADDR_MX   : in std_logic_vector(max(log2(INPUT_WIDTH/OUTPUT_WIDTH),1)-1 downto 0);
      ADDR_MX   : in std_logic_vector(log2(INPUT_WIDTH/OUTPUT_WIDTH)-1 downto 0);

      -- Output interface -----------------------------------------------------
      ADDR_OUT  : out std_logic_vector(OUTPUT_WIDTH-1 downto 0)
   );
end ADDR_SPLITTER;

-- ----------------------------------------------------------------------------
--               ARCHITECTURE DECLARATION  --  Address Splitter              --
-- ----------------------------------------------------------------------------

architecture addr_splitter_arch of ADDR_SPLITTER is

   signal reg_addr : std_logic_vector(INPUT_WIDTH-OUTPUT_WIDTH-1 downto 0);
   signal addr     : std_logic_vector(INPUT_WIDTH-1 downto 0);

begin

   -- -------------------------------------------------------------------------
   --                             ADDRESS REGISTER                           --
   -- ------------------------------------------------------------------------- 

   reg_addrp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (ADDR_WE = '1') then
           reg_addr <= ADDR_IN(INPUT_WIDTH-1 downto OUTPUT_WIDTH);
        end if;
     end if;
   end process;

   -- -------------------------------------------------------------------------
   --                             OUTPUT MULTIPLEXOR                         --
   -- -------------------------------------------------------------------------

   U_gen_mux: entity work.GEN_MUX   
   generic map (
      DATA_WIDTH => OUTPUT_WIDTH,
      MUX_WIDTH  => INPUT_WIDTH/OUTPUT_WIDTH
   )
   port map (
      DATA_IN    => addr,
      SEL        => ADDR_MX,
      DATA_OUT   => ADDR_OUT       
   );

   addr <= reg_addr&ADDR_IN(OUTPUT_WIDTH-1 downto 0);
 
end addr_splitter_arch;



