--
-- counter.vhd : IB Transformer Counter
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
use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 
use work.ib_transformer_pkg.all;

-- ----------------------------------------------------------------------------
--               ENTITY DECLARATION -- IB Transformer Counter                --
-- ----------------------------------------------------------------------------

entity IB_TRANSFORMER_COUNTER is 
   generic(
      -- Input Data Width (1-128)
      IN_DATA_WIDTH   : integer := 64;
      -- Output Data Width (1-128)
      OUT_DATA_WIDTH  : integer :=  8    
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK             : in  std_logic;  
      RESET           : in  std_logic;  
      
      -- Control interface ----------------------------------------------------
      RST             : in  std_logic;  
      CE              : in  std_logic;  
      WE              : in  std_logic;  

      -- Data interface -------------------------------------------------------
      COUNTER_IN      : in  std_logic_vector(part_sel_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0);
      COUNTER_OUT     : out std_logic_vector(part_sel_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0)
   );
end IB_TRANSFORMER_COUNTER;

-- ----------------------------------------------------------------------------
--             ARCHITECTURE DECLARATION  --  IB Transformer Counter          --
-- ----------------------------------------------------------------------------

architecture ib_transformer_counter_arch of IB_TRANSFORMER_COUNTER is

   signal COUNTER_OUT_aux : std_logic_vector(part_sel_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0);
                                                                       
begin

   cntp: process (CLK) 
   begin
      if (CLK = '1' and CLK'event) then
         if (RST = '1' or RESET = '1') then 
            COUNTER_OUT_aux <= (others => '0');
         elsif (WE = '1') then  
            COUNTER_OUT_aux <= COUNTER_IN;               
         elsif (CE = '1') then  
            COUNTER_OUT_aux <= COUNTER_OUT_aux + 1;
         end if;
      end if;
   end process;

   COUNTER_OUT <= COUNTER_OUT_aux;

end ib_transformer_counter_arch;

                     

