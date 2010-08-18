--
-- be_register.vhd: register with byte enable
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
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
--
-- $Id$
--
-- TODO:
--
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity be_register is
   generic (
      DATA_WIDTH : integer := 64
   );
   port(
      CLK : in std_logic;

      -- read/write PORT
      WEA   : in std_logic;
      BEA   : in std_logic_vector((DATA_WIDTH/8)-1 downto 0);
      DIA   : in std_logic_vector(DATA_WIDTH-1 downto 0);
      DOA   : out std_logic_vector(DATA_WIDTH-1 downto 0);

      -- readonly PORT
      DOB   : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end entity be_register;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture be_register_arch of be_register is

   type TREG_ARRAY  is array (DATA_WIDTH/8 - 1 downto 0) 
                  of std_logic_vector(7 downto 0);

   signal memory_array : TREG_ARRAY;

begin

   gen_mems: for i in 0 to DATA_WIDTH/8 - 1 generate

      regs_p : process(CLK) is
      begin
         if (CLK'event and CLK = '1') then
            if (WEA = '1' and BEA(i) = '1') then
               memory_array(i) <= DIA((i + 1)*8 - 1 downto i*8);
            end if;
         end if;
      end process;

      DOA((i + 1)*8 - 1 downto i*8) <= memory_array(i);
      DOB((i + 1)*8 - 1 downto i*8) <= memory_array(i);
   end generate;

end architecture be_register_arch;

