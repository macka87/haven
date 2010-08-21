--
-- dp_mem_lut.vhd: LUT base dual port memory with synchronous
--   write and asynchronous read and with the data preloading feature.
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Dedek <dedek@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;


--
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity dp_mem_lut is
   generic (
      ITEMS      : integer := 8; 
      DATA_WIDTH : integer := 16;
      DATA       : std_logic_vector 
   );
   port(
		CLK   : in  std_logic;

      -- port A
		WEA    : in  std_logic;
		ADDRA  : in  std_logic_vector(LOG2(ITEMS)-1 downto 0);
		DIA    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
		DOA    : out std_logic_vector(DATA_WIDTH-1 downto 0);

      -- port B
		ADDRB  : in  std_logic_vector(LOG2(ITEMS)-1 downto 0);
		DOB    : out std_logic_vector(DATA_WIDTH-1 downto 0)
	);
end entity dp_mem_lut;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture dp_mem_lut_arch of dp_mem_lut is

   type mem_t is array(0 to ITEMS-1) of 
                  std_logic_vector(DATA_WIDTH-1 downto 0);
   
	
   function mem_init (DATA : in std_logic_vector) return  mem_t is
	variable ram : mem_t;
   begin
	   for i in 0 to ITEMS - 1 loop
		   ram(i) := DATA(i*DATA_WIDTH + DATA_WIDTH - 1  downto i*DATA_WIDTH);
		end loop;
      return ram;
	end;
 
   signal ram: mem_t := mem_init(DATA);

begin
  
--   mem_init(DATA,ram);
	
  	process(CLK) is
   begin
      if (CLK'event and CLK = '1') then
         if (WEA = '1') then
            ram(conv_integer(ADDRA)) <= DIA;
         end if;
      end if;
   end process;

   DOA <= ram(conv_integer(ADDRA));
   DOB <= ram(conv_integer(ADDRB));

end architecture dp_mem_lut_arch;

