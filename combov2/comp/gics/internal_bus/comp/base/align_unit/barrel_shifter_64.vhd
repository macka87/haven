--
-- barrel_shifter_64.vhd 64 bit barrel shifter
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
-- $Id$
--
-- TODO:
--

library IEEE;  
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--                 ENTITY DECLARATION -- Barrel shifter		    	         -- 
-- ----------------------------------------------------------------------------

entity BARREL_SHIFTER_64 is 
   port (
      -- Input interface ------------------------------------------------------
      DATA_IN		: in std_logic_vector(63 downto 0);      
	  SEL			: in std_logic_vector(2 downto 0); 

      -- Output interface -----------------------------------------------------
      DATA_OUT      : out std_logic_vector(63 downto 0)
   );
end BARREL_SHIFTER_64;

-- ----------------------------------------------------------------------------
--                 ARCHITECTURE DECLARATION  								 --
-- ----------------------------------------------------------------------------

architecture barrel_shifter_64_arch of BARREL_SHIFTER_64 is

   -- multiplexors data out	
   signal data_out_mux0  : std_logic_vector(7 downto 0);
   signal data_out_mux1  : std_logic_vector(7 downto 0);
   signal data_out_mux2  : std_logic_vector(7 downto 0);
   signal data_out_mux3  : std_logic_vector(7 downto 0);
   signal data_out_mux4  : std_logic_vector(7 downto 0);
   signal data_out_mux5  : std_logic_vector(7 downto 0);
   signal data_out_mux6  : std_logic_vector(7 downto 0);
   signal data_out_mux7  : std_logic_vector(7 downto 0);	

begin

--     assert (true)
--     report "BARREL SHIFTER HAS NOT BEEN IMPLEMENTED YET!!!"
--     severity ERROR;

	-- multiplexor data_out_mux0 -----------------------------------------------
	data_out_mux0p: process(SEL, DATA_IN)
	begin
	   case SEL is
	      when "000" => data_out_mux0 <= DATA_IN(7 downto 0);
	      when "001" => data_out_mux0 <= DATA_IN(63 downto 56);
	      when "010" => data_out_mux0 <= DATA_IN(55 downto 48);
	      when "011" => data_out_mux0 <= DATA_IN(47 downto 40);
	      when "100" => data_out_mux0 <= DATA_IN(39 downto 32);
	      when "101" => data_out_mux0 <= DATA_IN(31 downto 24);
	      when "110" => data_out_mux0 <= DATA_IN(23 downto 16);
	      when "111" => data_out_mux0 <= DATA_IN(15 downto 8);
	      when others => data_out_mux0 <= (others => 'X');
	   end case;
	end process;
	
	-- multiplexor data_out_mux1 -----------------------------------------------
	data_out_mux1p: process(SEL, DATA_IN)
	begin
	   case SEL is
	      when "000" => data_out_mux1 <= DATA_IN(15 downto 8);
	      when "001" => data_out_mux1 <= DATA_IN(7 downto 0);
	      when "010" => data_out_mux1 <= DATA_IN(63 downto 56);
	      when "011" => data_out_mux1 <= DATA_IN(55 downto 48);
	      when "100" => data_out_mux1 <= DATA_IN(47 downto 40);
	      when "101" => data_out_mux1 <= DATA_IN(39 downto 32);
	      when "110" => data_out_mux1 <= DATA_IN(31 downto 24);
	      when "111" => data_out_mux1 <= DATA_IN(23 downto 16);
	      when others => data_out_mux1 <= (others => 'X');
	   end case;
	end process;
	
	-- multiplexor data_out_mux2 -----------------------------------------------
	data_out_mux2p: process(SEL, DATA_IN)
	begin
	   case SEL is
	      when "000" => data_out_mux2 <= DATA_IN(23 downto 16);
	      when "001" => data_out_mux2 <= DATA_IN(15 downto 8);
	      when "010" => data_out_mux2 <= DATA_IN(7 downto 0);
	      when "011" => data_out_mux2 <= DATA_IN(63 downto 56);
	      when "100" => data_out_mux2 <= DATA_IN(55 downto 48);
	      when "101" => data_out_mux2 <= DATA_IN(47 downto 40);
	      when "110" => data_out_mux2 <= DATA_IN(39 downto 32);
	      when "111" => data_out_mux2 <= DATA_IN(31 downto 24);
	      when others => data_out_mux2 <= (others => 'X');
	   end case;
	end process;
	
	-- multiplexor data_out_mux3 -----------------------------------------------
	data_out_mux3p: process(SEL, DATA_IN)
	begin
	   case SEL is
	      when "000" => data_out_mux3 <= DATA_IN(31 downto 24);
	      when "001" => data_out_mux3 <= DATA_IN(23 downto 16);
	      when "010" => data_out_mux3 <= DATA_IN(15 downto 8);
	      when "011" => data_out_mux3 <= DATA_IN(7 downto 0);
	      when "100" => data_out_mux3 <= DATA_IN(63 downto 56);
	      when "101" => data_out_mux3 <= DATA_IN(55 downto 48);
	      when "110" => data_out_mux3 <= DATA_IN(47 downto 40);
	      when "111" => data_out_mux3 <= DATA_IN(39 downto 32);
	      when others => data_out_mux3 <= (others => 'X');
	   end case;
	end process;
	
	-- multiplexor data_out_mux4 -----------------------------------------------
	data_out_mux4p: process(SEL, DATA_IN)
	begin
	   case SEL is
	      when "000" => data_out_mux4 <= DATA_IN(39 downto 32);
	      when "001" => data_out_mux4 <= DATA_IN(31 downto 24);
	      when "010" => data_out_mux4 <= DATA_IN(23 downto 16);
	      when "011" => data_out_mux4 <= DATA_IN(15 downto 8);
	      when "100" => data_out_mux4 <= DATA_IN(7 downto 0);
	      when "101" => data_out_mux4 <= DATA_IN(63 downto 56);
	      when "110" => data_out_mux4 <= DATA_IN(55 downto 48);
	      when "111" => data_out_mux4 <= DATA_IN(47 downto 40);
	      when others => data_out_mux4 <= (others => 'X');
	   end case;
	end process;
	
	-- multiplexor data_out_mux5 -----------------------------------------------
	data_out_mux5p: process(SEL, DATA_IN)
	begin
	   case SEL is
	      when "000" => data_out_mux5 <= DATA_IN(47 downto 40);
	      when "001" => data_out_mux5 <= DATA_IN(39 downto 32);
	      when "010" => data_out_mux5 <= DATA_IN(31 downto 24);
	      when "011" => data_out_mux5 <= DATA_IN(23 downto 16);
	      when "100" => data_out_mux5 <= DATA_IN(15 downto 8);
	      when "101" => data_out_mux5 <= DATA_IN(7 downto 0);
	      when "110" => data_out_mux5 <= DATA_IN(63 downto 56);
	      when "111" => data_out_mux5 <= DATA_IN(55 downto 48);
	      when others => data_out_mux5 <= (others => 'X');
	   end case;
	end process;
	
	-- multiplexor data_out_mux6 -----------------------------------------------
	data_out_mux6p: process(SEL, DATA_IN)
	begin
	   case SEL is
	      when "000" => data_out_mux6 <= DATA_IN(55 downto 48);
	      when "001" => data_out_mux6 <= DATA_IN(47 downto 40);
	      when "010" => data_out_mux6 <= DATA_IN(39 downto 32);
	      when "011" => data_out_mux6 <= DATA_IN(31 downto 24);
	      when "100" => data_out_mux6 <= DATA_IN(23 downto 16);
	      when "101" => data_out_mux6 <= DATA_IN(15 downto 8);
	      when "110" => data_out_mux6 <= DATA_IN(7 downto 0);
	      when "111" => data_out_mux6 <= DATA_IN(63 downto 56);
	      when others => data_out_mux6 <= (others => 'X');
	   end case;
	end process;
	
	-- multiplexor data_out_mux7 -----------------------------------------------
	data_out_mux7p: process(SEL, DATA_IN)
	begin
	   case SEL is
	      when "000" => data_out_mux7 <= DATA_IN(63 downto 56);
	      when "001" => data_out_mux7 <= DATA_IN(55 downto 48);
	      when "010" => data_out_mux7 <= DATA_IN(47 downto 40);
	      when "011" => data_out_mux7 <= DATA_IN(39 downto 32);
	      when "100" => data_out_mux7 <= DATA_IN(31 downto 24);
	      when "101" => data_out_mux7 <= DATA_IN(23 downto 16);
	      when "110" => data_out_mux7 <= DATA_IN(15 downto 8);
	      when "111" => data_out_mux7 <= DATA_IN(7 downto 0);
	      when others => data_out_mux7 <= (others => 'X');
	   end case;
	end process;

	-- connect actual data from multiplexors
	DATA_OUT <= data_out_mux7 & data_out_mux6 & 
				data_out_mux5 & data_out_mux4 & 
				data_out_mux3 & data_out_mux2 &
				data_out_mux1 & data_out_mux0;

end barrel_shifter_64_arch;

