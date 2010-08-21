-- crc.vhd: Top level wrapper for crc modules
-- Copyright (C) 2010 CESNET
-- Author: Tomas Dedek <dedek@liberouter.org>
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
                    
LIBRARY IEEE ;
USE ieee.std_logic_1164.all ;
USE ieee.std_logic_arith.all ;
USE ieee.std_logic_unsigned.all ;

ENTITY crc IS 
   GENERIC (
           DATA_WIDTH : integer := 64;
		   CRC_WIDTH  : integer := 3
   );
   PORT(           
           CLK        : IN  STD_LOGIC; 
           RESET      : IN  STD_LOGIC; 
           SOC        : IN  STD_LOGIC; 
           DATA       : IN  STD_LOGIC_VECTOR(DATA_WIDTH - 1 DOWNTO 0); 
           DATA_VALID : IN  STD_LOGIC; 
           EOC        : IN  STD_LOGIC; 
           CRC        : OUT STD_LOGIC_VECTOR(CRC_WIDTH - 1 DOWNTO 0); 
           CRC_VALID  : OUT STD_LOGIC 
       );
END crc; 

ARCHITECTURE full OF crc  IS 


BEGIN 

crc3_data64: if (DATA_WIDTH = 64) and (CRC_WIDTH = 3) generate
  crc_i : entity work.crc_gen3_64
  port map(
     CLOCK      => CLK,
	 RESET      => RESET,
	 SOC        => SOC,
	 DATA       => DATA,
	 DATA_VALID => DATA_VALID,
	 EOC        => EOC,
	 CRC        => CRC,
	 CRC_VALID  => CRC_VALID
  );
end generate;

crc3_data128: if (DATA_WIDTH = 128) and (CRC_WIDTH = 3) generate
  crc_i : entity work.crc_gen3_128
  port map(
     CLOCK      => CLK,
	 RESET      => RESET,
	 SOC        => SOC,
	 DATA       => DATA,
	 DATA_VALID => DATA_VALID,
	 EOC        => EOC,
	 CRC        => CRC,
	 CRC_VALID  => CRC_VALID
  );
end generate;

crc4_data64: if (DATA_WIDTH = 64) and (CRC_WIDTH = 4) generate
  crc_i : entity work.crc_gen4_64
  port map(
     CLOCK      => CLK,
	 RESET      => RESET,
	 SOC        => SOC,
	 DATA       => DATA,
	 DATA_VALID => DATA_VALID,
	 EOC        => EOC,
	 CRC        => CRC,
	 CRC_VALID  => CRC_VALID
  );
end generate;

crc4_data128: if (DATA_WIDTH = 128) and (CRC_WIDTH = 4) generate
  crc_i : entity work.crc_gen4_128
  port map(
     CLOCK      => CLK,
	 RESET      => RESET,
	 SOC        => SOC,
	 DATA       => DATA,
	 DATA_VALID => DATA_VALID,
	 EOC        => EOC,
	 CRC        => CRC,
	 CRC_VALID  => CRC_VALID
  );
end generate;
	
crc5_data64: if (DATA_WIDTH = 64) and (CRC_WIDTH = 5) generate
  crc_i : entity work.crc_gen5_64
  port map(
     CLOCK      => CLK,
	 RESET      => RESET,
	 SOC        => SOC,
	 DATA       => DATA,
	 DATA_VALID => DATA_VALID,
	 EOC        => EOC,
	 CRC        => CRC,
	 CRC_VALID  => CRC_VALID
  );
end generate;

crc5_data128: if (DATA_WIDTH = 128) and (CRC_WIDTH = 5) generate
  crc_i : entity work.crc_gen5_128
  port map(
     CLOCK      => CLK,
	 RESET      => RESET,
	 SOC        => SOC,
	 DATA       => DATA,
	 DATA_VALID => DATA_VALID,
	 EOC        => EOC,
	 CRC        => CRC,
	 CRC_VALID  => CRC_VALID
  );
end generate;

crc6_data64: if (DATA_WIDTH = 64) and (CRC_WIDTH = 6) generate
  crc_i : entity work.crc_gen6_64
  port map(
     CLOCK      => CLK,
	 RESET      => RESET,
	 SOC        => SOC,
	 DATA       => DATA,
	 DATA_VALID => DATA_VALID,
	 EOC        => EOC,
	 CRC        => CRC,
	 CRC_VALID  => CRC_VALID
  );
end generate;

crc6_data128: if (DATA_WIDTH = 128) and (CRC_WIDTH = 6) generate
  crc_i : entity work.crc_gen6_128
  port map(
     CLOCK      => CLK,
	 RESET      => RESET,
	 SOC        => SOC,
	 DATA       => DATA,
	 DATA_VALID => DATA_VALID,
	 EOC        => EOC,
	 CRC        => CRC,
	 CRC_VALID  => CRC_VALID
  );
end generate;

crc7_data64: if (DATA_WIDTH = 64) and (CRC_WIDTH = 7) generate
  crc_i : entity work.crc_gen7_64
  port map(
     CLOCK      => CLK,
	 RESET      => RESET,
	 SOC        => SOC,
	 DATA       => DATA,
	 DATA_VALID => DATA_VALID,
	 EOC        => EOC,
	 CRC        => CRC,
	 CRC_VALID  => CRC_VALID
  );
end generate;

crc7_data128: if (DATA_WIDTH = 128) and (CRC_WIDTH = 7) generate
  crc_i : entity work.crc_gen7_128
  port map(
     CLOCK      => CLK,
	 RESET      => RESET,
	 SOC        => SOC,
	 DATA       => DATA,
	 DATA_VALID => DATA_VALID,
	 EOC        => EOC,
	 CRC        => CRC,
	 CRC_VALID  => CRC_VALID
  );
end generate;

crc8_data64: if (DATA_WIDTH = 64) and (CRC_WIDTH = 8) generate
  crc_i : entity work.crc_gen3_64
  port map(
     CLOCK      => CLK,
	 RESET      => RESET,
	 SOC        => SOC,
	 DATA       => DATA,
	 DATA_VALID => DATA_VALID,
	 EOC        => EOC,
	 CRC        => CRC,
	 CRC_VALID  => CRC_VALID
  );
end generate;

crc8_data128: if (DATA_WIDTH = 128) and (CRC_WIDTH = 8) generate
  crc_i : entity work.crc_gen8_128
  port map(
     CLOCK      => CLK,
	 RESET      => RESET,
	 SOC        => SOC,
	 DATA       => DATA,
	 DATA_VALID => DATA_VALID,
	 EOC        => EOC,
	 CRC        => CRC,
	 CRC_VALID  => CRC_VALID
  );
end generate;

END full;
                      





 



