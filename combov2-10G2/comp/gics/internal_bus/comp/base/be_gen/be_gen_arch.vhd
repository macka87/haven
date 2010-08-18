--
-- be_gen_arch.vhd : IB Byte Enable Generator Architecture
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

-- ----------------------------------------------------------------------------
--          ARCHITECTURE DECLARATION  --  IB Byte Enable Generator           --
-- ----------------------------------------------------------------------------

architecture ib_be_gen_arch of IB_BE_GEN is

   constant ONES     : std_logic_vector(DATA_WIDTH/8-1 downto 0) := (others => '1');

   signal last_align : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal be_sof_dec : std_logic_vector(DATA_WIDTH/8-1 downto 0);
   signal be_eof_dec : std_logic_vector(DATA_WIDTH/8-1 downto 0);
   signal be_mux     : std_logic_vector(DATA_WIDTH/8-1 downto 0);
   signal be_mux_sel : std_logic_vector(1 downto 0);
                                                                                                 
begin

   -- -------------------------------------------------------------------------
   --                     BYTE ENABLE DECODERS (for sof, eof)                --
   -- -------------------------------------------------------------------------

   last_align <= LENGTH_ALIGN + ADDR_ALIGN;

   -- DATA WIDTH = 16 ---------------------------------------------------------

   DEC_GEN16: if (DATA_WIDTH = 16) generate    

      be_sof_decp: process(ADDR_ALIGN(0))
      begin
         case ADDR_ALIGN(0) is
            when '0'  => be_sof_dec <= "11";
            when '1'  => be_sof_dec <= "10";
            when others => be_sof_dec <= "XX";
         end case;
      end process;

      be_eof_decp: process(last_align(0))
      begin
         case last_align(0) is
            when '0'  => be_eof_dec <= "11";
            when '1'  => be_eof_dec <= "01";
            when others => be_eof_dec <= "XX";
         end case;
      end process; 

   end generate;      

   -- DATA WIDTH = 32 ---------------------------------------------------------

   DEC_GEN32: if (DATA_WIDTH = 32) generate    

      be_sof_decp: process(ADDR_ALIGN(1 downto 0))
      begin
         case ADDR_ALIGN(1 downto 0) is
            when "00"  => be_sof_dec <= "1111";
            when "01"  => be_sof_dec <= "1110";
            when "10"  => be_sof_dec <= "1100";
            when "11"  => be_sof_dec <= "1000";
            when others => be_sof_dec <= "XXXX";
         end case;
      end process;

      be_eof_decp: process(last_align(1 downto 0))
      begin
         case last_align(1 downto 0) is
            when "00"  => be_eof_dec <= "1111";
            when "01"  => be_eof_dec <= "0001";
            when "10"  => be_eof_dec <= "0011";
            when "11"  => be_eof_dec <= "0111";
            when others => be_eof_dec <= "XXXX";
         end case;
      end process; 

   end generate;   

   -- DATA WIDTH = 64 ---------------------------------------------------------

   DEC_GEN64: if (DATA_WIDTH = 64) generate    

      be_sof_decp: process(ADDR_ALIGN(2 downto 0))
      begin
         case ADDR_ALIGN(2 downto 0) is
            when "000"  => be_sof_dec <= "11111111";
            when "001"  => be_sof_dec <= "11111110";
            when "010"  => be_sof_dec <= "11111100";
            when "011"  => be_sof_dec <= "11111000";
            when "100"  => be_sof_dec <= "11110000";
            when "101"  => be_sof_dec <= "11100000";
            when "110"  => be_sof_dec <= "11000000";
            when "111"  => be_sof_dec <= "10000000";
            when others => be_sof_dec <= "XXXXXXXX";
         end case;
      end process;

      be_eof_decp: process(last_align(2 downto 0))
      begin
         case last_align(2 downto 0) is
            when "000"  => be_eof_dec <= "11111111";
            when "001"  => be_eof_dec <= "00000001";
            when "010"  => be_eof_dec <= "00000011";
            when "011"  => be_eof_dec <= "00000111";
            when "100"  => be_eof_dec <= "00001111";
            when "101"  => be_eof_dec <= "00011111";
            when "110"  => be_eof_dec <= "00111111";
            when "111"  => be_eof_dec <= "01111111";
            when others => be_eof_dec <= "XXXXXXXX";
         end case;
      end process; 

   end generate;

   -- DATA WIDTH = 128 --------------------------------------------------------

   DEC_GEN128: if (DATA_WIDTH = 128) generate    

      be_sof_decp: process(ADDR_ALIGN(3 downto 0))
      begin
         case ADDR_ALIGN(3 downto 0) is
            when "0000"  => be_sof_dec <= "1111111111111111";
            when "0001"  => be_sof_dec <= "1111111111111110";
            when "0010"  => be_sof_dec <= "1111111111111100";
            when "0011"  => be_sof_dec <= "1111111111111000";
            when "0100"  => be_sof_dec <= "1111111111110000";
            when "0101"  => be_sof_dec <= "1111111111100000";
            when "0110"  => be_sof_dec <= "1111111111000000";
            when "0111"  => be_sof_dec <= "1111111110000000";

            when "1000"  => be_sof_dec <= "1111111100000000";
            when "1001"  => be_sof_dec <= "1111111000000000";
            when "1010"  => be_sof_dec <= "1111110000000000";
            when "1011"  => be_sof_dec <= "1111100000000000";
            when "1100"  => be_sof_dec <= "1111000000000000";
            when "1101"  => be_sof_dec <= "1110000000000000";
            when "1110"  => be_sof_dec <= "1100000000000000";
            when "1111"  => be_sof_dec <= "1000000000000000";
            
            when others  => be_sof_dec <= "XXXXXXXXXXXXXXXX";
         end case;
      end process;

      be_eof_decp: process(last_align(3 downto 0))
      begin
         case last_align(3 downto 0) is
            when "0000"  => be_eof_dec <= "1111111111111111";
            when "0001"  => be_eof_dec <= "0000000000000001";
            when "0010"  => be_eof_dec <= "0000000000000011";
            when "0011"  => be_eof_dec <= "0000000000000111";
            when "0100"  => be_eof_dec <= "0000000000001111";
            when "0101"  => be_eof_dec <= "0000000000011111";
            when "0110"  => be_eof_dec <= "0000000000111111";
            when "0111"  => be_eof_dec <= "0000000001111111";

            when "1000"  => be_eof_dec <= "0000000011111111";
            when "1001"  => be_eof_dec <= "0000000111111111";
            when "1010"  => be_eof_dec <= "0000001111111111";
            when "1011"  => be_eof_dec <= "0000011111111111";
            when "1100"  => be_eof_dec <= "0000111111111111";
            when "1101"  => be_eof_dec <= "0001111111111111";
            when "1110"  => be_eof_dec <= "0011111111111111";
            when "1111"  => be_eof_dec <= "0111111111111111";
            
            when others  => be_eof_dec <= "XXXXXXXXXXXXXXXX";
         end case;
      end process; 

   end generate;   

   -- -------------------------------------------------------------------------
   --                       BYTE ENABLE OUTPUT MULTIPLEXOR                   --
   -- ------------------------------------------------------------------------- 

   be_mux_sel <= EOF & SOF;

   be_muxp: process(be_mux_sel, be_sof_dec, be_eof_dec)
   begin
      case be_mux_sel is
         when "00" => be_mux <= ONES;
         when "01" => be_mux <= be_sof_dec;
         when "10" => be_mux <= be_eof_dec;
         when "11" => be_mux <= (be_sof_dec and be_eof_dec);
         when others => be_mux <= (others => 'X');
      end case;
   end process; 
   
   BE <= be_mux;

end ib_be_gen_arch;



