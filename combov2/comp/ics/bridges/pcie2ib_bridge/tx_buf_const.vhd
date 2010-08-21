--
-- tx_buf_const.vhd : TX Buffer Constants derived from MAX_PAYLOAD_SIZE
-- Copyright (C) 2007 CESNET
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

library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use WORK.math_pack.all;

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--                 ENTITY DECLARATION -- TX Buffer Constants                 -- 
-- ----------------------------------------------------------------------------

entity TX_BUF_CONST is 
   port (
      -- clock & reset --------------------------------------------------------
      CLK              : in std_logic;  -- FPGA clock
      RESET            : in std_logic;  -- Reset active high

      -- input signals --------------------------------------------------------
      MAX_PAYLOAD_SIZE : in std_logic_vector( 2 downto 0);  -- Maximum Payload TLP Size      
      REG_BYTECOUNT    : in std_logic_vector(12 downto 0);  -- Byte Count Register

      -- output derived signals -----------------------------------------------
      TLP_MAX_LEN_13 : out std_logic_vector(12 downto 0); -- TLP_MAX_LEN
      TLP_MAX_LEN_13_MINUS_1 : out std_logic_vector(12 downto 0); -- TLP_MAX_LEN-1
      TLP_MAX_LEN_13_MINUS_2 : out std_logic_vector(12 downto 0); -- TLP_MAX_LEN-2
      REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN : out std_logic_vector(12 downto 0); -- reg_bytecount(12 downto log2(TLP_MAX_LEN)
      REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0 : out std_logic_vector(12 downto 0) -- reg_bytecount(log2(TLP_MAX_LEN)-1 downto 0)
   );
end TX_BUF_CONST;

-- ----------------------------------------------------------------------------
--            ARCHITECTURE DECLARATION  --  TX Buffer Constants              --
-- ----------------------------------------------------------------------------

architecture tx_buf_const_arch of TX_BUF_CONST is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal TLP_MAX_LEN_13_dec : std_logic_vector(12 downto 0); -- TLP_MAX_LEN
   signal TLP_MAX_LEN_13_MINUS_1_dec : std_logic_vector(12 downto 0); -- TLP_MAX_LEN-1
   signal TLP_MAX_LEN_13_MINUS_2_dec : std_logic_vector(12 downto 0); -- TLP_MAX_LEN-2
   signal REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN_dec : std_logic_vector(12 downto 0); -- reg_bytecount(12 downto log2(TLP_MAX_LEN)
   signal REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0_dec : std_logic_vector(12 downto 0); -- reg_bytecount(log2(TLP_MAX_LEN)-1 downto 0)

begin

   -- MAX_PAYLOAD_SIZE decoder ------------------------------------------------

   m_p_s_decp: process(CLK, RESET, MAX_PAYLOAD_SIZE, REG_BYTECOUNT)
   begin
      TLP_MAX_LEN_13_dec <= "0000000000000";
      TLP_MAX_LEN_13_MINUS_1_dec <= "0000000000000";
      TLP_MAX_LEN_13_MINUS_2_dec <= "0000000000000";            
      REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN_dec <= "0000000000000";
      REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0_dec <= "0000000000000";

      case MAX_PAYLOAD_SIZE is
         when "000"  => TLP_MAX_LEN_13_dec <= conv_std_logic_vector( 128, 13);          
                        TLP_MAX_LEN_13_MINUS_1_dec <= conv_std_logic_vector( 127, 13);
                        TLP_MAX_LEN_13_MINUS_2_dec <= conv_std_logic_vector( 126, 13);
                        REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN_dec <= "0000000"&reg_bytecount(12 downto 7);
                        REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0_dec <= "000000"&reg_bytecount(6 downto 0);
         
         when "001"  => TLP_MAX_LEN_13_dec <= conv_std_logic_vector( 256, 13);                   
                        TLP_MAX_LEN_13_MINUS_1_dec <= conv_std_logic_vector( 255, 13);
                        TLP_MAX_LEN_13_MINUS_2_dec <= conv_std_logic_vector( 254, 13);
                        REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN_dec <= "00000000"&reg_bytecount(12 downto 8);
                        REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0_dec <= "00000"&reg_bytecount(7 downto 0);
         
         when "010"  => TLP_MAX_LEN_13_dec <= conv_std_logic_vector( 512, 13);                            
                        TLP_MAX_LEN_13_MINUS_1_dec <= conv_std_logic_vector( 511, 13);
                        TLP_MAX_LEN_13_MINUS_2_dec <= conv_std_logic_vector( 510, 13);
                        REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN_dec <= "000000000"&reg_bytecount(12 downto 9);
                        REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0_dec <= "0000"&reg_bytecount(8 downto 0);
         
         when "011"  => TLP_MAX_LEN_13_dec <= conv_std_logic_vector(1024, 13);                                      
                        TLP_MAX_LEN_13_MINUS_1_dec <= conv_std_logic_vector( 1023, 13);
                        TLP_MAX_LEN_13_MINUS_2_dec <= conv_std_logic_vector( 1022, 13);
                        REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN_dec <= "0000000000"&reg_bytecount(12 downto 10);
                        REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0_dec <= "000"&reg_bytecount(9 downto 0);
         
         when "100"  => TLP_MAX_LEN_13_dec <= conv_std_logic_vector(2048, 13);                           
                        TLP_MAX_LEN_13_MINUS_1_dec <= conv_std_logic_vector(2047, 13);
                        TLP_MAX_LEN_13_MINUS_2_dec <= conv_std_logic_vector(2046, 13);
                        REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN_dec <= "00000000000"&reg_bytecount(12 downto 11);
                        REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0_dec <= "00"&reg_bytecount(10 downto 0);
         
         when "101"  => TLP_MAX_LEN_13_dec <= conv_std_logic_vector(4096, 13);                                             
                        TLP_MAX_LEN_13_MINUS_1_dec <= conv_std_logic_vector(4095, 13);
                        TLP_MAX_LEN_13_MINUS_2_dec <= conv_std_logic_vector(4094, 13);
                        REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN_dec <= "0000000000000";
                        REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0_dec <= reg_bytecount(12 downto 0);
         
         when others => TLP_MAX_LEN_13_dec <= conv_std_logic_vector( 128, 13);
                        TLP_MAX_LEN_13_MINUS_1_dec <= conv_std_logic_vector( 127, 13);
                        TLP_MAX_LEN_13_MINUS_2_dec <= conv_std_logic_vector( 126, 13);
                        REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN_dec <= "0000000"&reg_bytecount(12 downto 7);
                        REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0_dec <= "000000"&reg_bytecount(6 downto 0);
         
      end case;
   end process;       

   -- DECODED VALUES STORING --------------------------------------------------

   m_p_s_regp: process(RESET, CLK)
   begin
     if (CLK'event AND CLK = '1') then
        TLP_MAX_LEN_13 <= TLP_MAX_LEN_13_dec;
        TLP_MAX_LEN_13_MINUS_1 <= TLP_MAX_LEN_13_MINUS_1_dec;
        TLP_MAX_LEN_13_MINUS_2 <= TLP_MAX_LEN_13_MINUS_2_dec;
        --REG_BYTECOUNT_11_DOWNTO_LOG2_TLP_MAX_LEN <= REG_BYTECOUNT_11_DOWNTO_LOG2_TLP_MAX_LEN_dec;
        --REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0 <= REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0_dec;
     end if;
   end process;           

   REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN <= REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN_dec;
   REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0 <= REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0_dec;
       
end tx_buf_const_arch;

                      

