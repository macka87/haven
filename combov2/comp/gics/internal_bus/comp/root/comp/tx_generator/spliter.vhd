--
-- spliter.vhd : PCI-e Data realign unit
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kobierský <kobiersky@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity PCIE_SPLITER is
  port (
    -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N           : in  std_logic; 
      TRN_CLK               : in  std_logic; 

    -- Data Input Interface -------------------------------------------------
      IN_DATA               : in  std_logic_vector( 63 downto 0 ); -- Data or Header
      IN_SOP_N              : in  std_logic;                       -- Start of Packet
      IN_EOP_N              : in  std_logic;                       -- End of Packet
      IN_SRC_RDY_N          : in  std_logic;                       -- Source Ready
      IN_DST_RDY_N          : out std_logic;                       -- Destination Ready
      IN_REM_N              : in  std_logic;                       -- Output REM
    -- Data Output Interface ------------------------------------------------
      OUT_DATA              : out std_logic_vector( 63 downto 0 ); -- Data or Header
      OUT_SOP_N             : out std_logic;                       -- Start of Packet
      OUT_EOP_N             : out std_logic;                       -- End of Packet
      OUT_SRC_RDY_N         : out std_logic;                       -- Source Ready
      OUT_DST_RDY_N         : in  std_logic;                       -- Destination Ready
      OUT_REM_N             : out std_logic;                       -- Output REM

    -- Control Interface ----------------------------------------------------
      MAX_PAYLOAD_SIZE      : in  std_logic_vector(9 downto 0);
      DW4                   : in  std_logic;                       -- 4 DW 
      DW4_REG               : in  std_logic;                       -- 4 DW 
      INIT                  : in  std_logic                        -- Init   
    -- Spliting interface ---------------------------------------------------
   );
end PCIE_SPLITER;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of PCIE_SPLITER is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal max_words_out      : std_logic_vector(8 downto 0);
   signal dw3_plus_one       : std_logic;
   signal eop_n_split        : std_logic;
   signal stop_input         : std_logic;

begin

   OUT_DATA         <= IN_DATA;
   OUT_SOP_N        <= IN_SOP_N;
   OUT_EOP_N        <= '0' when (IN_EOP_N='0' or eop_n_split='0') else '1';
   OUT_SRC_RDY_N    <= IN_SRC_RDY_N;
   OUT_REM_N        <= IN_REM_N when (DW4_REG = '1' or eop_n_split='1') else '1';
   IN_DST_RDY_N     <= '0' when (OUT_DST_RDY_N='0' and stop_input='0') else '1';

   -- EOP when max is exceeded ------------------------------------------------
   -- Is active sended data exceed max payload limit
   eop_n_split <= '0' when max_words_out = 1 else '1';

   -- max_words_out counter ---------------------------------------------------
   max_words_outp: process(TRN_CLK, TRN_RESET_N)
   begin
      if (TRN_CLK'event AND TRN_CLK = '1') then
         if (TRN_RESET_N = '0') then
            max_words_out <= (others => '0');
         elsif (INIT='1' or (eop_n_split = '0' and OUT_DST_RDY_N='0' and IN_SRC_RDY_N = '0')) then
            max_words_out <= MAX_PAYLOAD_SIZE(9 downto 1);
         elsif (IN_SRC_RDY_N = '0' and OUT_DST_RDY_N = '0' and dw3_plus_one='0') then
            max_words_out <= max_words_out - 1;
         end if;
      end if;
   end process;

   -- last word generation for DW3 header -------------------------------------
   dw3_plus_onep: process(TRN_CLK, TRN_RESET_N)
   begin
      if (TRN_CLK'event AND TRN_CLK = '1') then
         if (TRN_RESET_N = '0') then
            dw3_plus_one <= '0';
         elsif (INIT='1' or (max_words_out = 1 and OUT_DST_RDY_N='0' and IN_SRC_RDY_N = '0')) then
            dw3_plus_one <= not DW4;
         elsif (IN_SRC_RDY_N = '0' and OUT_DST_RDY_N = '0') then
            dw3_plus_one <= '0';
         end if;
      end if;
   end process;

   stop_input <= '1' when (eop_n_split = '0' and IN_EOP_N='1' and DW4='0' and IN_SRC_RDY_N='0') or
                          (eop_n_split = '0' and IN_EOP_N='0' and DW4='0' and IN_REM_N='0' and IN_SRC_RDY_N='0')
                          else '0';

end architecture FULL;
