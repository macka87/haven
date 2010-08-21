-- rem_cmp.vhd: REM computation component
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FLB_REM_CMP is
   generic(
      INPUT_WIDTH    : integer;
      OUTPUT_WIDTH   : integer;
      COUNT          : integer
   );
   port(
      -- which REM is valid
      SEL            : in  std_logic_vector(COUNT-1 downto 0);
      INPUT_REMS     : in  std_logic_vector(COUNT*log2(INPUT_WIDTH/8)-1 
                                                                     downto 0);
      -- computed REM
      TX_REM         : out std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0)
   );
end entity FLB_REM_CMP;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FLB_REM_CMP is

   -- ------------------ Types declaration ------------------------------------
   type t_offsets          is array (0 to (COUNT-1)) of
                             std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0);

   -- ------------------ Signals declaration ----------------------------------
   signal offset           : std_logic_vector(COUNT*log2(OUTPUT_WIDTH/8)-1
                             downto 0);
   signal chosen_rem       : std_logic_vector(abs(log2(COUNT)-1) downto 0);
   signal mx_rem           : std_logic_vector(log2(INPUT_WIDTH/8)-1 downto 0);
   signal mx_offset        : std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0);

begin
   TX_REM   <= mx_offset + mx_rem;
   
   -- generate necessary comparators ------------------------------------------
   GEN_OFFSETS: for i in 0 to COUNT-1 generate
      offset((i+1)*log2(OUTPUT_WIDTH/8)-1 downto i*log2(OUTPUT_WIDTH/8)) 
         <= conv_std_logic_vector(i*(INPUT_WIDTH/8), log2(OUTPUT_WIDTH/8));
   end generate;
   
   -- generate components in case when COUNT = 1 ------------------------------
   GEN_COUNT_1 : if COUNT = 1 generate
      mx_rem      <= INPUT_REMS;
      mx_offset   <= offset;
   end generate;
   
   -- generate components in case when COUNT > 1 ------------------------------
   GEN_COUNT_N : if COUNT > 1 generate
      -- get chosen REM number
      CHOSEN_REM_ENC : entity work.GEN_ENC
         generic map(
            ITEMS       => COUNT
         )
         port map(
            DI          => SEL,
            ADDR        => chosen_rem
         );
   
      REM_MUX : entity work.GEN_MUX
         generic map(
            DATA_WIDTH  => log2(INPUT_WIDTH/8),
            MUX_WIDTH   => COUNT
         )
         port map(
            DATA_IN     => INPUT_REMS,
            SEL         => chosen_rem,
            DATA_OUT    => mx_rem
         );
   
      OFFSET_MUX : entity work.GEN_MUX
         generic map(
            DATA_WIDTH  => log2(OUTPUT_WIDTH/8),
            MUX_WIDTH   => COUNT
         )
         port map(
            DATA_IN     => offset,
            SEL         => chosen_rem,
            DATA_OUT    => mx_offset
         );
   end generate;

end architecture full;
