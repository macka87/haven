-- compress.vhd: Frame Link protocol signals compressor
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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

entity fl_compress is
   generic(
      WIRES : integer := 1 -- 1, 2, or 4
   );
   port(
      -- Common interface
      CLK            : in  std_logic;
      RESET          : in  std_logic;
      
      -- Recieve interface
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : in  std_logic; -- Is input, because this comp does not
                                      -- perform flow control.
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      
      FL_JUICE       : out std_logic_vector(WIRES-1 downto 0); 
         -- Compressed FL control signals
         
      FRAME_PART     : out std_logic 
         -- Every cycle in '1' means one frame part
   );
end entity;


architecture full of FL_COMPRESS is
   signal sig_juice     : std_logic_vector(3 downto 0); -- output signal
   signal reg_first     : std_logic;   -- Is set to '1' after first frame ends
   signal sig_frame_part: std_logic;   -- output

begin
   sig_juice <= RX_SOF_N & RX_SOP_N & RX_EOF_N & RX_EOP_N; -- All signals

   -- Register to remember that first frame is gone
   reg_first_p : process(CLK, RESET)
   begin
      if(RESET = '1') then
         reg_first <= '0';
      elsif(CLK'event and CLK = '1') then
         if(RX_EOF_N = '0' and RX_SRC_RDY_N = '0' and RX_DST_RDY_N = '0') then
            reg_first <= '1';
         end if;
      end if;
   end process;

   -- Each end of part except the last one is marked
   sig_frame_part <= (not RX_SRC_RDY_N) and
                     (not RX_DST_RDY_N) and
                     (not RX_EOP_N) and
                     (RX_EOF_N) and
                     (not reg_first);

   FL_JUICE    <= sig_juice(WIRES-1 downto 0);
   FRAME_PART  <= sig_frame_part;
end architecture full;

