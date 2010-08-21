-- dma_status_reg.vhd: DMA status register for interrupt vector reading
-- Copyright (C) 2008 CESNET
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity DMA_STATUS_REG is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- Internal Bus interface
      RD_BE          : in  std_logic_vector(7 downto 0);
      RD_REQ         : in  std_logic;
      RD_DATA        : out std_logic_vector(63 downto 0);
      
      -- DMA Controller interface
      SET_INTERRUPT  : in  std_logic_vector(63 downto 0)
   );
end entity DMA_STATUS_REG;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of DMA_STATUS_REG is
   constant BYTES             : integer := 8;

   -- ------------------ Signals declaration ----------------------------------
   -- registers
   signal reg_status          : std_logic_vector(BYTES*8-1 downto 0);
   signal reg_status_clear    : std_logic_vector(BYTES-1 downto 0);

begin
   RD_DATA  <= reg_status;

   GEN_CLEAR_SIG: for i in 0 to BYTES-1 generate
      reg_status_clear(i) <= RD_BE(i) and RD_REQ;
   end generate;
   
   GEN_STATUS_BYTE: for i in 0 to BYTES-1 generate
      GEM_STATUS_BIT: for j in 0 to 7 generate
         -- status register
         reg_statusp: process (CLK)
         begin
            if CLK'event and CLK='1' then
               if (RESET = '1') then
                  reg_status(i*8+j) <= '0';
               else
                  if (SET_INTERRUPT(i*8+j) = '1') then
                     reg_status(i*8+j) <= '1';
                  elsif(reg_status_clear(i) = '1') then
                     reg_status(i*8+j) <= '0';
                  end if;
               end if;
            end if;
         end process;
      end generate;
   end generate;

end architecture full;

