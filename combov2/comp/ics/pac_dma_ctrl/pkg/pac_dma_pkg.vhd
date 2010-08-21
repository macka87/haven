-- pac_dma_pkg.vhd: Packet DMA package
-- Copyright (C) 2009 CESNET
-- Author(s): Petr Kastovsky <kastovsky@liberouter.org>
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
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use IEEE.numeric_std.all;

-- ----------------------------------------------------------------------------
--                        Packet DMA Package
-- ----------------------------------------------------------------------------
package pac_dma_pkg is

   -- number of flags in descriptor
   constant NUM_FLAGS      : integer := 8;
   -- flags position inside of descriptor = upper 32bits of first word
   constant PAC_DMA_INTF   : integer := 0; -- position of interrupt flag
   constant PAC_DMA_LFF    : integer := 1; -- position of last fragment flag
   constant PAC_DMA_NDF    : integer := 2; -- position of next desc flag
   
   -- maximal number of interfaces
   constant PAC_MAX_IFCS   : integer := 64;

   -- dma ctrl block address space constants definitions
   constant PAC_RX_BUFF_BASE : std_logic_vector(31 downto 0) := X"02000000";
   -- gap between two buffers
   constant PAC_RX_BUFF_GAP  : std_logic_vector(31 downto 0) := X"00004000";
   constant PAC_RX_BUFF_SIZE : integer := 4096;

   constant PAC_TX_BUFF_BASE : std_logic_vector(31 downto 0) := X"02100000";
   -- gap between two buffers
   constant PAC_TX_BUFF_GAP  : std_logic_vector(31 downto 0) := X"00004000";
   constant PAC_TX_BUFF_SIZE : integer := 4096;

   constant PAC_IB_BASE  : std_logic_vector(31 downto 0) := X"02200000";

   -- size of address space for one channel on mi32
   constant PAC_MI32_ADDR_MAX : integer := 64;
end pac_dma_pkg;

-- ----------------------------------------------------------------------------
--                        Packet DMA Package body
-- ----------------------------------------------------------------------------
package body pac_dma_pkg is

end pac_dma_pkg;
