-- ifnum_extract.vhd: Extractor of InterFace NUMver from FrameLink.
-- Copyright (C) 2010 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
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

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

--* The entity extracts data of TX_COUNT length from the FrameLink.
--* The data are placed on the IFNUM_OFFSET (in bits) from start of frame.
entity ifnum_extract is
generic (
   TX_COUNT    : integer := 4;
   DATA_WIDTH  : integer := 32;
   IFNUM_OFFSET : integer := 0
);
port (
   RX_DATA  : in std_logic_vector(DATA_WIDTH - 1 downto 0);
   RX_REM   : in std_logic_vector(log2(DATA_WIDTH / 8) - 1 downto 0);
   RX_EOP_N : in std_logic;

   --* Extracted interface number (bit map)
   IFNUM    : out std_logic_vector(TX_COUNT - 1 downto 0)
);
end entity;


-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

architecture full of ifnum_extract is

   constant OFFSET_IN_WORD : integer := IFNUM_OFFSET mod DATA_WIDTH;
   constant DATA_SIZE      : integer := DATA_WIDTH / 8;
   constant LAST_BYTE      : integer := (IFNUM_OFFSET / 8) mod DATA_SIZE;

   signal extracted_ifnum  : std_logic_vector(TX_COUNT - 1 downto 0);

begin

   extracted_ifnum <= RX_DATA(OFFSET_IN_WORD + TX_COUNT - 1 downto OFFSET_IN_WORD);

   IFNUM <= extracted_ifnum when LAST_BYTE <= RX_REM or RX_EOP_N = '1' else
            (others => '0');

end architecture;

