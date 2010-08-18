
-- tx_buffer_ent.vhd: Entity for Aurvc TX buffer 
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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
-- TODO: - 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on
use work.math_pack.all; 

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity tx_buffer is
   generic (
      DATA_PATHS           : integer;     -- Number of bytes of data port
      CHANNEL_SIZE         : integer;     -- Number of items in channel buffer
      BYTE_QUOTA           : integer      -- Byte quota for this channel (see documentation for more information)
   );
   port (
      -- Common Input
      RESET                : in std_logic;
      FLCLK                : in std_logic;   -- FrameLink Interface clock

      -- FrameLink TX Interface
      TX_D             : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      TX_REM           : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      TX_SRC_RDY_N     : in std_logic;
      TX_SOF_N         : in std_logic;
      TX_SOP_N         : in std_logic;
      TX_EOF_N         : in std_logic;
      TX_EOP_N         : in std_logic;
      TX_DST_RDY_N     : out std_logic;

      -- AURVC_Core Interface
      BUFFER_CLK        : in std_logic;
      BUFFER_DATA       : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      BUFFER_REM        : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      BUFFER_EOP        : out std_logic;
      BUFFER_DV         : out std_logic;
      BUFFER_READ       : in std_logic;
      BUFFER_EMPTY      : out std_logic;
      BYTE_QUOTA_MET    : out std_logic;
      BYTE_QUOTA_RST    : in std_logic

   );
end tx_buffer;

