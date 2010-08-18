-- uh_fifo.vhd: Unified Header FIFO, full implementation of a single UH FIFO
-- Copyright (C) 2003 CESNET, Liberouter project
-- Author(s): Filip Hofer    <fil@liberouter.org>
--            Tomas Martinek <martinek@liberouter.org>
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
use IEEE.STD_LOGIC_1164.ALL;

-- ----------------------------------------------------------------------
--  Entity declaration: UH FIFO
-- ----------------------------------------------------------------------
entity UH_FIFO is
   port(
      RESET      : in std_logic;

      -- HFE interface
      HFE_DOUT   : in std_logic_vector(15 downto 0); -- SOR data output
      HFE_ADDR   : in std_logic_vector(5 downto 0);  -- SOR address
      HFE_RDY    : out std_logic;   -- Control signals
      HFE_REQ    : in std_logic;
      HFE_WEN    : in std_logic;
      HFE_CLK    : in std_logic;

      -- LUP interface
      LUP_SR_VALID    : out std_logic;       -- If cell contains unfied header
      LUP_SR_CLEAN    : in  std_logic;       -- Clean addressed cell
      LUP_DATA        : out std_logic_vector(31 downto 0); -- UH data
      LUP_ADDR        : in  std_logic_vector(8 downto 0);  -- Cell addr.
      LUP_CLK         : in std_logic;

      -- Address Decoder interface
      ADC_RD         : in std_logic;
      ADC_ADDR       : in std_logic_vector(9 downto 0);
      ADC_DO         : out std_logic_vector(31 downto 0)
   );
end UH_FIFO;

