--
-- I2C_SW.vhd: SW interface for I2C Protocol
-- Copyright (C) 2006 CESNET
-- Author(s): Pecenka Tomas <pecenka at liberouter.org>
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
use ieee.std_logic_arith.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity I2C_SW is
   port(
      CLK        : in std_logic;   -- Clock 4x I2C clock
      RESET      : in std_logic;   -- Reset

      WR_DATA    : in std_logic;   -- Data for I2C_DATA
      WR_DATA_Z  : in std_logic;   -- Controls I2C_DATA Z-buffer
      WR_CLK     : in std_logic;   -- Data for I2C_CLK
      WR_CLK_Z   : in std_logic;   -- Controls I2C_CLK Z-buffer
      WRITE      : in std_logic;   -- Write data to DATA and CLK registers

      RD_DATA    : out std_logic;  -- Data from I2C_DATA
      RD_CLK     : out std_logic;  -- Data from I2C_CLK
   
      I2C_CLK    : inout std_logic;-- I2C Clock
      I2C_DATA   : inout std_logic -- I2C Data
   );
end entity I2C_SW;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture I2C_SW_arch of I2C_SW is

   -- IOB registers
   signal regiob_data_out  : std_logic;
   signal regiob_data_zbuf : std_logic; 
   signal regiob_data_in   : std_logic;
   signal regiob_clk_out   : std_logic; 
   signal regiob_clk_zbuf  : std_logic;
   signal regiob_clk_in    : std_logic;

begin


-- #######################################################################
--                   IOB cells - Output / input part 
-- #######################################################################

RD_DATA <= regiob_data_in;
RD_CLK  <= regiob_clk_in;

-- IOB input registers ---------------------------------------------------
regiob_inputp: process(RESET, CLK)
begin
   if (RESET = '1') then
      regiob_data_in <= '0';
      regiob_clk_in  <= '0';
   elsif (CLK'event AND CLK = '1') then
      regiob_data_in <= I2C_DATA;
      regiob_clk_in  <= I2C_CLK;
   end if;
end process;

-- IOB output registers --------------------------------------------------
regiob_outputp: process(RESET, CLK)
begin
   if (RESET = '1') then
      regiob_data_out  <= '0';
      regiob_data_zbuf <= '1';
      regiob_clk_out   <= '0';
      regiob_clk_zbuf  <= '1';
   elsif (CLK'event AND CLK = '0') then
      if (WRITE = '1') then
         regiob_data_out  <= WR_DATA;
         regiob_data_zbuf <= WR_DATA_Z;
         regiob_clk_out   <= WR_CLK;
         regiob_clk_zbuf  <= WR_CLK_Z;
      end if;
   end if;
end process;

-- IOB ZBuffers ----------------------------------------------------------

-- tri-state buffer I2C_DATA
process (regiob_data_zbuf, regiob_data_out) is
begin
   if regiob_data_zbuf = '1' then
      I2C_DATA <= 'Z';
   else
      I2C_DATA <= regiob_data_out;
   end if;
end process;

-- tri-state buffer I2C_CLK
process (regiob_clk_zbuf, regiob_clk_out) is
begin
   if regiob_clk_zbuf = '1' then
      I2C_CLK <= 'Z';
   else
      I2C_CLK <= regiob_clk_out;
   end if;
end process;

end architecture I2C_SW_arch;

