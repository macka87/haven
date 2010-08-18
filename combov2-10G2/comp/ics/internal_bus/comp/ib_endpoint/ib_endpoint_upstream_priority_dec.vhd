--
-- ib_priority_dec.vhd: Internal Bus priority decoder
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
-------------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_ENDPOINT_UPSTREAM_PRIORITY_DEC is
   port(
      -- FPGA control
      CLK                   : in  std_logic;  -- 100  MHz FPGA clock
      RESET                 : in  std_logic;  -- Reset

      -- Input Interface
      IN_RD_RQ              : in  std_logic;
      IN_BM_RQ              : in  std_logic;
      IN_RD_ACK             : out std_logic;
      IN_BM_ACK             : out std_logic;

      -- Output Interface
      OUT_RD_RQ             : out std_logic;
      OUT_BM_RQ             : out std_logic;
      OUT_RD_ACK            : in  std_logic;
      OUT_BM_ACK            : in  std_logic
      );
end entity IB_ENDPOINT_UPSTREAM_PRIORITY_DEC;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_ENDPOINT_UPSTREAM_PRIORITY_DEC_ARCH of IB_ENDPOINT_UPSTREAM_PRIORITY_DEC is
   
   -- priority counter registers
   signal priority_reg0 : std_logic;
   signal change_priority : std_logic;

begin

IN_RD_ACK       <= OUT_RD_ACK;
IN_BM_ACK       <= OUT_BM_ACK;
change_priority <= OUT_RD_ACK or OUT_BM_ACK;

-- register priority_reg0 ------------------------------------------------------
priority_reg0p: process(RESET, CLK)
begin
  if (CLK'event AND CLK = '1') then
    if (RESET = '1') then
      priority_reg0 <= '1';
    elsif (change_priority = '1') then
      priority_reg0 <= not priority_reg0;
    end if;
  end if;
end process;


OUT_RD_RQ <= '1' when  ( (priority_reg0='1' and IN_RD_RQ  = '1') or
                         (priority_reg0='0' and IN_RD_RQ  = '1' and IN_BM_RQ = '0')) else '0'; 
                  
OUT_BM_RQ <= '1' when  ( (priority_reg0='0' and IN_BM_RQ = '1') or
                         (priority_reg0='1' and IN_BM_RQ = '1' and IN_RD_RQ = '0')) else '0'; 
                  
end architecture IB_ENDPOINT_UPSTREAM_PRIORITY_DEC_ARCH;

