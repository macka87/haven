--
-- arbitr_unitvhd: Round-robin arbitration unit
-- Copyright (C) 2006 CESNET
-- Author(s): Patrik Beck <beck@liberouter.org>
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
entity RR_ARBITER_UNIT is
   generic(
      PORTS                 : integer := 2 --minimum is 2
   );      
   port(
      -- port requerst
      RQ                    : in std_logic_vector(PORTS-1 downto 0); -- request from port
      CHNG                  : in std_logic; -- change the writer (next writer in round)
      GARANT                : in std_logic; -- this unit is responsible for choosing next writer

      ACK                   : out std_logic_vector(PORTS-1 downto 0); -- acknowledgement vector
      ACK_W                 : out std_logic  -- write the ack. vector
      
      );
end entity RR_ARBITER_UNIT;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture RR_ARBITER_UNIT_ARCH of RR_ARBITER_UNIT is
   
   type t_sig_ack is array(0 to PORTS-1) of std_logic_vector(PORTS-1 downto 0);
   signal sig_ack : t_sig_ack;

begin
   
ACK_W <= GARANT and chng;

sig_ack(0) <= RQ;

MASK_G1: for i in 0 to PORTS-2 generate

   MASK_G2: for j in 0 to i generate
      sig_ack(i + 1)(j) <= sig_ack(i)(j);      
   end generate;

   MASK_G3: for j in i + 1 to PORTS-1 generate
      sig_ack(i + 1)(j) <= sig_ack(i)(j) and not sig_ack(0)(i);
   end generate;
   
end generate;

ACK <= (others => '0') when GARANT='0' else sig_ack(PORTS-1);

end architecture RR_ARBITER_UNIT_ARCH;

