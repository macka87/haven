-- tx_out.vhd: Output logic for TX.
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

--* Component is intended to solve TX_SRC_RDY_N/TX_DST_RDY_N logic of fl_switch
--* especially when at least one of the TX is not ready to receive data.
--*
--* The unit waits for the TX_DST_RDY_N to be active. After data is successfully 
--* sent to TX, the internal state changes and blocks itself until all other 
--* tx_out components do the same. When REALOD signal comes (is activated) the
--* component reads the IFNUM from the input and resets its state to send again
--* (or to not send when IFNUM comes as zero).
--*
--* The component can be disabled immediately through EN_N signal.
entity tx_out is
port (
   CLK      : in  std_logic;
   RESET    : in  std_logic;
   IFNUM    : in  std_logic;
   EN_N     : in  std_logic;
   RELOAD   : in  std_logic;
   
   TX_SRC_RDY_N   : out std_logic;
   TX_DST_RDY_N   : in  std_logic
);
end entity;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

--* Contains 1 one bit register that holds its state.
architecture full of tx_out is

   signal src_rdy_n : std_logic;
   signal dst_rdy_n : std_logic;

   -- register for a bit of the InterFace NUMber
   signal reg_ifnum     : std_logic;
   signal reg_ifnum_set : std_logic;

   signal tx_ack        : std_logic;

begin

   TX_SRC_RDY_N <= src_rdy_n;
   src_rdy_n <= EN_N or reg_ifnum;
   dst_rdy_n <= TX_DST_RDY_N or EN_N;

   reg_ifnum_set  <= not IFNUM when RELOAD = '1' else
                     tx_ack;

   tx_ack         <= not dst_rdy_n when src_rdy_n = '0' else
                     '1';

   register_ifnum : process(CLK, RESET)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_ifnum <= '1';
         else
            reg_ifnum <= reg_ifnum_set;
         end if;
      end if;
   end process;

end architecture;
