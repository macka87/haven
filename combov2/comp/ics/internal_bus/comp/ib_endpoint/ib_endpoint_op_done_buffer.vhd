--
-- ib_endpoint_op_done_buffer.vhd: Internal Bus Busmaster Operation Done Buffer
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
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use work.ib_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_ENDPOINT_OP_DONE_BUFFER is
   port(
      -- Common Interface
      CLK              : in  std_logic;
      RESET            : in  std_logic;
      -- IB_Endpoint Input Interface (Listening for completition transactions)
      RD_COMPL_TAG     : in  std_logic_vector(15 downto 0);
      RD_COMPL_START   : in  std_logic; -- Read completition transaction goes for processing
      RD_COMPL_DONE    : in  std_logic; -- Write/completition transaction is done
      -- BM Tag
      BM_TAG           : in  std_logic_vector(15 downto 0);
      BM_DONE          : in  std_logic;
      -- OP Done Interface
      OP_TAG           : out std_logic_vector(15 downto 0); -- Busmaster Tag
      OP_DONE          : out std_logic  -- BM completition transaction recived
      );
end entity IB_ENDPOINT_OP_DONE_BUFFER;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_ENDPOINT_OP_DONE_BUFFER_ARCH of IB_ENDPOINT_OP_DONE_BUFFER is
         
      signal tag_reg               : std_logic_vector(15 downto 0);
      signal bm_tag_reg            : std_logic_vector(15 downto 0);
      signal bm_tag_vld            : std_logic;
      signal rd_compl_start_reg    : std_logic;
      signal local_op_done         : std_logic;
      signal tag_mux               : std_logic_vector(15 downto 0);

begin

OP_TAG           <= tag_mux;
local_op_done    <= RD_COMPL_DONE and rd_compl_start_reg;
OP_DONE          <= bm_tag_vld or local_op_done;

-- multiplexor tag_mux ------------------------------------------------------
tag_muxp: process(local_op_done, tag_reg, bm_tag_reg)
begin
   case local_op_done is
      when '0' => tag_mux <= bm_tag_reg;
      when '1' => tag_mux <= tag_reg;
      when others => tag_mux <= (others => 'X');
   end case;
end process;


-- register rd_compl_start_reg ------------------------------------------------------
rd_compl_start_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      rd_compl_start_reg <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (RD_COMPL_START = '1') then
         rd_compl_start_reg <= '1';
      end if;
      if (RD_COMPL_DONE = '1') then
         rd_compl_start_reg <= '0';
      end if;
   end if;
end process;


-- register tag_reg -----------------------------------------------------------------
tag_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      tag_reg <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (RD_COMPL_START='1') then
         tag_reg <= RD_COMPL_TAG;
      end if;
   end if;
end process;

-- register bm_tag_reg -----------------------------------------------------------------
bm_tag_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      bm_tag_reg <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (BM_DONE = '1') then
         bm_tag_reg <= BM_TAG;
      end if;
   end if;
end process;

-- register bm_tag_vld -----------------------------------------------------------------
bm_tag_vldp: process(RESET, CLK)
begin
   if (RESET = '1') then
      bm_tag_vld <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (BM_DONE = '1') then
         bm_tag_vld <= '1';
      elsif (local_op_done = '0') then
         bm_tag_vld <= '0';
      end if;
   end if;
end process;


end architecture IB_ENDPOINT_OP_DONE_BUFFER_ARCH;

