-- dma_64b_16rx2tx_const.vhd: User constants for 64b 16RX+2TX DMA Module
-- Copyright (C) 2010 CESNET
-- Author(s):  Viktor Pus <pus@liberouter.org>
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
use IEEE.std_logic_1164.all;

use work.ib_ifc_pkg.all;
use work.math_pack.all;

package dma_mod_128b_nrx0tx_gen_const is

      -- Note that FL_WIDTH is the actual RX width of the DMA module while RX_FL_WIDTH is the size
      -- of the module itself. If you find this naming convenction weired you are not alone. Blame
      -- Netkoup and their leader for thisa situation
      -- Also see https://www.liberouter.org/trac/netcope/ticket/333#comment:1
      constant FL_WIDTH       : integer := 128;
      constant FL_REM_WIDTH   : integer := log2(FL_WIDTH/8);


      -- ======================================================================
      -- !!! This part is parsed by script.
      -- !!! Values must be a numeric constants, without any calculation.
      constant RX_IFC_COUNT   : integer := 8; 
      constant RX_BUFFER_SIZE : integer := 4096;
      constant RX_FL_WIDTH    : integer := 64;
      constant RX_REM_WIDTH   : integer := 3;

      constant TX_IFC_COUNT   : integer := 2; -- FIXME should be 0!
      constant TX_BUFFER_SIZE : integer := 4096;
      constant TX_FL_WIDTH    : integer := 64;
      -- ------------------------------------------------------------
      constant RX_BUFFER_ADDR : std_logic_vector(31 downto 0) := X"02000000";
      constant TX_BUFFER_ADDR : std_logic_vector(31 downto 0) := X"02100000";
      -- !!! End of part parsed by script
      -- ======================================================================

      constant RX_DISCARD_EN   : boolean := false;

      -- Descriptor manager generics
      constant DESC_BASE_ADDR  : std_logic_vector(31 downto 0) := X"02200000";
      constant DESC_BLOCK_SIZE : integer := 16;

      -- --------------- Internal Bus Endpoint --------------------------------
      -- BASE and LIMIT used only if CONNECTED_TO = SWITCH_SLAVE
      constant IB_EP_CONNECTED_TO       : t_ib_comp := SWITCH_SLAVE;
      constant IB_EP_ENDPOINT_BASE      : std_logic_vector(31 downto 0) := X"02000000";
      constant IB_EP_ENDPOINT_LIMIT     : std_logic_vector(31 downto 0) := X"00300000";
      constant IB_EP_STRICT_ORDER       : boolean := false;
      constant IB_EP_DATA_REORDER       : boolean := false;
      constant IB_EP_READ_IN_PROCESS    : integer := 8;
      constant IB_EP_INPUT_BUFFER_SIZE  : integer := 1;
      constant IB_EP_OUTPUT_BUFFER_SIZE : integer := 1;

end;

package body dma_mod_128b_nrx0tx_gen_const is
end;


