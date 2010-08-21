--
-- dma_test.vhd: DMA modul constants for PCIe2IB testing
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
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
use work.ib_pkg.all;
use work.lb_pkg.all;

package dma_test_pkg is

-- ----------------------------------------------------------------------------
--       Internal Bus Data Width
-- ----------------------------------------------------------------------------

   constant IB_DATA_WIDTH     : integer := 64;  

-- ----------------------------------------------------------------------------
--       Internal Bus Switch Parameters
-- ----------------------------------------------------------------------------
   
   constant IB_SWITCH_BASE    : std_logic_vector(31 downto 0) := X"00000000"; 
   constant IB_SWITCH_LIMIT   : std_logic_vector(31 downto 0) := X"00200000";

   constant DOWNSTREAM0_BASE  : std_logic_vector(31 downto 0) := X"00000000";
   constant DOWNSTREAM0_LIMIT : std_logic_vector(31 downto 0) := X"00001100";

   constant DOWNSTREAM1_BASE  : std_logic_vector(31 downto 0) := X"00100000";
   constant DOWNSTREAM1_LIMIT : std_logic_vector(31 downto 0) := X"00004000";

-- ----------------------------------------------------------------------------
--       Local Bus Root Parameters
-- ----------------------------------------------------------------------------

   constant LB_ROOT_BASE      : std_logic_vector(31 downto 0) := X"00000000";
   constant LB_ROOT_LIMIT     : std_logic_vector(31 downto 0) := X"00001100";

-- ----------------------------------------------------------------------------
--       Internal Bus Endpoint (BM) Parameters
-- ----------------------------------------------------------------------------

   constant IB_EP_LIMIT                : std_logic_vector(31 downto 0) := X"00004000";
   constant IB_EP_INPUT_BUFFER_SIZE    : integer:= 0;
   constant IB_EP_OUTPUT_BUFFER_SIZE   : integer:= 0;
   constant IB_EP_READ_REORDER_BUFFER  : boolean:= true;
   constant IB_EP_STRICT_EN            : boolean:= false;

-- ----------------------------------------------------------------------------
--       Local Bus Endpoint Parameters
-- ----------------------------------------------------------------------------

   constant LB_EP_BASE_ADDR            : std_logic_vector(31 downto 0):= X"00000000";
   constant LB_EP_LIMIT                : std_logic_vector(31 downto 0):= X"00000100";
   constant LB_EP_FREQUENCY            : integer:= 100;
   constant LB_EP_BUFFER_EN            : boolean:= false;

-- ----------------------------------------------------------------------------
--       LB2BM Unit Parameters
-- ----------------------------------------------------------------------------

-- ----------------------------------------------------------------------------
--       Memory Parameters
-- ----------------------------------------------------------------------------

   constant IB_MEM_SIZE          : integer := 16384;  -- size of memory in bytes (16kB)
   constant IB_MEM_TYPE          : integer := 0;      -- 0 = BRAM / 1 = DISTMEM

-- ----------------------------------------------------------------------------

end dma_test_pkg;


package body dma_test_pkg is
end dma_test_pkg;

