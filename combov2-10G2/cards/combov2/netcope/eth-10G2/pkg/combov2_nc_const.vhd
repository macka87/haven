-- combov2_nc_const.vhd: Non-changeable constants for Combov2 card
-- Copyright (C) 2009 CESNET
-- Author(s): Vaclav Bartos <washek@liberouter.org>
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

package combov2_nc_const is

--    Some address spaces is now specified by MI_Splitters connection.
--    Current address spaces:
--    00000000-000003FF: ID
--    00000400-000007FF: I2C
--    00000800-00003FFF: (unused)
--    00004000-00007FFF: Network mod
--    00008000-0000BFFF: TSU
--    0000C000-0000FFFF: DMA mod
--    00010000-0006FFFF: IFC1, IFC2, LSC1, LSC2, LSC3, LSC4
--    00070000-0008FFFF: (unsued)
--    00080000-01FFFFFF: USER
--

   -- -------------------------------------------------------------------------
   -- ----------------------- Internal Bus constants --------------------------
   -- -------------------------------------------------------------------------
   
   -- SWITCH 0 ----------------------------------------------------------------
   -- The number of headers to be stored
   constant IBS0_HEADER_NUM        : integer:=1;
   -- Port 1 Address Space
   constant IBS0_PORT1_BASE        : std_logic_vector:=X"00000000";
   constant IBS0_PORT1_LIMIT       : std_logic_vector:=X"02000000";
   -- Port 2 Address Space
   constant IBS0_PORT2_BASE        : std_logic_vector:=X"02000000"; 
   constant IBS0_PORT2_LIMIT       : std_logic_vector:=X"C2000000";
   
   -- TRANSFORMER 0 -----------------------------------------------------------
   -- Input buffers
   constant IBT0_UP_INPUT_BUFFER_ITEMS    : integer:=2;
   constant IBT0_DOWN_INPUT_BUFFER_ITEMS  : integer:=8;
   -- Output pipes
   constant IBT0_UP_OUTPUT_PIPE    : boolean:=true;
   constant IBT0_DOWN_OUTPUT_PIPE  : boolean:=false;
   
   -- ENDPOINT0 ---------------------------------------------------------------
   -- Endpoint Address Space 
   constant IBE0_ENDPOINT_BASE         : std_logic_vector:=X"00000000";
   constant IBE0_ENDPOINT_LIMIT        : std_logic_vector:=X"02000000";
   -- Data alignment (to dst. address)
   constant IBE0_DATA_REORDER          : boolean:=false;
   -- Buffers Sizes
   constant IBE0_INPUT_BUFFER_SIZE     : integer:=2;
   constant IBE0_OUTPUT_BUFFER_SIZE    : integer:=2;
   
   -- MI Splitters ------------------------------------------------------------
   constant SPLIT0_PIPE         : boolean:=true;
   constant SPLIT0_PIPE_OUTREG  : boolean:=true;
   
   constant SPLIT1_PIPE         : boolean:=false;
   constant SPLIT1_PIPE_OUTREG  : boolean:=true;
   
   constant SPLIT2_PIPE         : boolean:=true;
   constant SPLIT2_PIPE_OUTREG  : boolean:=true;
   
   constant SPLIT3_PIPE         : boolean:=false;
   constant SPLIT3_PIPE_OUTREG  : boolean:=true;
   
   -- MI Pipes ----------------------------------------------------------------
   constant PIPE_DMA            : boolean:=true;
   constant PIPE_DMA_OUTREG     : boolean:=true;
   
   constant PIPE_TSU            : boolean:=false;
   constant PIPE_TSU_OUTREG     : boolean:=false;
   
   constant PIPE_NET            : boolean:=false;
   constant PIPE_NET_OUTREG     : boolean:=true;
   
   -- TSU_CV2 constants -------------------------------------------------------
   -- both frequencies should be higher or same as pacodag ifc frequency
      -- frequency from gps ptm card
   constant PTM_PRECISE_CLK_FREQUENCY : integer      := 160000000; -- frequency of PTM crystal clk in Hz
      -- frequency from backup clk source signal on cv2 card
   constant COMBOV2_REF_CLK_FREQUENCY : integer      := 166666666; -- frequency from CLK_GEN @ 166 MHz in Hz
   -- -------------------------------------------------------------------------

end combov2_nc_const;

package body combov2_nc_const is
end combov2_nc_const;


