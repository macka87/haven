-- default_const.vhd: Default constants for Generic DMA Module
-- Copyright (C) 2008 CESNET
-- Author(s):  Martin Spinler <xspinl00@stud.fit.vutbr.cz>
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

package dma_ctrl_generic_default_const is
   -- This file is parsed, if DMA Ctrls are compiled by make in their directory.
   -- These constant should correspond with generic values in dma_module.
   -- Set also in tbench/test_pkg.sv
   constant RX_IFC_COUNT             : integer := 4; 
   constant RX_BUFFER_SIZE           : integer := 4096;
   constant RX_FL_WIDTH              : integer := 64;

   constant TX_IFC_COUNT             : integer := 2;
   constant TX_BUFFER_SIZE           : integer := 4096;
   constant TX_FL_WIDTH              : integer := 64;

   -- These constants are used only by controllers, should correspond with address decoders in dma_module
   constant RX_BUFFER_ADDR           : std_logic_vector(31 downto 0) := X"02000000";
   constant TX_BUFFER_ADDR           : std_logic_vector(31 downto 0) := X"02100000";
end dma_ctrl_generic_default_const;
