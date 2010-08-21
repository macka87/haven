-- cam_addr_pkg.vhd: CAM address space
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use work.addr_space.all;

-- ----------------------------------------------------------------------------
--                      SW_TXBUF Address Package Declaration
-- ----------------------------------------------------------------------------
package cam_addr_pkg is

   constant CAM_CMD_OFFSET : std_logic_vector(31 downto 0) := X"00000000";
   constant CAM_CMD        : std_logic_vector(31 downto 0) := 
                                   CAM_BASE_ADDR + CAM_CMD_OFFSET;
   
   constant CAM_STATUS_OFFSET : std_logic_vector(31 downto 0) := X"00100000";
   constant CAM_STATUS        : std_logic_vector(31 downto 0) := 
                                   CAM_BASE_ADDR + CAM_STATUS_OFFSET;
   
   constant CAM_MASK_OFFSET : std_logic_vector(31 downto 0) := X"00101000";
   constant CAM_MASK        : std_logic_vector(31 downto 0) := 
                                   CAM_BASE_ADDR + CAM_MASK_OFFSET;
   
   constant CAM_DATA_OFFSET  : std_logic_vector(31 downto 0) := X"00101008";
   constant CAM_DATA         : std_logic_vector(31 downto 0) := 
                                   CAM_BASE_ADDR + CAM_DATA_OFFSET;

   constant CAM_ADDR_OFFSET  : std_logic_vector(31 downto 0) := X"00101008";
   constant CAM_ADDR         : std_logic_vector(31 downto 0) := 
                                   CAM_ADDR + CAM_ADDR_OFFSET;
   
   constant CAM_WRITE_OFFSET  : std_logic_vector(31 downto 0) := X"00101008";
   constant CAM_WRITE         : std_logic_vector(31 downto 0) := 
                                   CAM_BASE_ADDR + CAM_WRITE_OFFSET;
end cam_addr_pkg;

package body cam_addr_pkg is
end cam_addr_pkg;
