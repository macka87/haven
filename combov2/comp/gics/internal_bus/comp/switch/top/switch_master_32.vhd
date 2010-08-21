--
-- switch_master_32.vhd : Internal Bus Master Switch (data width : 32 bits)
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
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

use work.ib_ifc_pkg.all;

-- ----------------------------------------------------------------------------
--       ENTITY DECLARATION -- IB Master Switch (data width : 32 bits)       -- 
-- ----------------------------------------------------------------------------

entity IB_SWITCH_MASTER_32 is
   generic(
      -- The number of headers to be stored
      HEADER_NUM   : integer:=  1;
      -- Port 1 Address Space
      PORT1_BASE   : std_logic_vector(31 downto 0) := X"11111111";
      PORT1_LIMIT  : std_logic_vector(31 downto 0) := X"11111111";
      -- Port 2 Address Space
      PORT2_BASE   : std_logic_vector(31 downto 0) := X"22222222"; 
      PORT2_LIMIT  : std_logic_vector(31 downto 0) := X"22222222"
   );   
   port(
      -- Common interface -----------------------------------------------------   
      CLK   : in std_logic; -- FPGA clock
      RESET : in std_logic; -- Reset active high 
      
      -- Switch Ports ---------------------------------------------------------
      PORT0 : inout t_ib32; -- Upstream port   #0
      PORT1 : inout t_ib32; -- Downstream port #1
      PORT2 : inout t_ib32  -- Downstream port #2
   );
end entity IB_SWITCH_MASTER_32;

-- ----------------------------------------------------------------------------
--    ARCHITECTURE DECLARATION -- IB Master Switch (data width : 32 bits)    --
-- ----------------------------------------------------------------------------

architecture ib_switch_master_32_arch of IB_SWITCH_MASTER_32 is

begin

   U_ib_switch_master: entity work.IB_SWITCH_MASTER
   generic map(
      -- Data Width (1-128)
      DATA_WIDTH   => 32,
      -- The number of headers to be stored
      HEADER_NUM   => HEADER_NUM,  
      -- Port 1 Address Space
      PORT1_BASE   => PORT1_BASE, 
      PORT1_LIMIT  => PORT1_LIMIT,
      -- Port 2 Address Space
      PORT2_BASE   => PORT2_BASE, 
      PORT2_LIMIT  => PORT2_LIMIT
   )
   port map(
      -- Common interface -----------------------------------------------------
      CLK                  => CLK,  
      RESET                => RESET,
      
      -- Upstream Port #0 -----------------------------------------------------
      PORT0_DOWN_DATA      => PORT0.DOWN.DATA,     
      PORT0_DOWN_SOF_N     => PORT0.DOWN.SOF_N,     
      PORT0_DOWN_EOF_N     => PORT0.DOWN.EOF_N,      
      PORT0_DOWN_SRC_RDY_N => PORT0.DOWN.SRC_RDY_N,  
      PORT0_DOWN_DST_RDY_N => PORT0.DOWN.DST_RDY_N, 
      
      PORT0_UP_DATA        => PORT0.UP.DATA,      
      PORT0_UP_SOF_N       => PORT0.UP.SOF_N,      
      PORT0_UP_EOF_N       => PORT0.UP.EOF_N,      
      PORT0_UP_SRC_RDY_N   => PORT0.UP.SRC_RDY_N,  
      PORT0_UP_DST_RDY_N   => PORT0.UP.DST_RDY_N,  

      -- Downstream Port #1 ---------------------------------------------------
      PORT1_DOWN_DATA      => PORT1.DOWN.DATA,     
      PORT1_DOWN_SOF_N     => PORT1.DOWN.SOF_N,      
      PORT1_DOWN_EOF_N     => PORT1.DOWN.EOF_N,      
      PORT1_DOWN_SRC_RDY_N => PORT1.DOWN.SRC_RDY_N,  
      PORT1_DOWN_DST_RDY_N => PORT1.DOWN.DST_RDY_N,  
                                         
      PORT1_UP_DATA        => PORT1.UP.DATA,         
      PORT1_UP_SOF_N       => PORT1.UP.SOF_N,        
      PORT1_UP_EOF_N       => PORT1.UP.EOF_N,        
      PORT1_UP_SRC_RDY_N   => PORT1.UP.SRC_RDY_N,    
      PORT1_UP_DST_RDY_N   => PORT1.UP.DST_RDY_N,    

      -- Downstream Port #2 ---------------------------------------------------
      PORT2_DOWN_DATA      => PORT2.DOWN.DATA,     
      PORT2_DOWN_SOF_N     => PORT2.DOWN.SOF_N,      
      PORT2_DOWN_EOF_N     => PORT2.DOWN.EOF_N,      
      PORT2_DOWN_SRC_RDY_N => PORT2.DOWN.SRC_RDY_N,  
      PORT2_DOWN_DST_RDY_N => PORT2.DOWN.DST_RDY_N,  
                              
      PORT2_UP_DATA        => PORT2.UP.DATA,         
      PORT2_UP_SOF_N       => PORT2.UP.SOF_N,        
      PORT2_UP_EOF_N       => PORT2.UP.EOF_N,        
      PORT2_UP_SRC_RDY_N   => PORT2.UP.SRC_RDY_N,    
      PORT2_UP_DST_RDY_N   => PORT2.UP.DST_RDY_N    
   );
            
end ib_switch_master_32_arch;

                     

