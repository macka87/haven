--
-- endpoint_master_64.vhd : Internal Bus Master Endpoint (data width : 64 bits)
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 
use work.ib_endpoint_pkg.all; 

-- ----------------------------------------------------------------------------
--      ENTITY DECLARATION -- IB Master Endpoint (data width : 64 bits)      -- 
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_MASTER_64 is
   generic(
      -- Address Width (1-32)
      ADDR_WIDTH         : integer := 32;   
      -- Endpoint Address Space 
      ENDPOINT_BASE      : std_logic_vector(31 downto 0) := X"11111111";
      ENDPOINT_LIMIT     : std_logic_vector(31 downto 0) := X"44444444";
      -- Endpoint is connected to
      CONNECTED_TO       : t_ib_comp := SWITCH_MASTER;      
      -- Strict Transaction Order
      STRICT_ORDER       : boolean := false;      
      -- Data alignment (to dst. address)       
      DATA_REORDER       : boolean := false;
      -- Read type (CONTINUAL/PACKET)
      READ_TYPE          : t_ibrd_type := CONTINUAL;
      -- The number of reads in-process
      READ_IN_PROCESS    : integer :=  1;
      -- Buffers Sizes
      INPUT_BUFFER_SIZE  : integer := 16; 
      OUTPUT_BUFFER_SIZE : integer := 16      
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK                : in std_logic;  
      RESET              : in std_logic;  

      -- IB Interface ---------------------------------------------------------
      IB                 : inout t_ib64;
      -- User Interface -------------------------------------------------------
      WR                 : inout t_ibwr64;
      RD                 : inout t_ibrd64;
      -- Bus Master Interface -------------------------------------------------
      BM                 : inout t_ibbm64
   ); 
end entity IB_ENDPOINT_MASTER_64;

-- ----------------------------------------------------------------------------
--   ARCHITECTURE DECLARATION -- IB Master Endpoint (data width : 64 bits)   --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_master_64_arch of IB_ENDPOINT_MASTER_64 is

begin

   U_ib_endpoint: entity work.IB_ENDPOINT
   generic map (
      -- Data Width (8-128)
      DATA_WIDTH         => 64,
      -- Address Width (1-32)
      ADDR_WIDTH         => ADDR_WIDTH,
      -- Bus Master Enable
      BUS_MASTER_ENABLE  => true,
      -- Endpoint Address Space 
      ENDPOINT_BASE      => ENDPOINT_BASE,
      ENDPOINT_LIMIT     => ENDPOINT_LIMIT,
      -- Endpoint is connected to
      CONNECTED_TO       => CONNECTED_TO,
      -- Strict Transaction Order
      STRICT_ORDER       => STRICT_ORDER,
      -- Data alignment (to dst. address)       
      DATA_REORDER       => DATA_REORDER,
      -- Read type (CONTINUAL/PACKET)
      READ_TYPE          => READ_TYPE,
      -- The number of reads in-process
      READ_IN_PROCESS    => READ_IN_PROCESS,
      -- Buffers Sizes
      INPUT_BUFFER_SIZE  => INPUT_BUFFER_SIZE,  
      OUTPUT_BUFFER_SIZE => OUTPUT_BUFFER_SIZE  
   )
   port map (
      -- Common interface -----------------------------------------------------
      CLK                => CLK,
      RESET              => RESET,

      -- IB Interface ---------------------------------------------------------
      IB_DOWN_DATA       => IB.DOWN.DATA,     
      IB_DOWN_SOF_N      => IB.DOWN.SOF_N,    
      IB_DOWN_EOF_N      => IB.DOWN.EOF_N,    
      IB_DOWN_SRC_RDY_N  => IB.DOWN.SRC_RDY_N,
      IB_DOWN_DST_RDY_N  => IB.DOWN.DST_RDY_N,
                                             
      IB_UP_DATA         => IB.UP.DATA,       
      IB_UP_SOF_N        => IB.UP.SOF_N,      
      IB_UP_EOF_N        => IB.UP.EOF_N,      
      IB_UP_SRC_RDY_N    => IB.UP.SRC_RDY_N,  
      IB_UP_DST_RDY_N    => IB.UP.DST_RDY_N,  
                         
      -- Write Interface ------------------------------------------------------
      WR_REQ             => WR.REQ,   
      WR_RDY             => WR.RDY,   
      WR_DATA            => WR.DATA,  
      WR_ADDR            => WR.ADDR,  
      WR_BE              => WR.BE,    
      WR_LENGTH          => WR.LENGTH,
      WR_SOF             => WR.SOF,   
      WR_EOF             => WR.EOF,   
                              
      -- Read Interface -------------------------------------------------------
      RD_REQ             => RD.REQ,        
      RD_ARDY_ACCEPT     => RD.ARDY_ACCEPT,
      RD_ADDR            => RD.ADDR,       
      RD_BE              => RD.BE,         
      RD_LENGTH          => RD.LENGTH,     
      RD_SOF             => RD.SOF,        
      RD_EOF             => RD.EOF,        
                                         
      RD_DATA            => RD.DATA,       
      RD_SRC_RDY         => RD.SRC_RDY,    
      RD_DST_RDY         => RD.DST_RDY,    
                              
      -- Bus Master Interface -------------------------------------------------
      BM_DATA            => BM.TRANS.DATA,     
      BM_SOF_N           => BM.TRANS.SOF_N,      
      BM_EOF_N           => BM.TRANS.EOF_N,      
      BM_SRC_RDY_N       => BM.TRANS.SRC_RDY_N,
      BM_DST_RDY_N       => BM.TRANS.DST_RDY_N,
                                       
      BM_TAG             => BM.DONE.TAG,      
      BM_TAG_VLD         => BM.DONE.TAG_VLD  
   );    
           
end ib_endpoint_master_64_arch;



