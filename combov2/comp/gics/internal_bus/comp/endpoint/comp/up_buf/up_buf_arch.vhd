--
-- up_buf_arch.vhd : Internal Bus Endpoint Up Buffer architecture
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
--       ARCHITECTURE DECLARATION  --  Internal Bus Endpoint Up Buffer       --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_up_buf_arch of IB_ENDPOINT_UP_BUF is
 
begin

   -- -------------------------------------------------------------------------
   --                          WITHOUT OUTPUT BUFFER                         --
   -- -------------------------------------------------------------------------

   OUTPUT_BUFFER_GEN0: if (OUTPUT_BUFFER_SIZE = 0) generate

      OUT_DATA      <= IN_DATA;
      OUT_SOF_N     <= IN_SOF_N;
      OUT_EOF_N     <= IN_EOF_N;    
      OUT_SRC_RDY_N <= IN_SRC_RDY_N;
      
      IN_DST_RDY_N  <= OUT_DST_RDY_N;
   
   end generate;

   -- -------------------------------------------------------------------------
   --                           WITH IB PIPE ONLY                            --
   -- -------------------------------------------------------------------------
   
   OUTPUT_BUFFER_GEN1: if (OUTPUT_BUFFER_SIZE = 1 or
                           OUTPUT_BUFFER_SIZE = 2) generate

      U_output_pipe : entity work.IB_PIPE
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         USE_OUTREG     => (OUTPUT_BUFFER_SIZE = 2)
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,
         
         IN_DATA        => IN_DATA,
         IN_SOF_N       => IN_SOF_N,
         IN_EOF_N       => IN_EOF_N,    
         IN_SRC_RDY_N   => IN_SRC_RDY_N,
         IN_DST_RDY_N   => IN_DST_RDY_N,
                                          
         OUT_DATA       => OUT_DATA,     
         OUT_SOF_N      => OUT_SOF_N,    
         OUT_EOF_N      => OUT_EOF_N,    
         OUT_SRC_RDY_N  => OUT_SRC_RDY_N,
         OUT_DST_RDY_N  => OUT_DST_RDY_N
      );                
      
   end generate;

   -- -------------------------------------------------------------------------
   --                           WITH OUTPUT BUFFER                           --
   -- -------------------------------------------------------------------------

   OUTPUT_BUFFER_GEN:  if (OUTPUT_BUFFER_SIZE > 2) generate

      U_output_buffer : entity work.IB_BUFFER_SH
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         ITEMS          => OUTPUT_BUFFER_SIZE
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,
         
         IN_DATA        => IN_DATA,
         IN_SOF_N       => IN_SOF_N,
         IN_EOF_N       => IN_EOF_N,    
         IN_SRC_RDY_N   => IN_SRC_RDY_N,
         IN_DST_RDY_N   => IN_DST_RDY_N,
                        
         OUT_DATA       => OUT_DATA,     
         OUT_SOF_N      => OUT_SOF_N,    
         OUT_EOF_N      => OUT_EOF_N,    
         OUT_SRC_RDY_N  => OUT_SRC_RDY_N,
         OUT_DST_RDY_N  => OUT_DST_RDY_N
      );                
      
   end generate;   
                              
end ib_endpoint_up_buf_arch;   



