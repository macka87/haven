--
-- buffer_bram_arch.vhd : Internal Bus BlockRAM Buffer architecture
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

-- ----------------------------------------------------------------------------
--         ARCHITECTURE DECLARATION  --  Internal Bus BlockRAM Buffer        --
-- ----------------------------------------------------------------------------

architecture ib_buffer_bram_arch of IB_BUFFER_BRAM is

   -- -------------------------------------------------------------------------
   --                            Signal declaration                          --
   -- -------------------------------------------------------------------------

   signal fifo_data_in   : std_logic_vector(DATA_WIDTH+1 downto 0);
   signal fifo_lstblk    : std_logic;
   signal fifo_wr        : std_logic;
   signal fifo_data_out  : std_logic_vector(DATA_WIDTH+1 downto 0);
   signal fifo_rd        : std_logic;
   signal fifo_dv        : std_logic;

   -- -------------------------------------------------------------------------
   --                          BRAM_TYPE calculation                         --
   -- -------------------------------------------------------------------------

   function bram_type_func return integer is
      variable aux : integer;
   begin
      if (DATA_WIDTH < 32) then
         aux := 18;
      else
         aux := 36;
      end if;
      
      return aux;
   end function; 
   
begin

   -- -------------------------------------------------------------------------
   --                         INPUT/OUTPUT INTERFACE                         --
   -- -------------------------------------------------------------------------  

   fifo_data_in   <= IN_EOF_N & IN_SOF_N & IN_DATA;
   fifo_wr        <= not IN_SRC_RDY_N and not fifo_lstblk;
   IN_DST_RDY_N   <= fifo_lstblk or RESET;

   OUT_DATA       <= fifo_data_out(DATA_WIDTH-1 downto 0);
   OUT_SOF_N      <= fifo_data_out(DATA_WIDTH);
   OUT_EOF_N      <= fifo_data_out(DATA_WIDTH+1);
   OUT_SRC_RDY_N  <= not fifo_dv;
   fifo_rd        <= not OUT_DST_RDY_N;

   -- -------------------------------------------------------------------------
   --                         BRAM FIFO INSTANTIATION                        --
   -- -------------------------------------------------------------------------  

   FIFO_BRAM_U : entity work.FIFO_BRAM
   generic map (
      ITEMS          => ITEMS,
      BLOCK_SIZE     =>  1,
      BRAM_TYPE      => bram_type_func,
      DATA_WIDTH     => DATA_WIDTH+2,
      AUTO_PIPELINE  => true
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,

      -- Write interface
      WR             => fifo_wr, 
      DI             => fifo_data_in,
      FULL           => open,
      LSTBLK         => fifo_lstblk,

      -- Read interface
      RD             => fifo_rd,
      DO             => fifo_data_out,
      DV             => fifo_dv,
      EMPTY          => open
   );
 
end ib_buffer_bram_arch;



