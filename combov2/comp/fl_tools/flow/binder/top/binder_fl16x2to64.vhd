-- binder_fl16x2to64.vhd: FrameLink Binder 2x16 -> 64
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
use work.fl_pkg.all;
use work.fl_binder_decl.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity fl_binder_fl16x2to64 is
   generic(
      -- number of parts in one FrameLink frame
      FRAME_PARTS    : integer;
      -- Queue choosing policy
      -- select BlockRAM or LUT memory
      LUT_MEMORY     : boolean := false;
      -- Number of items (INPUT_WIDTH*INPUT_COUNT wide) in LUT memory that can 
      -- be stored for each block
      LUT_BLOCK_SIZE : integer := 16;
      QUEUE_CHOOSING : T_BINDER_QUEUE_POLICY := most_occupied;
      -- if TRUE simple version of FL_BINDER is used instead of complex one
      -- this version composes only from FL_FIFO, TRANSFORMERs and output logic
      SIMPLE_BINDER  : boolean := false
   );
   port(

      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interfaces
      RX0            : inout t_fl16;
      RX1            : inout t_fl16;
      
      -- output interface
      TX             : inout t_fl64
   );
end entity fl_binder_fl16x2to64;

architecture full of fl_binder_fl16x2to64 is
begin
   
   -- FL_BINDER instantiation
   FL_BINDER_I: entity work.FL_BINDER
      generic map(
         INPUT_WIDTH    => 16,
         INPUT_COUNT    => 2,
         OUTPUT_WIDTH   => 64,
         FRAME_PARTS    => FRAME_PARTS,
         LUT_MEMORY     => LUT_MEMORY,
         LUT_BLOCK_SIZE => LUT_BLOCK_SIZE,
         QUEUE_CHOOSING => QUEUE_CHOOSING,
         SIMPLE_BINDER  => SIMPLE_BINDER
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
   
         -- input interfaces
         RX_SOF_N(0)             => RX0.SOF_N,
         RX_SOF_N(1)             => RX1.SOF_N,
   
         RX_SOP_N(0)             => RX0.SOP_N,
         RX_SOP_N(1)             => RX1.SOP_N,
   
         RX_EOP_N(0)             => RX0.EOP_N,
         RX_EOP_N(1)             => RX1.EOP_N,
   
         RX_EOF_N(0)             => RX0.EOF_N,
         RX_EOF_N(1)             => RX1.EOF_N,
   
         RX_SRC_RDY_N(0)         => RX0.SRC_RDY_N,
         RX_SRC_RDY_N(1)         => RX1.SRC_RDY_N,
   
         RX_DST_RDY_N(0)         => RX0.DST_RDY_N,
         RX_DST_RDY_N(1)         => RX1.DST_RDY_N,
   
         RX_DATA(15 downto 0)    => RX0.DATA,
         RX_DATA(31 downto 16)   => RX1.DATA,
   
         RX_REM(0 downto 0)      => RX0.DREM,
         RX_REM(1 downto 1)      => RX1.DREM,
   
         -- output interface
         TX_SOF_N       => TX.SOF_N,
         TX_SOP_N       => TX.SOP_N,
         TX_EOP_N       => TX.EOP_N,
         TX_EOF_N       => TX.EOF_N,
         TX_SRC_RDY_N   => TX.SRC_RDY_N,
         TX_DST_RDY_N   => TX.DST_RDY_N,
         TX_DATA        => TX.DATA,
         TX_REM         => TX.DREM
      );
end architecture full; 

