-- nicprobe_ent.vhd: Entity of NIC Probe FrameLink debug unit
-- Copyright (C) 2009 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_NICPROBE is

   generic(
      -- Data width of one input interface (16, 32, 64, 128 bits)
      FL_WIDTH             : integer := 128
   );

   port(
      -- Common signals
      -- clock sigal
      CLK               : in std_logic;
      -- asynchronous reset, active in '1'
      RESET             : in std_logic;

      -- FrameLink interface of the debugging channel
      -- Note that all signals are input
      DATA              : in std_logic_vector(FL_WIDTH-1 downto 0);
      DREM              : in std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);
      SOF_N             : in std_logic;
      SOP_N             : in std_logic;
      EOP_N             : in std_logic;
      EOF_N             : in std_logic;
      TX_SRC_RDY_N      : in std_logic;
      RX_DST_RDY_N      : in std_logic;

      -- Processes frame is valid NIC frame
      FRAME_OK          : out std_logic;
      -- FRAME_OK is valid
      FRAME_OK_VLD      : out std_logic

   );

end entity FL_NICPROBE;

