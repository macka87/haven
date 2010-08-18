--
-- fl_frame_spliter_ent.vhd: Dividing frame link into two parts 
-- Copyright (C) 2006 CESNET
-- Author(s): Jan Kastil <xkasti00@stud.fit.vutbr.cz>
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
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use work.fl_pkg.all;
use work.fl_sim_oper.all;
-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity Frame_spliter is
   generic(
      -- FrameLink data bus width
      -- only 16, 32, 64 and 128 bit fl bus supported
      FL_WIDTH_IN  : integer := 32;
      FL_WIDTH_OUT1 : integer := 32;
      FL_WIDTH_OUT2 : integer := 32;
      Split_Pos   : integer := 1
   );
   port(
      -- Common interface
      FL_RESET            : in  std_logic;
      FL_CLK              : in  std_logic;

      -- Frame link Interface
      RX_DATA             : in std_logic_vector(FL_WIDTH_IN-1 downto 0);
      RX_REM              : in std_logic_vector(log2(FL_WIDTH_IN/8)-1 downto 0);
      RX_SOF_N            : in std_logic;
      RX_EOF_N            : in std_logic;
      RX_SOP_N            : in std_logic;
      RX_EOP_N            : in std_logic;
      RX_SRC_RDY_N        : in std_logic;
      RX_DST_RDY_N        : out  std_logic;

      TX_DATA_OUT1        : out std_logic_vector(FL_WIDTH_OUT1-1 downto 0);
      TX_REM_OUT1         : out std_logic_vector(log2(FL_WIDTH_OUT1/8)-1 downto 0);
      TX_SOF_N_OUT1       : out std_logic;
      TX_EOF_N_OUT1       : out std_logic;
      TX_SOP_N_OUT1       : out std_logic;
      TX_EOP_N_OUT1       : out std_logic;
      TX_SRC_RDY_N_OUT1   : out std_logic;
      TX_DST_RDY_N_OUT1   : in  std_logic;

      TX_DATA_OUT2        : out std_logic_vector(FL_WIDTH_OUT2-1 downto 0);
      TX_REM_OUT2         : out std_logic_vector(log2(FL_WIDTH_OUT2/8)-1 downto 0);
      TX_SOF_N_OUT2       : out std_logic;
      TX_EOF_N_OUT2       : out std_logic;
      TX_SOP_N_OUT2       : out std_logic;
      TX_EOP_N_OUT2       : out std_logic;
      TX_SRC_RDY_N_OUT2   : out std_logic;
      TX_DST_RDY_N_OUT2   : in  std_logic
     );
end entity;

