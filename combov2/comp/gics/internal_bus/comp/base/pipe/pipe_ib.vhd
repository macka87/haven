--
-- pipe_ib.vhd: Internal Bus Pipeline
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
--               ENTITY DECLARATION -- Internal Bus Pipeline                 --
-- ---------------------------------------------------------------------------- 

entity IB_PIPE is
   generic(
      -- Data Width (1-128)
      DATA_WIDTH     : integer := 64;
      -- Use output register
      USE_OUTREG     : boolean := false;
      -- Fake pipe (wires only)
      FAKE_PIPE      : boolean := false
   );   
   port(
      -- Common interface -----------------------------------------------------
      CLK            : in std_logic;
      RESET          : in std_logic;
      
      -- Input interface ------------------------------------------------------
      IN_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_SOF_N       : in  std_logic;
      IN_EOF_N       : in  std_logic;
      IN_SRC_RDY_N   : in  std_logic;
      IN_DST_RDY_N   : out std_logic;
 
      -- Output interface -----------------------------------------------------
      OUT_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_SOF_N      : out std_logic;
      OUT_EOF_N      : out std_logic;
      OUT_SRC_RDY_N  : out std_logic;
      OUT_DST_RDY_N  : in  std_logic
   );
end entity IB_PIPE;

-- ----------------------------------------------------------------------------
--             ARCHITECTURE DECLARATION  --  Internal Bus Pipeline           --
-- ----------------------------------------------------------------------------

architecture ib_pipe_arch of IB_PIPE is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal in_data_aux   : std_logic_vector(DATA_WIDTH+1 downto 0);
   signal out_data_aux  : std_logic_vector(DATA_WIDTH+1 downto 0);
   signal in_src_rdy    : std_logic;
   signal in_dst_rdy    : std_logic;
   signal out_src_rdy   : std_logic;
   signal out_dst_rdy   : std_logic;   
   
begin

   -- -------------------------------------------------------------------------
   --                                  PIPE                                  --
   -- -------------------------------------------------------------------------
   
   PIPE : entity work.PIPE
   generic map(
      DATA_WIDTH  => DATA_WIDTH+2,
      USE_OUTREG  => USE_OUTREG,
      FAKE_PIPE   => FAKE_PIPE
   )
   port map(
      CLK         => CLK,
      RESET       => RESET,
      
      IN_DATA      => in_data_aux,
      IN_SRC_RDY   => in_src_rdy,
      IN_DST_RDY   => in_dst_rdy,

      OUT_DATA     => out_data_aux,
      OUT_SRC_RDY  => out_src_rdy,
      OUT_DST_RDY  => out_dst_rdy
   );
   
   in_data_aux(DATA_WIDTH-1 downto 0) <= IN_DATA;
   in_data_aux(DATA_WIDTH)            <= IN_SOF_N;
   in_data_aux(DATA_WIDTH+1)          <= IN_EOF_N;
   
   OUT_DATA  <= out_data_aux(DATA_WIDTH-1 downto 0); 
   OUT_SOF_N <= out_data_aux(DATA_WIDTH)   or not out_src_rdy;
   OUT_EOF_N <= out_data_aux(DATA_WIDTH+1) or not out_src_rdy;
   
   in_src_rdy    <= not IN_SRC_RDY_N;
   out_dst_rdy   <= not OUT_DST_RDY_N;
   
   IN_DST_RDY_N  <= not in_dst_rdy;
   OUT_SRC_RDY_N <= not out_src_rdy;
   
end ib_pipe_arch;



