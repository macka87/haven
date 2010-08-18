--
-- write_ctrl_arch.vhd : Internal Bus Endpoint Write Controller architecture
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
--    ARCHITECTURE DECLARATION  --  Internal Bus Endpoint Write Controller   --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_write_ctrl_arch of IB_ENDPOINT_WRITE_CTRL is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------   

   constant ALIGNZEROES    : std_logic_vector(addr_we_width(DATA_WIDTH, ADDR_WIDTH)-1 downto 0) := (others => '0');

   signal WR_SOF_aux       : std_logic;
   signal WR_EOF_aux       : std_logic;
   signal WR_REQ_aux       : std_logic;
   signal WR_LENGTH_aux    : std_logic_vector(11 downto 0);
   signal WR_ADDR_aux      : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal IB_DST_RDY_N_aux : std_logic;
   signal header_last      : std_logic;
   signal addr_ce          : std_logic;
   signal header           : std_logic;
   signal length_we        : std_logic_vector(length_we_width(DATA_WIDTH)-1 downto 0);
   signal addr_we          : std_logic_vector(addr_we_width(DATA_WIDTH, ADDR_WIDTH)-1 downto 0);
   signal length_align     : std_logic_vector(align_width(DATA_WIDTH)-1 downto 0);
   signal addr_align       : std_logic_vector(align_width(DATA_WIDTH)-1 downto 0);
   
begin

   -- -------------------------------------------------------------------------
   --                             FETCH MARKER                               --
   -- -------------------------------------------------------------------------

   U_fetch_marker : entity work.IB_ENDPOINT_WRITE_CTRL_FETCH_MARKER
   generic map (
      -- Data Width (8-128)
      DATA_WIDTH    => DATA_WIDTH,
      -- Address Width (1-32)
      ADDR_WIDTH    => ADDR_WIDTH      
   )
   port map (
      -- Common interface ---------------------------------
      CLK            => CLK,
      RESET          => RESET,

      -- IB interface -------------------------------------
      SOF_N          => IB_SOF_N,    
      EOF_N          => IB_EOF_N,              
      SRC_RDY_N      => IB_SRC_RDY_N,
      DST_RDY_N      => IB_DST_RDY_N_aux,

      -- Control Interface --------------------------------
      LENGTH_WE      => length_we,
      ADDR_WE        => addr_we,
      HEADER         => header,
      HEADER_LAST    => header_last
   );                

   -- -------------------------------------------------------------------------
   --                              UNPACKER                                  --
   -- -------------------------------------------------------------------------

   U_unpacker : entity work.IB_UNPACKER
   generic map (
      -- Data Width (8-128)
      DATA_WIDTH   => DATA_WIDTH,
      -- Address Width (1-32)
      ADDR_WIDTH   => ADDR_WIDTH
   ) 
   port map (
      -- Common interface ---------------------------------
      CLK          => CLK,
      RESET        => RESET,

      -- Input interface ----------------------------------
      DATA         => IB_DATA,

      -- Output Interface ---------------------------------
      LENGTH       => WR_LENGTH_aux,
      COUNT        => open,
      ADDR32       => WR_ADDR_aux,
      ADDR64       => open,      
      LEN_ALIGN    => length_align,      
      A32_ALIGN    => addr_align,   
      A64_ALIGN    => open,   
      TAG          => open,   
      DONE_FLAG    => open,   

      -- Control Interface ----------------------------------------------------
      LENGTH_WE    => length_we,      
      ADDR32_WE    => addr_we,
      ADDR64_WE    => ALIGNZEROES,
      ADDR32_CE    => addr_ce,
      ADDR64_CE    => '0',
      COUNT_CE     => '0',
      TAG_WE       => '0',
      DONE_FLAG_WE => '0',
      HEADER_LAST  => '0'
   );                 

   WR_LENGTH <= WR_LENGTH_aux;
   WR_ADDR   <= WR_ADDR_aux;
   WR_DATA   <= IB_DATA;
   
   -- -------------------------------------------------------------------------
   --                        BYTE ENABLE GENERATOR                           --
   -- -------------------------------------------------------------------------

   BE_GEN_YES:  if (DATA_WIDTH > 8) generate

      U_be_gen : entity work.IB_BE_GEN
      generic map (
         -- Data Width (8-128)
         DATA_WIDTH   => DATA_WIDTH
      )
      port map (
         -- Common interface ------------------------------
         CLK          => CLK,  
         RESET        => RESET,
         
         -- Input Interface -------------------------------
         LENGTH_ALIGN => length_align,
         ADDR_ALIGN   => addr_align,
         SOF          => WR_SOF_aux,
         EOF          => WR_EOF_aux,
         
         -- Output Interface ------------------------------
         BE           => WR_BE
      );              

   end generate;

   -- -------------------------------------------------------------------------
   --                             WRITE FSM                                  --
   -- -------------------------------------------------------------------------   

   U_write_fsm : entity work.GICS_IB_ENDPOINT_WRITE_FSM
   port map (
      -- Common interface ---------------------------------
      CLK          => CLK,
      RESET        => RESET,
 
      -- IB interface -------------------------------------
      IB_SOF_N     => IB_SOF_N,    
      IB_EOF_N     => IB_EOF_N,              
      IB_SRC_RDY_N => IB_SRC_RDY_N,
      IB_DST_RDY_N => IB_DST_RDY_N_aux,

      -- WR interface -------------------------------------
      WR_SOF       => WR_SOF_aux,
      WR_EOF       => WR_EOF_aux,
      WR_REQ       => WR_REQ_aux,
      WR_RDY       => WR_RDY,

      -- Control interface --------------------------------
      HEADER_LAST  => header_last,
      HEADER       => header,
      ADDR_CE      => addr_ce,
      
      -- Strict unit interface ----------------------------
      WR_EN        => WR_EN
   );

   WR_SOF <= WR_SOF_aux;
   WR_EOF <= WR_EOF_aux;
   WR_REQ <= WR_REQ_aux;

   IB_DST_RDY_N <= IB_DST_RDY_N_aux;
   
   WR_COMPLETE <= WR_EOF_aux and WR_REQ_aux and WR_RDY;
   
end ib_endpoint_write_ctrl_arch;   



