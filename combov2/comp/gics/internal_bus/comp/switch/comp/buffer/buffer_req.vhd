--
-- buffer_req.vhd : IB Switch Request Buffer
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
use work.ib_switch_pkg.all;

-- ----------------------------------------------------------------------------
--               ENTITY DECLARATION -- IB Switch Request Buffer              -- 
-- ----------------------------------------------------------------------------

entity IB_SWITCH_BUFFER_REQUEST is 
   generic(
      -- Data Width (1-128)
      DATA_WIDTH   : integer:= 64;   
      -- The number of headers to be stored
      HEADER_NUM   : integer:=  1     
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK          : in std_logic;  
      RESET        : in std_logic;  

      -- Input interface ------------------------------------------------------
      IN_REQ_VEC   : in  std_logic_vector(2 downto 0);
      IN_REQ_WE    : in  std_logic;      
      
      -- Output interface -----------------------------------------------------
      OUT_REQ_VEC  : out std_logic_vector(2 downto 0);
      OUT_ACK_VEC  : in  std_logic_vector(2 downto 0)      
   );
end IB_SWITCH_BUFFER_REQUEST;

-- ----------------------------------------------------------------------------
--            ARCHITECTURE DECLARATION  --  IB Switch Request Buffer         --
-- ----------------------------------------------------------------------------

architecture ib_switch_request_buffer_arch of IB_SWITCH_BUFFER_REQUEST is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal dout  : std_logic_vector(2 downto 0);
   signal re    : std_logic;
   signal empty : std_logic;
   signal ack   : std_logic;

begin

   -- -------------------------------------------------------------------------
   --               THE NUMBER OF HEADERS TO BE STORED == 1                  --
   -- -------------------------------------------------------------------------

   HEADER_NUM_EQ_1: if (ib_switch_buffer_request_depth(HEADER_NUM, DATA_WIDTH) = 1) generate

      regp : process(CLK)                                                                                                  
      begin                                                                                                                            
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then                                                                                                         
               OUT_REQ_VEC <= "000";                                                                                       
            elsif (IN_REQ_WE = '1') then
               OUT_REQ_VEC <= IN_REQ_VEC; 
            elsif (ack = '1') then
               OUT_REQ_VEC <= "000";
            end if;
         end if;                                                                                                  
      end process;

      ack <= OUT_ACK_VEC(2) or OUT_ACK_VEC(1) or OUT_ACK_VEC(0);

   end generate;

   -- -------------------------------------------------------------------------
   --               THE NUMBER OF HEADERS TO BE STORED > 1                   --
   -- -------------------------------------------------------------------------

   HEADER_NUM_GT_1: if (ib_switch_buffer_request_depth(HEADER_NUM, DATA_WIDTH) > 1) generate

      -- REQUEST BUFFER -------------------------------------------------------
      U_ib_switch_request_buffer_sh_fifo: entity work.SH_FIFO
      generic map (
         FIFO_WIDTH     => 3,
         FIFO_DEPTH     => ib_switch_buffer_request_depth(HEADER_NUM, DATA_WIDTH),
         USE_INREG      => false, 
         USE_OUTREG     => false  
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,
         -- write interface
         DIN            => IN_REQ_VEC,
         WE             => IN_REQ_WE,
         FULL           => open,
         -- read interface
         DOUT           => dout,
         RE             => re,
         EMPTY          => empty,
         -- status
         STATUS         => open
      );

      -- OUTPUT logic ---------------------------------------------------------
      OUT_REQ_VEC <= (dout(2) and not empty)&(dout(1) and not empty)&(dout(0) and not empty);
      
      re <= OUT_ACK_VEC(2) or OUT_ACK_VEC(1) or OUT_ACK_VEC(0);

   end generate;

   -- -------------------------------------------------------------------------
   --                            WRONG HEADER_NUM                            --
   -- -------------------------------------------------------------------------    

   assert (HEADER_NUM > 0)
   report "Wrong count of 'headers to be stored' specified (IB_SWITCH_BUFFER_REQUEST)."
   severity ERROR;       
   
end ib_switch_request_buffer_arch;

                     

