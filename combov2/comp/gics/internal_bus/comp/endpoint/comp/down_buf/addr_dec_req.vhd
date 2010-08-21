--
-- addr_dec_req.vhd : IB Endpoint Address Decoder Request Buffer
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

use work.math_pack.all;
use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 

-- ----------------------------------------------------------------------------
--     ENTITY DECLARATION -- IB Endpoint Address Decoder Request Buffer      -- 
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_ADDR_DEC_REQUEST_BUFFER is 
   generic(
      -- The number of items to be stored
      ITEMS        : integer:=  1     
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK          : in std_logic;  
      RESET        : in std_logic;  

      -- Input interface ------------------------------------------------------
      IN_REQ       : in  std_logic;
      IN_REQ_WE    : in  std_logic;      
      
      -- Output interface -----------------------------------------------------
      OUT_REQ      : out std_logic;
      OUT_DROP     : out std_logic;      
      OUT_ACK      : in  std_logic      
   );
end IB_ENDPOINT_ADDR_DEC_REQUEST_BUFFER;

-- ----------------------------------------------------------------------------
--  ARCHITECTURE DECLARATION  --  IB Endpoint Address Decoder Request Buffer --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_addr_dec_req_buf_arch of IB_ENDPOINT_ADDR_DEC_REQUEST_BUFFER is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal empty : std_logic;
   signal dout  : std_logic_vector(0 downto 0);
                                                                                                   
begin

   -- -------------------------------------------------------------------------
   --               THE NUMBER OF HEADERS TO BE STORED == 1                  --
   -- -------------------------------------------------------------------------

   HEADER_NUM_EQ_1: if (ITEMS = 1) generate

      regp : process(RESET, CLK)                                                                                                  
      begin                                                                                                                            
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then                                                                                                         
               OUT_REQ  <= '0';
               OUT_DROP <= '0';         
            elsif (IN_REQ_WE = '1') then
               OUT_REQ  <= IN_REQ;
               OUT_DROP <= not IN_REQ;
            elsif (OUT_ACK = '1') then
               OUT_REQ  <= '0';
               OUT_DROP <= '0';
            end if;
         end if;                                                                                                  
      end process;

   end generate;

   -- -------------------------------------------------------------------------
   --               THE NUMBER OF HEADERS TO BE STORED > 1                   --
   -- -------------------------------------------------------------------------

   HEADER_NUM_GT_1: if (ITEMS > 1) generate

      -- REQUEST BUFFER -------------------------------------------------------
      U_ib_endpoint_request_buffer_sh_fifo: entity work.SH_FIFO
      generic map (
         FIFO_WIDTH     => 1,
         FIFO_DEPTH     => ITEMS,
         USE_INREG      => false, 
         USE_OUTREG     => false  
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,
         -- write interface
         DIN(0)         => IN_REQ,
         WE             => IN_REQ_WE,
         FULL           => open,
         -- read interface
         DOUT           => dout,
         RE             => OUT_ACK,
         EMPTY          => empty,
         -- status
         STATUS         => open
      );

      -- OUTPUT logic ---------------------------------------------------------
      OUT_REQ  <= (    dout(0) and not empty);
      OUT_DROP <= (not dout(0) and not empty);      
      
   end generate;

end ib_endpoint_addr_dec_req_buf_arch;

                     

