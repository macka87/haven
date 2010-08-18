 --
-- len_decoder.vhd : PCI-e Length decoder
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kobierský <kobierskyk@liberouter.org>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- TODO: Addr assertion to toplevel (check for out of 4kb aligment)

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity PCIE_TX_ADDR_DECODER is
  port (
    -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N           : in  std_logic; 
      TRN_CLK               : in  std_logic; 
    -- Data Input Interface -------------------------------------------------
      ADDR_IN               : in std_logic_vector(11 downto 0);
      ADDR_IN_WE            : in std_logic;
      TYPE_REG              : in std_logic_vector(1 downto 0);
      MAX_READ_SIZE         : in std_logic_vector(9 downto 0);
      MAX_PAYLOAD_SIZE      : in std_logic_vector(9 downto 0);
    -- Output FSM Interface -------------------------------------------------
      NEXT_PART             : in  std_logic;
    -- Output Interface -----------------------------------------------------
      ADDR_OUT              : out std_logic_vector(11 downto 0)
   );
end PCIE_TX_ADDR_DECODER;



-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of PCIE_TX_ADDR_DECODER is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal addr_in_reg         : std_logic_vector(9 downto 0);
   signal addr_in_mux         : std_logic_vector(9 downto 0);
   signal empty               : std_logic_vector(1 downto 0);

begin

   empty <= ADDR_IN(1 downto 0);

   -- memory for address ------------------------------------------------------
   ADDR_IN_P : process (TRN_CLK, TRN_RESET_N, ADDR_IN, ADDR_IN_WE, NEXT_PART, addr_in_mux) 
      begin
         if (TRN_CLK = '1' and TRN_CLK'event) then
            if (TRN_RESET_N = '0') then 
               -- addr_in_reg  <= (others => '0');
            elsif (ADDR_IN_WE = '1') then       -- INIT
               addr_in_reg <=  ADDR_IN(11 downto 2);
            elsif (NEXT_PART = '1') then     -- INCREMENT
            	addr_in_reg  <= addr_in_reg + addr_in_mux;
            end if;
         end if;
      end process;

   -- multiplexer for increment address ---------------------------------------
   ADDR_MUX : process(TYPE_REG, MAX_READ_SIZE, MAX_PAYLOAD_SIZE)
	   begin
		   case (TYPE_REG(1)) is
		   	when '0' => addr_in_mux <= MAX_READ_SIZE;    -- READ, first_addr
            when '1' => addr_in_mux <= MAX_PAYLOAD_SIZE; -- WRITE, CPL, first_addr
		   	when others => null;
		   end case;
	   end process;

   -- select valid address to output ------------------------------------------
   ADDR_OUT <= addr_in_reg & "00";

end architecture FULL;

