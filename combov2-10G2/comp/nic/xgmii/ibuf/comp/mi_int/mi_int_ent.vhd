-- mi_int_ent.vhd: Entity of component providing MI32 interface for IBUF
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
--            Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.ibuf_pkg.all;
use work.lb_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity MI_INT is

   generic(
      -- Number of MAC addresses that can be placed into CAM
      MAC_COUNT     	: integer
   );

   port(
      ---------- IBUF signals ----------
      IBUF_CLK     	: in std_logic; 		-- Clock sigal
      RESET        	: in std_logic;  		-- Asynchronous reset, active in '1'

      ---------- MI32 interface ----------
      MI_CLK         : in 	std_logic;                   	-- MI32 bus clock
      MI_DWR      	: in  std_logic_vector(31 downto 0); -- Input Data
      MI_ADDR     	: in  std_logic_vector(31 downto 0); -- Address
      MI_RD       	: in  std_logic;                     -- Read Request
      MI_WR       	: in  std_logic;                     -- Write Request
      MI_BE       	: in  std_logic_vector(3  downto 0); -- Byte Enable
      MI_DRD      	: out std_logic_vector(31 downto 0); -- Output Data
      MI_ARDY     	: out std_logic;                     -- Address Ready
      MI_DRDY     	: out std_logic;                     -- Data Ready

	   ---------- Check interface ----------
      MI2CHECK       : out t_mi2check; 	-- Data provided to Check component

      ---------- Buf interface ----------
      MI2BUF         : out t_mi2buf; 		-- Data provided to Buf component
      BUF2MI         : in  t_buf2mi;    	-- Data provided by Buf component

      DEBUG_INFO     : in std_logic_vector(0 downto 0);

      ---------- CAM interface ----------
      -- MAC address to be searched
      CAM_DI            : in  std_logic_vector(63 downto 0);
      -- MAC address search enable
      CAM_MATCH_EN      : in  std_logic;
      -- CAM match reset
      CAM_MATCH_RST     : in  std_logic;
      -- Addresses found in CAM
      CAM_MATCH_BUS     : out std_logic_vector(MAC_COUNT-1 downto 0);
      -- CAM_MATCH_BUS is valid, active in '1'
      CAM_MATCH_BUS_VLD : out std_logic

   ); 

end entity MI_INT;
