-- header_rearranger_full.vhd: Full architecture of HEADER REARRANGER unit.
-- Copyright (C) 2008 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
use IEEE.numeric_std.all;
use WORK.math_pack.all;

-- ----------------------------------------------------------------------------
--  Entity declaration: FL SAMPLER
-- ----------------------------------------------------------------------------
entity FL_SAMPLER is
    generic(
       DATA_WIDTH  :   integer:=128;
       MAX_RATE    :   integer:=16 -- Maximum Rate 1:N
   );
   port(
      -- common signals
      -- global FGPA clock
      CLK            : in  std_logic;

      -- global synchronous reset
      RESET          : in  std_logic;
	  
	  -- Sampling RATE 1:N
	  RATE           : in std_logic_vector(log2(MAX_RATE)  - 1 downto 0);
	  
      -- RX Framelink interface
      RX_DATA        : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;

      -- TX FrameLink interface
      TX_DATA       : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      TX_REM        : out std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      TX_SOF_N      : out std_logic;
      TX_EOF_N      : out std_logic;
      TX_SOP_N      : out std_logic;
      TX_EOP_N      : out std_logic;
      TX_SRC_RDY_N  : out std_logic;
      TX_DST_RDY_N  : in  std_logic
   );
end entity FL_SAMPLER;

-- ----------------------------------------------------------------------------
--  Architecture: FL SAMPLER
-- ----------------------------------------------------------------------------
architecture full of FL_SAMPLER is


signal cnt_packet          : std_logic_vector(3 downto 0);
signal mx_dst_rdy_n        : std_logic;

begin

-------------------------------------------------------------------------------
-- Passed packet counter
cnt_packetp: process(RESET, CLK)
begin
  if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         cnt_packet <= (others => '0');
      else
          if (cnt_packet = RATE) and (RX_EOF_N = '0') and (RX_SRC_RDY_N = '0') and (mx_dst_rdy_n = '0') then
             cnt_packet <= (others => '0');
          else
		     if (RX_EOF_N = '0') and (RX_SRC_RDY_N = '0') and (mx_dst_rdy_n = '0') then
               cnt_packet <= cnt_packet + 1 ;
			 end if;  
          end if;
       end if;
    end if;
end process;

-------------------------------------------------------------------------------
-- TX_DST_RDY_N multiplexer
mx_dst_rdy_np: process(cnt_packet,  TX_DST_RDY_N)
begin
   case cnt_packet is
     when conv_std_logic_vector(0,LOG2(MAX_RATE)) => mx_dst_rdy_n <= TX_DST_RDY_N;
     when others => mx_dst_rdy_n <= '0';
    end case;
end process;
 
RX_DST_RDY_N <= mx_dst_rdy_n ;

-------------------------------------------------------------------------------
-- TX_SRC_RDY_N multiplexer
mx_src_rdy_np: process(cnt_packet,  RX_SRC_RDY_N)
begin
   case cnt_packet is
     when conv_std_logic_vector(0,LOG2(MAX_RATE)) => TX_SRC_RDY_N <= RX_SRC_RDY_N;
     when others => TX_SRC_RDY_N <= '1';
    end case;
end process;

-------------------------------------------------------------------------------
-- Maping other ports 
TX_SOF_N <= RX_SOF_N;
TX_SOP_N <= RX_SOP_N;
TX_EOP_N <= RX_EOP_N;
TX_EOF_N <= RX_EOF_N;
TX_DATA  <= RX_DATA;
TX_REM   <= RX_REM;


end architecture full;
