-- spliter.vhd: Split 96-bit input interface to n 96-bit output interfaces
-- Copyright (C) 2009 CESNET
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--  Entity declaration: SPLITER
-- ----------------------------------------------------------------------------
entity SPLITER is
   generic(
      -- number of output interfaces
      INTERFACES     : integer := 4
   );
   port(
      -- common signals
      -- global FGPA clock
      CLK               : in  std_logic;

      -- global synchronous reset
      RESET             : in  std_logic;
      
      -- RX 96-bit interface
      RX_DATA          : in  std_logic_vector(95 downto 0);
      RX_SOF           : in  std_logic;
      RX_EOF           : in  std_logic;
      RX_VLD           : in  std_logic;
      RX_RDY           : out std_logic;
   
      -- TX 96-bit interfaces
      TX_DATA          : out std_logic_vector((INTERFACES * 96) - 1 downto 0);
      TX_SOF           : out std_logic_vector(INTERFACES - 1 downto 0);
      TX_EOF           : out std_logic_vector(INTERFACES - 1 downto 0);
      TX_VLD           : out std_logic_vector(INTERFACES - 1 downto 0);
      TX_RDY           : in  std_logic_vector(INTERFACES - 1 downto 0)
   );
end entity SPLITER;

-- ----------------------------------------------------------------------------
--  Architecture: SPLITER
-- ----------------------------------------------------------------------------
architecture full of SPLITER is
   signal cnt_interfaces      : std_logic_vector(log2(INTERFACES) - 1 downto 0);
   signal cnt_interfaces_ce   : std_logic;
   signal in_rdy              : std_logic_vector(0 downto 0);
   signal out_rdy             : std_logic_vector(0 downto 0);
begin

   interface_counter: process (CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            cnt_interfaces <= (others => '0');
         else
            if (cnt_interfaces_ce = '1') then
               if (cnt_interfaces = INTERFACES - 1) then
                  cnt_interfaces <= (others => '0');
               else
                  cnt_interfaces <= cnt_interfaces + '1';
               end if;
            end if;
         end if;
      end if;
   end process interface_counter;
   
   VLD_DEMUX_U: entity work.GEN_DEMUX
   generic map(
      DATA_WIDTH  => 1,
      DEMUX_WIDTH => INTERFACES,
      DEF_VALUE   => '0'
   )
   port map(
      DATA_IN     => in_rdy,
      SEL         => cnt_interfaces,
      DATA_OUT    => TX_VLD
   );
   
   in_rdy(0) <= RX_VLD;
   
   RDY_MUX_U: entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 1,
      MUX_WIDTH   => INTERFACES
   )
   port map(
      DATA_IN     => TX_RDY,
      SEL         => cnt_interfaces,
      DATA_OUT    => out_rdy
   );
   
   RX_RDY <= out_rdy(0);
   
   gen_conections: for i in 0 to INTERFACES - 1 generate
      TX_SOF(i) <= RX_SOF;
      TX_EOF(i) <= RX_EOF;
      TX_DATA((i + 1) * 96 - 1 downto i * 96) <= RX_DATA;
   end generate gen_conections;
   
   cnt_interfaces_ce <= RX_EOF and RX_VLD and out_rdy(0);
   
end architecture full;