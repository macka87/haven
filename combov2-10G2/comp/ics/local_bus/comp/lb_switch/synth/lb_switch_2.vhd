-- lb_switch_2.vhd: Synthesis wrapper of Local Bus Switch with two downstreams
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity LB_SWITCH_2 is
   port(
      -- Common Interface
      LB_CLK        : in std_logic;
      LB_RESET      : in std_logic;
      
      -- Upstream Link
      PORT0_DWR           : in  std_logic_vector(15 downto 0);
      PORT0_BE            : in  std_logic_vector(1 downto 0);
      PORT0_ADS_N         : in  std_logic;
      PORT0_RD_N          : in  std_logic;
      PORT0_WR_N          : in  std_logic;
      PORT0_DRD           : out std_logic_vector(15 downto 0);
      PORT0_RDY_N         : out std_logic;
      PORT0_ERR_N         : out std_logic;
      PORT0_ABORT_N       : in  std_logic;

      -- Downstream Links
      DWR           : out std_logic_vector(2*16-1 downto 0);
      BE            : out std_logic_vector(2*2-1 downto 0);
      ADS_N         : out std_logic_vector(2-1 downto 0);
      RD_N          : out std_logic_vector(2-1 downto 0);
      WR_N          : out std_logic_vector(2-1 downto 0);
      DRD           : in  std_logic_vector(2*16-1 downto 0);
      RDY_N         : in  std_logic_vector(2-1 downto 0);
      ERR_N         : in  std_logic_vector(2-1 downto 0);
      ABORT_N       : out std_logic_vector(2-1 downto 0)
   );
end entity LB_SWITCH_2;

architecture full of lb_switch_2 is

begin

   switch_i : entity work.LB_SWITCH_NOREC
   generic map(
      PORT_COUNT => 2
   )
   port map(
      -- Common Interface
      LB_CLK        => LB_CLK,
      LB_RESET      => LB_RESET,
                       
      -- Upstream Li
      PORT0_DWR     => PORT0_DWR,
      PORT0_BE      => PORT0_BE,
      PORT0_ADS_N   => PORT0_ADS_N,
      PORT0_RD_N    => PORT0_RD_N,
      PORT0_WR_N    => PORT0_WR_N,
      PORT0_DRD     => PORT0_DRD,
      PORT0_RDY_N   => PORT0_RDY_N,
      PORT0_ERR_N   => PORT0_ERR_N,
      PORT0_ABORT_N => PORT0_ABORT_N,
                                    
      -- Downstream
      DWR           => DWR,
      BE            => BE,
      ADS_N         => ADS_N,
      RD_N          => RD_N,
      WR_N          => WR_N,
      DRD           => DRD,
      RDY_N         => RDY_N,
      ERR_N         => ERR_N,
      ABORT_N       => ABORT_N
   );

end architecture;
