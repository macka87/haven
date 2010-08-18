-- lb_switch_synth.vhd: Synthesis wrapper of Local Bus Switch
-- Copyright (C) 2009 CESNET
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
entity LB_SWITCH_SYNTH is
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
      DWR           : out std_logic_vector(3*16-1 downto 0);
      BE            : out std_logic_vector(3*2-1 downto 0);
      ADS_N         : out std_logic_vector(3-1 downto 0);
      RD_N          : out std_logic_vector(3-1 downto 0);
      WR_N          : out std_logic_vector(3-1 downto 0);
      DRD           : in  std_logic_vector(3*16-1 downto 0);
      RDY_N         : in  std_logic_vector(3-1 downto 0);
      ERR_N         : in  std_logic_vector(3-1 downto 0);
      ABORT_N       : out std_logic_vector(3-1 downto 0)
   );
end entity LB_SWITCH_SYNTH;

architecture full of lb_switch_synth is

   signal reg_port0_dwr     : std_logic_vector(15 downto 0);
   signal reg_port0_be      : std_logic_vector(1 downto 0);
   signal reg_port0_ads_n   : std_logic;
   signal reg_port0_rd_n    : std_logic;
   signal reg_port0_wr_n    : std_logic;
   signal sig_port0_drd     : std_logic_vector(15 downto 0);
   signal sig_port0_rdy_n   : std_logic;
   signal sig_port0_err_n   : std_logic;
   signal reg_port0_abort_n : std_logic;

   signal sig_dwr           : std_logic_vector(3*16-1 downto 0);
   signal sig_be            : std_logic_vector(3*2-1 downto 0);
   signal sig_ads_n         : std_logic_vector(3-1 downto 0);
   signal sig_rd_n          : std_logic_vector(3-1 downto 0);
   signal sig_wr_n          : std_logic_vector(3-1 downto 0);
   signal reg_drd           : std_logic_vector(3*16-1 downto 0);
   signal reg_rdy_n         : std_logic_vector(3-1 downto 0);
   signal reg_err_n         : std_logic_vector(3-1 downto 0);
   signal sig_abort_n       : std_logic_vector(3-1 downto 0);

begin

   switch_i : entity work.LB_SWITCH_NOREC
   generic map(
      PORT_COUNT => 3
   )
   port map(
      -- Common Interface
      LB_CLK        => LB_CLK,
      LB_RESET      => LB_RESET,
                       
      -- Upstream Li
      PORT0_DWR     => reg_port0_dwr,
      PORT0_BE      => reg_port0_be,
      PORT0_ADS_N   => reg_port0_ads_n,
      PORT0_RD_N    => reg_port0_rd_n,
      PORT0_WR_N    => reg_port0_wr_n,
      PORT0_DRD     => sig_port0_drd,
      PORT0_RDY_N   => sig_port0_rdy_n,
      PORT0_ERR_N   => sig_port0_err_n,
      PORT0_ABORT_N => reg_port0_abort_n,
                                    
      -- Downstream
      DWR           => sig_dwr,
      BE            => sig_be,
      ADS_N         => sig_ads_n,
      RD_N          => sig_rd_n,
      WR_N          => sig_wr_n,
      DRD           => reg_drd,
      RDY_N         => reg_rdy_n,
      ERR_N         => reg_err_n,
      ABORT_N       => sig_abort_n
   );

   process(LB_CLK)
   begin
      if LB_CLK'event and LB_CLK = '1' then
         reg_port0_dwr     <= PORT0_DWR;
         reg_port0_be      <= PORT0_BE;
         reg_port0_ads_n   <= PORT0_ADS_N;
         reg_port0_rd_n    <= PORT0_RD_N;
         reg_port0_wr_n    <= PORT0_WR_N;
         reg_port0_abort_n <= PORT0_ABORT_N;
         reg_drd           <= DRD;
         reg_rdy_n         <= RDY_N;
         reg_err_n         <= ERR_N;

         PORT0_DRD   <= sig_port0_drd;
         PORT0_RDY_N <= sig_port0_rdy_n;
         PORT0_ERR_N <= sig_port0_err_n;
         DWR         <= sig_dwr;
         BE          <= sig_be;
         ADS_N       <= sig_ads_n;
         RD_N        <= sig_rd_n;
         WR_N        <= sig_wr_n;
         ABORT_N     <= sig_abort_n;
      end if;
   end process;

end architecture;
