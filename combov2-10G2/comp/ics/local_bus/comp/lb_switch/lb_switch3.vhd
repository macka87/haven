--
-- lb_switch3.vhd: LB switch with 3 ports
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
use work.lb_pkg.all; -- Local Bus package


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity LB_SWITCH3 is
   port(
      -- Common Interface
      LB_CLK        : in std_logic;
      LB_RESET      : in std_logic;

      -- Upstream Port
      PORT0         : inout t_local_bus16;
      -- Downstream Ports
      PORT1         : inout t_local_bus16;
      PORT2         : inout t_local_bus16
   );

end entity LB_SWITCH3;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture LB_SWITCH3_ARCH of LB_SWITCH3 is
   
   -- Port Count constant
   constant C_PORT_COUNT    : integer := 2;

   -- Generic switch signals
   signal aux_dwr           : std_logic_vector(C_PORT_COUNT*16-1 downto 0);
   signal aux_be            : std_logic_vector(C_PORT_COUNT*2-1 downto 0);
   signal aux_ads_n         : std_logic_vector(C_PORT_COUNT-1 downto 0);
   signal aux_rd_n          : std_logic_vector(C_PORT_COUNT-1 downto 0);
   signal aux_wr_n          : std_logic_vector(C_PORT_COUNT-1 downto 0);
   signal aux_drd           : std_logic_vector(C_PORT_COUNT*16-1 downto 0);
   signal aux_rdy_n         : std_logic_vector(C_PORT_COUNT-1 downto 0);
   signal aux_err_n         : std_logic_vector(C_PORT_COUNT-1 downto 0);
   signal aux_abort_n       : std_logic_vector(C_PORT_COUNT-1 downto 0);

   signal reset_pipe : std_logic;
   attribute equivalent_register_removal : string;
   attribute equivalent_register_removal of reset_pipe : signal is "no";

begin

-- Port 1 Map
PORT1.DWR                    <= aux_dwr(1*16-1 downto 0*16);   
PORT1.BE                     <= aux_be(1*2-1 downto 0*2);   
PORT1.ADS_N                  <= aux_ads_n(0);   
PORT1.RD_N                   <= aux_rd_n(0); 
PORT1.WR_N                   <= aux_wr_n(0);   
aux_drd(1*16-1 downto 0*16)  <= PORT1.DRD;        
aux_rdy_n(0)                 <= PORT1.RDY_N;
aux_err_n(0)                 <= PORT1.ERR_N;
PORT1.ABORT_N                <= aux_abort_n(0);
-- Port 2 Map
PORT2.DWR                    <= aux_dwr(2*16-1 downto 1*16);   
PORT2.BE                     <= aux_be(2*2-1 downto 1*2);
PORT2.ADS_N                  <= aux_ads_n(1);   
PORT2.RD_N                   <= aux_rd_n(1); 
PORT2.WR_N                   <= aux_wr_n(1);   
aux_drd(2*16-1 downto 1*16)  <= PORT2.DRD;        
aux_rdy_n(1)                 <= PORT2.RDY_N;
aux_err_n(1)                 <= PORT2.ERR_N;
PORT2.ABORT_N                <= aux_abort_n(1);

-- ----------------------------------------------------------------------------
RESET_PIPE_P : process(LB_RESET, LB_CLK)
   begin
      if LB_CLK'event and LB_CLK = '1' then
         reset_pipe  <= LB_RESET;
      end if;
end process;

-- ----------------------------------------------------------------------------
LB_SWITCH_GENERIC_U : entity work.LB_SWITCH_GENERIC
   generic map (
       PORT_COUNT => C_PORT_COUNT
   )   
   port map (
      -- Common Interface
      LB_CLK        => LB_CLK,
      LB_RESET      => reset_pipe,
      
      -- Port 0 (Upstream Link)
      PORT0         => PORT0,

      -- Other Ports (Downstream Links)
      DWR           => aux_dwr,
      BE            => aux_be,
      ADS_N         => aux_ads_n,
      RD_N          => aux_rd_n,
      WR_N          => aux_wr_n,
      DRD           => aux_drd,
      RDY_N         => aux_rdy_n,
      ERR_N         => aux_err_n,
      ABORT_N       => aux_abort_n
   );


end architecture LB_SWITCH3_ARCH;
