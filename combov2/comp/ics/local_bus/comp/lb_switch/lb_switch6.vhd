--
-- lb_switch6.vhd: LB switch with 5 ports
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek   <kosek@liberouter.org>
--            Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the OpenIPCore Hardware General Public
-- License as published by the OpenIPCore Organization; either version
-- 0.20-15092000 of the License, or (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful, but
-- WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- OpenIPCore Hardware General Public License for more details.
--
-- You should have received a copy of the OpenIPCore Hardware Public
-- License along with this program; if not, download it from
-- OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
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
entity LB_SWITCH6 is
   port(
      -- Common Interface
      LB_CLK        : in std_logic;
      LB_RESET      : in std_logic;

      -- Upstream Port
      PORT0         : inout t_local_bus16;
      -- Downstream Ports
      PORT1         : inout t_local_bus16;
      PORT2         : inout t_local_bus16;
      PORT3         : inout t_local_bus16;
      PORT4         : inout t_local_bus16;
      PORT5         : inout t_local_bus16
   );

end entity LB_SWITCH6;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture LB_SWITCH6_ARCH of LB_SWITCH6 is
   
   -- Port Count constant
   constant C_PORT_COUNT    : integer := 5;

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
-- Port 3 Map
PORT3.DWR                    <= aux_dwr(3*16-1 downto 2*16);   
PORT3.BE                     <= aux_be(3*2-1 downto 2*2);
PORT3.ADS_N                  <= aux_ads_n(2);   
PORT3.RD_N                   <= aux_rd_n(2); 
PORT3.WR_N                   <= aux_wr_n(2);   
aux_drd(3*16-1 downto 2*16)  <= PORT3.DRD;        
aux_rdy_n(2)                 <= PORT3.RDY_N;
aux_err_n(2)                 <= PORT3.ERR_N;
PORT3.ABORT_N                <= aux_abort_n(2);
-- Port 4 Map
PORT4.DWR                    <= aux_dwr(4*16-1 downto 3*16);   
PORT4.BE                     <= aux_be(4*2-1 downto 3*2);
PORT4.ADS_N                  <= aux_ads_n(3);   
PORT4.RD_N                   <= aux_rd_n(3); 
PORT4.WR_N                   <= aux_wr_n(3);   
aux_drd(4*16-1 downto 3*16)  <= PORT4.DRD;        
aux_rdy_n(3)                 <= PORT4.RDY_N;
aux_err_n(3)                 <= PORT4.ERR_N;
PORT4.ABORT_N                <= aux_abort_n(3);
-- Port 5 Map
PORT5.DWR                    <= aux_dwr(5*16-1 downto 4*16);   
PORT5.BE                     <= aux_be(5*2-1 downto 4*2);
PORT5.ADS_N                  <= aux_ads_n(4);   
PORT5.RD_N                   <= aux_rd_n(4); 
PORT5.WR_N                   <= aux_wr_n(4);   
aux_drd(5*16-1 downto 4*16)  <= PORT5.DRD;        
aux_rdy_n(4)                 <= PORT5.RDY_N;
aux_err_n(4)                 <= PORT5.ERR_N;
PORT5.ABORT_N                <= aux_abort_n(4);

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


end architecture LB_SWITCH6_ARCH;
