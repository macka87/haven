--
-- lb_switch_generic.vhd: Local Bus Switch with Generic interface
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.lb_pkg.all; -- Local Bus package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity LB_SWITCH_GENERIC is
   generic(
       PORT_COUNT : integer -- Count of downstream ports >=1
   );
   
   port(
      -- Common Interface
      LB_CLK        : in std_logic;
      LB_RESET      : in std_logic;
      
      -- Upstream Link
      PORT0         : inout t_local_bus16;   

      -- Downstream Links
      DWR           : out std_logic_vector(PORT_COUNT*16-1 downto 0);
      BE            : out std_logic_vector(PORT_COUNT*2-1 downto 0);
      ADS_N         : out std_logic_vector(PORT_COUNT-1 downto 0);
      RD_N          : out std_logic_vector(PORT_COUNT-1 downto 0);
      WR_N          : out std_logic_vector(PORT_COUNT-1 downto 0);
      DRD           : in  std_logic_vector(PORT_COUNT*16-1 downto 0);
      RDY_N         : in  std_logic_vector(PORT_COUNT-1 downto 0);
      ERR_N         : in  std_logic_vector(PORT_COUNT-1 downto 0);
      ABORT_N       : out std_logic_vector(PORT_COUNT-1 downto 0)
   );
end entity LB_SWITCH_GENERIC;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture LB_SWITCH_GENERIC_ARCH of LB_SWITCH_GENERIC is

signal dwr_pipe      : std_logic_vector(PORT_COUNT*16-1 downto 0);
signal be_pipe       : std_logic_vector(PORT_COUNT*2-1 downto 0);
signal ads_n_pipe    : std_logic_vector(PORT_COUNT-1 downto 0);
signal rd_n_pipe     : std_logic_vector(PORT_COUNT-1 downto 0);
signal wr_n_pipe     : std_logic_vector(PORT_COUNT-1 downto 0);
signal drd_pipe      : std_logic_vector(PORT_COUNT*16-1 downto 0);
signal rdy_n_pipe    : std_logic_vector(PORT_COUNT-1 downto 0);
signal err_n_pipe    : std_logic_vector(PORT_COUNT-1 downto 0);
signal abort_n_pipe  : std_logic_vector(PORT_COUNT-1 downto 0);
signal err_in        : std_logic;
signal switch_err    : std_logic;

-- Port registers won't be removed
attribute equivalent_register_removal : string;
attribute equivalent_register_removal of ABORT_N : signal is "no";
attribute equivalent_register_removal of DWR     : signal is "no"; 
attribute equivalent_register_removal of RD_N    : signal is "no"; 
attribute equivalent_register_removal of BE      : signal is "no"; 
attribute equivalent_register_removal of ADS_N   : signal is "no";
attribute equivalent_register_removal of WR_N    : signal is "no";


begin

-- ----------------------------------------------------------------------------
pipe_map_gen : for i in 0 to PORT_COUNT - 1 generate
  dwr_pipe((i+1)*16-1 downto i*16) <= PORT0.DWR;
  be_pipe((i+1)*2-1 downto i*2)    <=  PORT0.BE;
  ads_n_pipe(i)                    <= PORT0.ADS_N;
  rd_n_pipe(i)                     <= PORT0.RD_N;
  wr_n_pipe(i)                     <= PORT0.WR_N;
  abort_n_pipe(i)                  <= PORT0.ABORT_N;
end generate;


-- ----------------------------------------------------------------------------
drd_gen: process(drd_pipe, rdy_n_pipe)
  variable aux_drd : std_logic_vector(15 downto 0);
begin
  aux_drd := "0000000000000000";
  for i in 0 to PORT_COUNT - 1 loop
     if rdy_n_pipe(i) = '0' then
        aux_drd := drd_pipe((i+1)*16-1 downto i*16);
     end if;
  end loop;
  PORT0.DRD <= aux_drd;
end process drd_gen;

-- ----------------------------------------------------------------------------
rdy_n_gen: process(rdy_n_pipe)
  variable aux_rdy : std_logic;
begin
  aux_rdy := '0';
  for i in 0 to PORT_COUNT - 1 loop
     aux_rdy := aux_rdy or not rdy_n_pipe(i);
  end loop;
  PORT0.RDY_N <= not aux_rdy;
end process rdy_n_gen;

-- ----------------------------------------------------------------------------
err_in_gen: process(err_n_pipe)
  variable aux_err : std_logic;
begin
  aux_err := '0';
  for i in 0 to PORT_COUNT - 1 loop
    aux_err := aux_err or not err_n_pipe(i);
  end loop;
  err_in <= aux_err;
end process err_in_gen;

-- ----------------------------------------------------------------------------
switch_err_gen: process(rdy_n_pipe)
  variable aux_err : std_logic;
  variable aux_rdy : std_logic;
begin
  aux_rdy := '0';
  aux_err := '0';
  for i in 0 to PORT_COUNT - 1 loop
     aux_err := aux_err or (aux_rdy and not rdy_n_pipe(i));
     aux_rdy := aux_rdy or not rdy_n_pipe(i);
  end loop;
  switch_err <= aux_err;
end process switch_err_gen;


PORT0.ERR_N <= not (err_in or switch_err);



-------------------------------------------------------------------------------
--                          OUTPUT REGISTERS
-------------------------------------------------------------------------------
-- Output registers for Internal Bus Output Interface
output_registersp: process(LB_RESET, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (LB_RESET = '1') then
         DWR        <= (others => '0');
         BE         <= (others => '0');
         ADS_N      <= (others => '1');
         RD_N       <= (others => '1');
         WR_N       <= (others => '1');
         drd_pipe   <= (others => '0');
         rdy_n_pipe <= (others => '1');
         err_n_pipe <= (others => '1');
         ABORT_N    <= (others => '1');
      else
         DWR        <= dwr_pipe;
         BE         <= be_pipe;
         ADS_N      <= ads_n_pipe;
         RD_N       <= rd_n_pipe;
         WR_N       <= wr_n_pipe;
         drd_pipe   <= DRD;
         rdy_n_pipe <= RDY_N;
         err_n_pipe <= ERR_N;
         ABORT_N    <= abort_n_pipe;
      end if;
   end if;
end process;


end architecture LB_SWITCH_GENERIC_ARCH;
