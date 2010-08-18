-- swr_cb_mgmt_fl16.vhd: Control Bus management unit with FL16 interface
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek    <kosek@liberouter.org>
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


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity SWR_CB_MGMT_FL16 is
   generic (
      COUNT          : integer   -- number of connected SW_RXBUFs
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;
      
      -- Control Bus interface
      -- User Component Upstream Interface
      UPS_FL         : inout t_fl16;

      -- User Component Downstream Interface
      DNS_FL         : inout t_fl16;

      -- SW_RXBUF Control Bus interface
      CTRL_OFFSET    : in  std_logic_vector(COUNT*20-1 downto 0);
      CTRL_LENGTH    : in  std_logic_vector(COUNT*12-1 downto 0);
      CTRL_IFC       : in  std_logic_vector(COUNT*4-1 downto 0);
      INFO_READY     : in  std_logic_vector(COUNT-1 downto 0);
      ACK            : out std_logic_vector(COUNT-1 downto 0);
      FREE_PACKET    : out std_logic_vector(COUNT-1 downto 0)
   );
end entity SWR_CB_MGMT_FL16;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of SWR_CB_MGMT_FL16 is
   -- auxiliary signals
   signal ups_sof          : std_logic;
   signal ups_eof          : std_logic;
   signal ups_src_rdy      : std_logic;
   signal ups_dst_rdy      : std_logic;
   signal dns_sof          : std_logic;
   signal dns_eof          : std_logic;
   signal dns_src_rdy      : std_logic;
   signal dns_dst_rdy      : std_logic;
begin
   -- configure upstream interface
   UPS_FL.SRC_RDY_N  <= not ups_src_rdy;
   ups_dst_rdy       <= not UPS_FL.DST_RDY_N;
   UPS_FL.DREM       <= (others => '1');
   UPS_FL.SOP_N      <= not ups_sof;
   UPS_FL.EOP_N      <= not ups_eof;
   UPS_FL.SOF_N      <= not ups_sof;
   UPS_FL.EOF_N      <= not ups_eof;

   -- configure downstream interface
   dns_sof           <= not DNS_FL.SOF_N;
   dns_eof           <= not DNS_FL.EOF_N;
   dns_src_rdy       <= not DNS_FL.SRC_RDY_N;
   DNS_FL.DST_RDY_N  <= not dns_dst_rdy;

   -- Control Bus Management Unit mapping
   SWR_CB_MGMT_I : entity work.SWR_CB_MGMT
      generic map(
         COUNT          => COUNT
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- Control Bus interface
         -- User Component Upstream Interface
         UPS_DATA       => UPS_FL.DATA,
         UPS_SOP        => ups_sof,
         UPS_EOP        => ups_eof,
         UPS_SRC_RDY    => ups_src_rdy,
         UPS_DST_RDY    => ups_dst_rdy,
         -- User Component Downstream Interface
         DNS_DATA       => DNS_FL.DATA,
         DNS_SOP        => dns_sof,
         DNS_EOP        => dns_eof,
         DNS_SRC_RDY    => dns_src_rdy,
         DNS_DST_RDY    => dns_dst_rdy,
         -- SW_RXBUF Control Bus interface
         CTRL_OFFSET    => CTRL_OFFSET,
         CTRL_LENGTH    => CTRL_LENGTH,
         CTRL_IFC       => CTRL_IFC,
         INFO_READY     => INFO_READY,
         ACK            => ACK,
         FREE_PACKET    => FREE_PACKET
      );

end architecture full;
