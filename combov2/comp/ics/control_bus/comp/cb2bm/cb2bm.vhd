--
-- cb2bm.vhd: CB2BM component entity interface
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


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
use work.fl_pkg.all;
use work.ib_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity CB2BM is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;
      
      -- Control Bus Endpoint interface
      -- User Component Upstream Interface
      UPS_FL         : inout t_fl16;

      -- User Component Downstream Interface
      DNS_FL         : inout t_fl16;
      
      -- Bus Master Controller interface
      BM             : inout t_ibbm_64
   );
end entity CB2BM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of CB2BM is
   -- auxiliary signals
   signal ups_sof          : std_logic;
   signal ups_eof          : std_logic;
   signal ups_src_rdy      : std_logic;
   signal ups_dst_rdy      : std_logic;
   signal dns_sof          : std_logic;
   signal dns_eof          : std_logic;
   signal dns_src_rdy      : std_logic;
   signal dns_dst_rdy      : std_logic;
   signal sig_empty        : std_logic_vector(1 downto 0);
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
   sig_empty         <= DNS_FL.SOP_N & DNS_FL.EOP_N;

   -- CB2BM mapping
   CB2BM_CORE_I : entity work.CB2BM_CORE
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- Control Bus Endpoint interface
         UPS_DATA       => UPS_FL.DATA,
         UPS_SOP        => ups_sof,
         UPS_EOP        => ups_eof,
         UPS_SRC_RDY    => ups_src_rdy,
         UPS_DST_RDY    => ups_dst_rdy,
         DNS_DATA       => DNS_FL.DATA,
         DNS_SOP        => dns_sof,
         DNS_EOP        => dns_eof,
         DNS_SRC_RDY    => dns_src_rdy,
         DNS_DST_RDY    => dns_dst_rdy,
         -- Bus Master Controller interface
         GLOBAL_ADDR    => BM.GLOBAL_ADDR,
         LOCAL_ADDR     => BM.LOCAL_ADDR,
         LENGTH         => BM.LENGTH,
         TAG            => BM.TAG,
         TRANS_TYPE     => BM.TRANS_TYPE,
         REQ            => BM.REQ,
         ACK            => BM.ACK,
         OP_TAG         => BM.OP_TAG,
         OP_DONE        => BM.OP_DONE
      );

end architecture full;
