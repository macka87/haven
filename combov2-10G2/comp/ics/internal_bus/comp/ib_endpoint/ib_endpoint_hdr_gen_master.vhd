--
-- lb_endpoint_hdr_gen.vhd: Internal Bus Header Generator
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
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use work.ib_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_ENDPOINT_HDR_GEN_MASTER is
   port (
      -- Slave Interface
      RD_COMPL_DST_ADDR     : in  std_logic_vector(31 downto 0);
      RD_COMPL_SRC_ADDR     : in  std_logic_vector(31 downto 0);
      RD_COMPL_TAG          : in  std_logic_vector(15 downto 0);
      RD_COMPL_LENGTH       : in  std_logic_vector(11 downto 0);
              
      -- Master Interface
      MASTER_GLOBAL_ADDR    : in  std_logic_vector(63 downto 0);
      MASTER_LOCAL_ADDR     : in  std_logic_vector(31 downto 0);
      MASTER_TAG            : in  std_logic_vector(15 downto 0);
      MASTER_LENGTH         : in  std_logic_vector(11 downto 0);

      -- Control Interface
      GET_SLAVE_MASTER      : in  std_logic; -- 0-Slave/1-Master
      GET_SECOND_HDR        : in  std_logic; -- Get 0-First/1-Second header
      GET_TRANS_TYPE        : in  std_logic_vector(1 downto 0); -- Transaction Type

      -- Output Interface
      HEADER_DATA           : out std_logic_vector(63 downto 0) -- Header data
      );
end entity IB_ENDPOINT_HDR_GEN_MASTER;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_ENDPOINT_HDR_GEN_MASTER_ARCH of IB_ENDPOINT_HDR_GEN_MASTER is

   signal rd_completition_hdr1 : std_logic_vector(63 downto 0);
   signal rd_completition_hdr2 : std_logic_vector(63 downto 0);
   signal l2gw_hdr1            : std_logic_vector(63 downto 0);
   signal l2gw_hdr2            : std_logic_vector(63 downto 0);
   signal g2lr_hdr1            : std_logic_vector(63 downto 0);
   signal g2lr_hdr2            : std_logic_vector(63 downto 0);
   signal l2lw_hdr1            : std_logic_vector(63 downto 0);
   signal l2lw_hdr2            : std_logic_vector(63 downto 0);
   signal l2lr_hdr1            : std_logic_vector(63 downto 0);
   signal l2lr_hdr2            : std_logic_vector(63 downto 0);
   signal mux_header_data_sel  : std_logic_vector(3 downto 0);


begin

rd_completition_hdr1 <= RD_COMPL_DST_ADDR & RD_COMPL_TAG & '1' & C_IB_RD_COMPL_TRANSACTION & RD_COMPL_LENGTH;
rd_completition_hdr2 <= X"00000000" & RD_COMPL_SRC_ADDR;

l2gw_hdr1            <= MASTER_GLOBAL_ADDR(31 downto 0)  & MASTER_TAG  & '0' & C_IB_L2GW_TRANSACTION & MASTER_LENGTH;
l2gw_hdr2            <= MASTER_GLOBAL_ADDR(63 downto 32) & MASTER_LOCAL_ADDR;
g2lr_hdr1            <= MASTER_GLOBAL_ADDR(31 downto 0)  & MASTER_TAG  & '0' & C_IB_G2LR_TRANSACTION & MASTER_LENGTH;
g2lr_hdr2            <= MASTER_GLOBAL_ADDR(63 downto 32) & MASTER_LOCAL_ADDR;

l2lw_hdr1            <= MASTER_GLOBAL_ADDR(31 downto 0)  & MASTER_TAG  & '1' & C_IB_L2LW_TRANSACTION & MASTER_LENGTH;
l2lw_hdr2            <= X"00000000" & MASTER_LOCAL_ADDR;
l2lr_hdr1            <= MASTER_GLOBAL_ADDR(31 downto 0)  & MASTER_TAG  & '0' & C_IB_L2LR_TRANSACTION & MASTER_LENGTH;
l2lr_hdr2            <= X"00000000" & MASTER_LOCAL_ADDR;



mux_header_data_sel <= GET_SLAVE_MASTER & GET_SECOND_HDR & GET_TRANS_TYPE;

-- multiplexor header_data ---------------------------------------------------
mux_header_datap: process(mux_header_data_sel, rd_completition_hdr1, rd_completition_hdr2,
                          l2gw_hdr1, l2gw_hdr2, g2lr_hdr1, g2lr_hdr2, l2lw_hdr1, l2lw_hdr2,
                          l2lr_hdr1, l2lr_hdr2)
begin
   case mux_header_data_sel is
      when "0000"   => HEADER_DATA <= rd_completition_hdr1;
      when "0100"   => HEADER_DATA <= rd_completition_hdr2;
      
      when "1010"   => HEADER_DATA <= l2lr_hdr1;
      when "1011"   => HEADER_DATA <= l2lw_hdr1; 
      when "1000"   => HEADER_DATA <= g2lr_hdr1;
      when "1001"   => HEADER_DATA <= l2gw_hdr1;

      when "1110"   => HEADER_DATA <= l2lr_hdr2;
      when "1111"   => HEADER_DATA <= l2lw_hdr2;
      when "1100"   => HEADER_DATA <= g2lr_hdr2;
      when "1101"   => HEADER_DATA <= l2gw_hdr2;
      when others   => HEADER_DATA <= (others => 'X');
   end case;
end process;


end architecture IB_ENDPOINT_HDR_GEN_MASTER_ARCH;

