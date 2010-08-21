--
-- mi32tobm_core.vhd: Easilly create busmaster transaction using mi32 interface
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
use work.ib_pkg.all;      -- Internal Bus Package
use work.lb_pkg.all;      -- Local Bus Package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity MI32TOBM_CORE is
   port (
      -- Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;
      -- MI32 interface
      MI32           : inout t_mi32;
      -- Endpoint Busmaster interface
      GLOBAL_ADDR    : out std_logic_vector(63 downto 0);   -- Global Address 
      LOCAL_ADDR     : out std_logic_vector(31 downto 0);   -- Local Address
      LENGTH         : out std_logic_vector(11 downto 0);   -- Length
      TAG            : out std_logic_vector(15 downto 0);   -- Operation TAG
      TRANS_TYPE     : out std_logic_vector(1 downto 0);    -- Transaction Type
      REQ            : out std_logic;                       -- Request
      -- Master Input interface
      ACK            : in std_logic;                       -- Ack
      OP_TAG         : in std_logic_vector(15 downto 0);   -- Operation TAG
      OP_DONE        : in std_logic                        -- Acknowledge
      );
end entity MI32TOBM_CORE;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture MI32TOBM_CORE_ARCH of MI32TOBM_CORE is

   signal global_addr_low_reg     : std_logic_vector(31 downto 0);
   signal global_addr_high_reg    : std_logic_vector(31 downto 0);
   signal local_addr_reg          : std_logic_vector(31 downto 0);
   signal length_reg              : std_logic_vector(31 downto 0);
   signal tag_reg                 : std_logic_vector(31 downto 0);
   signal control_reg             : std_logic_vector(31 downto 0);
   signal bm_req                  : std_logic;
   signal bm_op_tag               : std_logic_vector(15 downto 0);
   signal bm_pending              : std_logic;

begin

-- Master Interface Input
GLOBAL_ADDR <= global_addr_high_reg & global_addr_low_reg; 
LOCAL_ADDR  <= local_addr_reg;
LENGTH      <= length_reg(11 downto 0);
TAG         <= tag_reg(15 downto 0);
TRANS_TYPE  <= control_reg(2 downto 1);
REQ         <= bm_req;

-- Master Output interface
bm_op_tag      <= OP_TAG;

-- MI32
MI32.ARDY      <= '1';
MI32.DRDY      <= MI32.RD;

-- -------------------------------------------------------------------------
-- User registers
-- -------------------------------------------------------------------------
REGISTERS : process(CLK, RESET)
   begin
      if reset = '1' then
         global_addr_low_reg   <= X"00000000"; -- PCI address
         global_addr_high_reg  <= X"00000000"; -- PCI address
         local_addr_reg        <= X"00000000"; -- Local address
         length_reg            <= X"00000000"; -- Length
         tag_reg               <= X"00000000"; -- Tag
         control_reg           <= X"00000000"; -- Control reg; bit0 = start; bit1 = dir, 0 = G2L; bit2 = type, 0 - global, 1 - local

      elsif CLK = '1' and CLK'event then
         -- Write to my registers
         if (MI32.WR = '1') then
            case MI32.ADDR(4 downto 2) is
               -- Global Addr Low
               when "000" =>
                  for i in 0 to 3 loop
                     if MI32.BE(i) = '1' then
                        global_addr_low_reg(i*8+7 downto i*8) <= MI32.DWR(i*8+7 downto i*8);
                     end if;
                  end loop;
               -- Global Addr High
               when "001" =>
                  for i in 0 to 3 loop
                     if MI32.BE(i) = '1' then
                        global_addr_high_reg(i*8+7 downto i*8) <= MI32.DWR(i*8+7 downto i*8);
                     end if;
                  end loop;
               -- Local Addr
               when "010" =>
                  for i in 0 to 3 loop
                     if MI32.BE(i) = '1' then
                        local_addr_reg(i*8+7 downto i*8) <= MI32.DWR(i*8+7 downto i*8);
                     end if;
                  end loop;
               -- Length
               when "011" =>
                  for i in 0 to 3 loop
                     if MI32.BE(i) = '1' then
                        length_reg(i*8+7 downto i*8) <= MI32.DWR(i*8+7 downto i*8);
                     end if;
                  end loop;
               -- Tag_reg
               when "100" =>
                  for i in 0 to 3 loop
                     if MI32.BE(i) = '1' then
                        tag_reg(i*8+7 downto i*8) <= MI32.DWR(i*8+7 downto i*8);
                     end if;
                  end loop;

               -- Control Reg
               when "101" =>
                  for i in 0 to 3 loop
                     if MI32.BE(i) = '1' then
                        control_reg(i*8+7 downto i*8) <= MI32.DWR(i*8+7 downto i*8);
                     end if;
                  end loop;
               when others => null;
            end case;
         end if;


         -- Read from my registers
         case MI32.ADDR(4 downto 2) is
            when "000"    => MI32.DRD <= global_addr_low_reg;
            when "001"    => MI32.DRD <= global_addr_high_reg;
            when "010"    => MI32.DRD <= local_addr_reg;
            when "011"    => MI32.DRD <= length_reg;
            when "100"    => MI32.DRD <= tag_reg;
            when "101"    => MI32.DRD <= control_reg(31 downto 1) & bm_pending;
            when others   => MI32.DRD <= X"00000000";
         end case;
      end if;
end process;


-- -------------------------------------------------------------------------
-- BM control
-- -------------------------------------------------------------------------
BM_REQ_PROC: process(RESET, CLK)
   begin
      if (RESET = '1') then
         bm_req     <= '0';
         bm_pending <= '0';
      elsif (CLK = '1' and CLK'event) then
         -- Set/Clear the DMA reguest
         if (MI32.WR = '1') then
            if (MI32.ADDR(4 downto 2) = "101") and (MI32.BE(0) = '1') then
               bm_req <= MI32.DWR(0); -- set master request
            end if;
         elsif (ACK = '1') then    -- clear the request
            bm_req <= '0';
         end if;

         -- Set/Clear the DMA status flag
         if (bm_req = '1') then
            bm_pending <= '1';
         elsif (OP_DONE = '1') then
            bm_pending <= '0';
         end if;
      end if;
end process;


end architecture MI32TOBM_CORE_ARCH;
