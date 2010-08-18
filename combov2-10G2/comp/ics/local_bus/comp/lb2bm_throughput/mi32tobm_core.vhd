--
-- mi32tobm_core.vhd: Easilly create busmaster transaction using mi32 interface
--                    with "throughput measurer" support
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--            Pavol Korcek <korcek@liberouter.org> 
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
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
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
   signal tag_cnt                 : std_logic_vector(15 downto 0);
   signal control_reg             : std_logic_vector(31 downto 0);
   signal bm_req                  : std_logic;
   signal bm_op_tag               : std_logic_vector(15 downto 0);

   -- timer
   signal timer_cnt               : std_logic_vector(63 downto 0);
   signal timer_cnt_en            : std_logic;
   
   -- bm request counter
   signal bmreq_cnt               : std_logic_vector(63 downto 0); 
   signal bmreq_init              : std_logic_vector(63 downto 0);
   signal init_wr                 : std_logic;
   signal init_wr_reg             : std_logic;

   -- bm done counter
   signal bmdone_cnt              : std_logic_vector(63 downto 0);

   -- last request
   signal last_req                : std_logic;

   -- last done
   signal last_done_n               : std_logic;

   -- request to BM
   signal req_signal              : std_logic;

   -- some BM request are still waitting
   signal bm_req_waiting          : std_logic;

begin

   -- tag counte --------------------------------------------------------------
   tag_cntp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            tag_cnt <= (others => '0');
         else
            tag_cnt <= tag_cnt + 1;
         end if;
      end if;
   end process;

   -- register timer_cnt_en ---------------------------------------------------
   timer_cnt_enp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            timer_cnt_en <= '0';
         elsif(last_req = '1' and last_done_n = '0') then
            timer_cnt_en <= '0';
         elsif(bm_req = '1') then
            timer_cnt_en <= '1';
         end if;
      end if;
   end process;

   -- counter timer_cnt -------------------------------------------------------
   timer_cntp: process(RESET, CLK)
   begin 
      if (CLK'event AND CLK = '1') then
         if (RESET = '1' or init_wr_reg = '1') then
            timer_cnt <= (others => '0');
         elsif(timer_cnt_en = '1' or bm_req = '1') then
            timer_cnt <= timer_cnt + 1;
         end if;
      end if;
   end process;

   -- last BM request signaling -----------------------------------------------
   last_req <= '1' when (bmreq_cnt = X"0000000000000000")  else '0';

   -- counter bmreq_cnt -------------------------------------------------------
   bmreq_cntp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            bmreq_cnt <= (others => '0');    -- number of requests
         elsif (ACK = '1') then
            bmreq_cnt <= bmreq_cnt - 1;
         elsif(init_wr_reg = '1') then       -- init phase
            bmreq_cnt <= bmreq_init;
         end if;
      end if;
   end process;

   -- register of init phase ---------------------------------------------------
   init_wr_regp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            init_wr_reg <= '0';
         else
            init_wr_reg <= init_wr;
         end if;
      end if;
   end process;

   -- counter bmdone_cnt ------------------------------------------------------
   bmdone_cntp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            bmdone_cnt <= (others => '0');   -- number of requests
         elsif (OP_DONE = '1') then
            bmdone_cnt <= bmdone_cnt - 1;
         elsif (init_wr_reg = '1') then      -- init phase
            bmdone_cnt <= bmreq_init;
         end if;
      end if;
   end process;

   -- last BM operation signaling ---------------------------------------------
   last_done_n <= '0' when (bmdone_cnt = X"0000000000000000")  else '1';

 
-- Master Interface Input
GLOBAL_ADDR <= global_addr_high_reg & global_addr_low_reg; 
LOCAL_ADDR  <= local_addr_reg;
LENGTH      <= length_reg(11 downto 0);

-- use tag counter to prevent same tags for DMA transfers
TAG         <= tag_cnt;    -- tag_reg(15 downto 0);
TRANS_TYPE  <= control_reg(2 downto 1);

req_signal         <= (bm_req or bm_req_waiting) and (not last_req);
REQ                <= req_signal;


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
         bmreq_init            <= X"0000000000000000"; -- number of continuos DMA transfers
         init_wr               <= '0';

      elsif CLK = '1' and CLK'event then
         
         init_wr <= '0';
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

               -- req_low_reg
               when "110" =>
                  for i in 0 to 3 loop
                     if MI32.BE(i) = '1' then
                        bmreq_init(i*8+7 downto i*8) <= MI32.DWR(i*8+7 downto i*8);
                     end if;
                  end loop;

               -- req_high_reg
               when "111" =>
                  for i in 0 to 3 loop
                     if MI32.BE(i) = '1' then
                        bmreq_init(32+(i*8+7) downto 32+(i*8)) <= MI32.DWR(i*8+7 downto i*8);
                     end if;
                  end loop;
                  init_wr <= '1';   -- set final init phase

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
            when "101"    => MI32.DRD <= control_reg(31 downto 1) & last_done_n;
            when "110"    => MI32.DRD <= timer_cnt(31 downto 0);        -- uses same address of register as bmreq
            when "111"    => MI32.DRD <= timer_cnt(63 downto 32);       -- dtto
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
         bm_req_waiting <= '0';
      elsif (CLK = '1' and CLK'event) then
         -- Set/Clear the DMA reguest
         if (MI32.WR = '1') then
            if (MI32.ADDR(4 downto 2) = "101") and (MI32.BE(0) = '1') then
               bm_req <= MI32.DWR(0); -- set master request
            end if;
         elsif (ACK = '1') then    -- clear the request
            bm_req <= '0';
         end if;

         -- Set/Clear next BM request waiting
         if (bm_req = '1') then
            bm_req_waiting <= '1';
         elsif(last_req = '1') then
            bm_req_waiting <= '0';
         end if;

      end if;
end process;


end architecture MI32TOBM_CORE_ARCH;
