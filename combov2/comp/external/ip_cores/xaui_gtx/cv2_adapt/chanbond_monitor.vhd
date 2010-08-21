-----------------------------------------------------------------------------
-- Title      : VHDL Channel Bonding Monitor
-- Project    : XAUI
-- File       : chanbond_monitor.vhd
-- Author     : Xilinx Inc.
-- Description: This module holds the Channel Bonding monitor circuitry
-----------------------------------------------------------------------------
-- (c) Copyright 2007 - 2009 Xilinx, Inc. All rights reserved. 
-- This file contains confidential and proprietary information
-- of Xilinx, Inc. and is protected under U.S. and
-- international copyright and other intellectual property
-- laws.
--
-- DISCLAIMER
-- This disclaimer is not a license and does not grant any
-- rights to the materials distributed herewith. Except as
-- otherwise provided in a valid license issued to you by
-- Xilinx, and to the maximum extent permitted by applicable
-- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
-- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
-- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
-- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
-- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
-- (2) Xilinx shall not be liable (whether in contract or tort,
-- including negligence, or under any other theory of
-- liability) for any loss or damage of any kind or nature
-- related to, arising under or in connection with these
-- materials, including for any direct, or any indirect,
-- special, incidental, or consequential loss or damage
-- (including loss of data, profits, goodwill, or any type of
-- loss or damage suffered as a result of any action brought
-- by a third party) even if such damage or loss was
-- reasonably foreseeable or Xilinx had been advised of the
-- possibility of the same.
--
-- CRITICAL APPLICATIONS
-- Xilinx products are not designed or intended to be fail-
-- safe, or for use in any application requiring fail-safe
-- performance, such as life-support or safety devices or
-- systems, Class III medical devices, nuclear facilities,
-- applications related to the deployment of airbags, or any
-- other applications that could lead to death, personal
-- injury, or severe property or environmental damage
-- (individually and collectively, "Critical
-- Applications"). Customer assumes the sole risk and
-- liability of any use of Xilinx products in Critical
-- Applications, subject only to applicable laws and
-- regulations governing limitations on product liability.
--
-- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
-- PART OF THIS FILE AT ALL TIMES.
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

--***********************************Entity Declaration*******************************

entity chanbond_monitor is
port
(
    CLK                     :  in  std_logic;    
    RST                     :  in  std_logic;
    COMMA_ALIGN_DONE        :  in  std_logic;
    CORE_ENCHANSYNC         :  in  std_logic;
    CHANBOND_DONE           :  in  std_logic;
    RXRESET                 :  out std_logic
);
end chanbond_monitor;

architecture rtl of chanbond_monitor is
type STATE_TYP is (IDLE, WAIT_FOR_ALIGN, CB_SEARCH, RESET);
signal cnt                     : unsigned(7 downto 0) := (others => '0');
signal enable_cnt              : std_logic;
signal state, next_state : STATE_TYP;

begin

-- Current State Update
process(CLK)
begin
  if rising_edge(CLK) then
    if RST = '1' then
      state <= IDLE;
    else
      state <= next_state;
    end if;
  end if;
end process;

-- Next State Assignment
process( state, COMMA_ALIGN_DONE, CORE_ENCHANSYNC, CHANBOND_DONE, cnt)
begin
    next_state <= state;
  
  case state is
    when IDLE =>
      if CORE_ENCHANSYNC = '1' and CHANBOND_DONE = '0' then
        next_state  <= WAIT_FOR_ALIGN;
      end if;
      
    when WAIT_FOR_ALIGN =>  
      if COMMA_ALIGN_DONE = '1' then
        next_state  <= CB_SEARCH;
      end if;
      
    when CB_SEARCH =>
      if COMMA_ALIGN_DONE = '0' then            
        next_state <= WAIT_FOR_ALIGN;
      elsif CHANBOND_DONE = '1' then
        next_state <= IDLE;
      elsif cnt(7) = '1' then
        next_state <= RESET;
      else
        next_state <= CB_SEARCH;
      end if;  
            
    when RESET =>
      next_state  <=  WAIT_FOR_ALIGN;
      
    when OTHERS =>    
      next_state  <=  IDLE;
  
  end case;
end process;

-- Registered Output Assignment
process(CLK)
begin
  if rising_edge(CLK) then
    if RST = '1' then
      enable_cnt      <= '0';
      RXRESET         <= '0';
    else      
      -- Default Assignments
      enable_cnt      <= '0';
      RXRESET         <= '0';
    
    case state is      
      when CB_SEARCH =>
        enable_cnt <= '1';
        
      when RESET =>
        RXRESET <= '1';
                  
      when OTHERS =>
        enable_cnt  <=  '0';  
        RXRESET     <= '0';
    end case;
    end if;
  end if;
end process;

-- CB_SEARCH Timeout Counter
process (CLK)
begin
  if rising_edge(CLK) then    
    if enable_cnt = '0' then
      cnt <= (others => '0');
    else
      cnt <= cnt + 1;
    end if;
  end if;
end process;

end rtl;
  
