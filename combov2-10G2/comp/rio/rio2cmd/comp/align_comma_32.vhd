-- *
-- ***********************************************************
-- ***********************************************************
-- *
-- * XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION "AS IS"
-- * AS A COURTESY TO YOU, SOLELY FOR USE IN DEVELOPING PROGRAMS AND
-- * SOLUTIONS FOR XILINX DEVICES. BY PROVIDING THIS DESIGN, CODE,
-- * OR INFORMATION AS ONE POSSIBLE IMPLEMENTATION OF THIS FEATURE,
-- * APPLICATION OR STANDARD, XILINX IS MAKING NO REPRESENTATION
-- * THAT THIS IMPLEMENTATION IS FREE FROM ANY CLAIMS OF INFRINGEMENT,
-- * AND YOU ARE RESPONSIBLE FOR OBTAINING ANY RIGHTS YOU MAY REQUIRE
-- * FOR YOUR IMPLEMENTATION. XILINX EXPRESSLY DISCLAIMS ANY
-- * WARRANTY WHATSOEVER WITH RESPECT TO THE ADEQUACY OF THE
-- * IMPLEMENTATION, INCLUDING BUT NOT LIMITED TO ANY WARRANTIES OR
-- * REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE FROM CLAIMS OF
-- * INFRINGEMENT, IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
-- * FOR A PARTICULAR PURPOSE.
-- *
-- * (c) Copyright 2002 Xilinx Inc.
-- * All rights reserved.
-- *
--************************************************************
-- Virtex-II Pro RocketIO comma alignment module
--
-- This module reads RXDATA[31:0] from a RocketIO transceiver
-- and copies it to
-- its output, realigning it if necessary so that commas
-- are aligned to the MSB position
-- [31:24]. The module assumes ALIGN_COMMA_MSB is TRUE,
-- so that the comma
-- is already aligned to [31:24] or [15:8].
--
-- Outputs
--
-- aligned_data[31:0] -- Properly aligned 32-std_logic ALIGNED_DATA
-- sync -- Indicator that aligned_data is properly aligned
-- aligned_rxisk[3:0] -properly aligned 4-std_logic RXCHARISK
-- Inputs - These are all RocketIO inputs or outputs
-- as indicated:
--
-- usrclk2 -- RXUSRCLK2
-- rxreset -- RXRESET
-- rxdata[31:0] RXDATA[31:0] -- (commas aligned to
-- [31:24] or [15:8])
-- rxisk[3:0] - RXCHARISK[3:0]
-- rxrealign -- RXREALIGN
-- rxcommadet -- RXCOMMADET
-- rxchariscomma3 -- RXCHARISCOMMA[3]
-- rxchariscomma1 -- RXCHARISCOMMA[1]
--
LIBRARY IEEE;
USE IEEE.std_logic_1164.all;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.Numeric_STD.all;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

ENTITY align_comma_32 IS
PORT (
   ALIGNED_DATA      : out std_logic_vector(31 downto 0);
   ALIGNED_RXISK     : out std_logic_vector(3 downto 0);
   SYNC              : out std_logic;
   USRCLK2           : in std_logic;
   RXRESET           : in std_logic;
   RXDATA            : in std_logic_vector(31 downto 0);
   RXISK             : in std_logic_vector(3 downto 0);
   RXREALIGN         : in std_logic;
   RXCOMMADET        : in std_logic;
   RXCHARISCOMMA3    : in std_logic;
   RXCHARISCOMMA1    : in std_logic
  );
END ENTITY align_comma_32;

ARCHITECTURE translated OF align_comma_32 IS
SIGNAL rxdata_reg : std_logic_vector(15 DOWNTO 0);
SIGNAL rxisk_reg : std_logic_vector(1 DOWNTO 0);
SIGNAL byte_sync : std_logic;
SIGNAL wait_to_sync : std_logic_vector(3 DOWNTO 0);
SIGNAL count : std_logic;
SIGNAL rxdata_hold : std_logic_vector(31 DOWNTO 0);
SIGNAL rxisk_hold : std_logic_vector(3 DOWNTO 0);
SIGNAL sync_hold : std_logic;

BEGIN
aligned_data <= rxdata_hold;
aligned_rxisk <= rxisk_hold;
sync <= sync_hold;

-- This process maintains wait_to_sync and count,
-- which are used only to
-- maintain output sync; this provides some idea
-- of when the output is properly
-- aligned, with the comma in aligned_data[31:24].
-- The counter is set to a high value
-- whenever the elastic buffer is reinitialized;
-- that is, upon asserted RXRESET or
-- RXREALIGN. Count-down is enabled whenever a
-- comma is known to have
-- come through the comma detection circuit, that
-- is, upon an asserted RXREALIGN
-- or RXCOMMADET.
PROCESS (usrclk2)
BEGIN
   IF (usrclk2'EVENT AND usrclk2 = '1') THEN
      IF (rxreset = '1') THEN
         wait_to_sync <= "1111";
         count <= '0';
      ELSE
         IF (rxrealign = '1') THEN
            wait_to_sync <= "1111";
            count <= '1';
         ELSE
            IF (count = '1') THEN
               IF (wait_to_sync /= "0000") THEN
                  wait_to_sync <= wait_to_sync - "0001";
               END IF;
            END IF;
            IF (rxcommadet = '1') THEN
               count <= '1';
            END IF;
         END IF;
      END IF;
   END IF;
END PROCESS;

-- This process maintains output sync, which
-- indicates when outgoing aligned_data
-- should be properly aligned, with the comma
-- in aligned_data[31:24]. Output aligned_data is
-- considered to be in sync when a comma is seen
-- on rxdata (as indicated
-- by rxchariscomma3 or 1) after the counter
-- wait_to_sync has reached 0, indicating
-- that commas seen by the comma detection circuit
-- have had time to propagate to
-- aligned_data after initialization of the elastic buffer.
PROCESS (usrclk2)
BEGIN
   IF (usrclk2'EVENT AND usrclk2 = '1') THEN
      IF ((rxreset OR rxrealign) = '1') THEN
         sync_hold <= '0';
      ELSE
         IF (wait_to_sync = "0000")THEN
            IF ((rxchariscomma3 OR rxchariscomma1) = '1') THEN
               sync_hold <= '1';
            END IF;
         END IF;
      END IF;
   END IF;
END PROCESS;

-- This process generates aligned_data with commas
-- aligned in [31:24],
-- assuming that incoming commas are aligned
-- to [31:24] or [15:8].
-- Here, you could add code to use ENPCOMMAALIGN and
-- ENMCOMMAALIGN to enable a move back into the
-- byte_sync=0 state.
PROCESS (usrclk2, rxreset)
BEGIN
   IF (rxreset = '1') THEN
      rxdata_reg <= "0000000000000000";
      rxdata_hold <= "00000000000000000000000000000000";
      rxisk_reg <= "00";
      rxisk_hold <= "0000";
      byte_sync <= '0';
   ELSIF (usrclk2'EVENT AND usrclk2 = '1') THEN
      rxdata_reg(15 DOWNTO 0) <= rxdata(15 DOWNTO 0);
      rxisk_reg(1 DOWNTO 0) <= rxisk(1 DOWNTO 0);
      IF (rxchariscomma3 = '1') THEN
         rxdata_hold(31 DOWNTO 0) <= rxdata(31 DOWNTO 0);
         rxisk_hold(3 DOWNTO 0) <= rxisk(3 DOWNTO 0);
         byte_sync <= '0';
      ELSE
         IF ((rxchariscomma1 OR byte_sync) = '1') THEN
            rxdata_hold(31 DOWNTO 0) <= rxdata_reg(15 DOWNTO 0) &
            rxdata(31 DOWNTO 16);
            rxisk_hold(3 DOWNTO 0) <= rxisk_reg(1 DOWNTO 0) &
            rxisk(3 DOWNTO 2);
            byte_sync <= '1';
         ELSE
            rxdata_hold(31 DOWNTO 0) <= rxdata(31 DOWNTO 0);
            rxisk_hold(3 DOWNTO 0) <= rxisk(3 DOWNTO 0);
         END IF;
      END IF;
   END IF;
END PROCESS;

END ARCHITECTURE translated;

