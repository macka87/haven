-- led_ctrl_top4.vhd: LED controller wrapper - 4 instantions of led_ctrl
-- Copyright (C) 2009 CESNET
-- Author(s): Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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

-- ----------------------------------------------------------------------------
--                      Entity declaration
-- ----------------------------------------------------------------------------
entity led_ctrl_top4 is

   generic (
      -- Length of the internal counter, determines period of blinks
      CNTR_SIZE            : integer := 25
   );

   port (
      -- Common signals -------------------------------------------------------
      -- Clock signal
      CLK                  : in std_logic;
      -- Global synchronous reset
      RESET                : in  std_logic;
   
      -- LED controller 0 ------------------------------------------------------
      -- '1' when coresponding line is up, '0' otherwise
      LINE_UP_0            : in std_logic;
      -- '1' when packet is being processed, '0' otherwise
      PACKET_0             : in std_logic;

      -- Determines if the LED should be on '0' or not '1'
      LED_0                : out std_logic;

      -- LED controller 1 ------------------------------------------------------
      -- '1' when coresponding line is up, '0' otherwise
      LINE_UP_1            : in std_logic;
      -- '1' when packet is being processed, '0' otherwise
      PACKET_1             : in std_logic;

      -- Determines if the LED should be on '0' or not '1'
      LED_1                : out std_logic;
      
      -- LED controller 2 ------------------------------------------------------
      -- '1' when coresponding line is up, '0' otherwise
      LINE_UP_2            : in std_logic;
      -- '1' when packet is being processed, '0' otherwise
      PACKET_2             : in std_logic;

      -- Determines if the LED should be on '0' or not '1'
      LED_2                : out std_logic;
      
      -- LED controller 3 ------------------------------------------------------
      -- '1' when coresponding line is up, '0' otherwise
      LINE_UP_3            : in std_logic;
      -- '1' when packet is being processed, '0' otherwise
      PACKET_3             : in std_logic;

      -- Determines if the LED should be on '0' or not '1'
      LED_3                : out std_logic
   );

end entity led_ctrl_top4;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture led_ctrl_top4_arch of led_ctrl_top4 is

begin

   -- LED controller 0 ---------------------------------------------------------
   led_ctrl_0 : entity work.led_ctrl
   generic map(
      CNTR_SIZE      => CNTR_SIZE
   )
   port map(
      -- common signals
      CLK            => CLK,
      RESET          => RESET,
      
      -- inputs
      LINE_UP        => LINE_UP_0,
      PACKET         => PACKET_0,
      
      -- output
      LED            => LED_0
   );
   
   -- LED controller 1 ---------------------------------------------------------
   led_ctrl_1 : entity work.led_ctrl
   generic map(
      CNTR_SIZE      => CNTR_SIZE
   )
   port map(
      -- common signals
      CLK            => CLK,
      RESET          => RESET,

      -- inputs
      LINE_UP        => LINE_UP_1,
      PACKET         => PACKET_1,

      -- output
      LED            => LED_1
   );
   
   -- LED controller 2 ---------------------------------------------------------
   led_ctrl_2 : entity work.led_ctrl
   generic map(
      CNTR_SIZE      => CNTR_SIZE
   )
   port map(
      -- common signals
      CLK            => CLK,
      RESET          => RESET,

      -- inputs
      LINE_UP        => LINE_UP_2,
      PACKET         => PACKET_2,

      -- output
      LED            => LED_2
   );
   
   -- LED controller 3 ---------------------------------------------------------
   led_ctrl_3 : entity work.led_ctrl
   generic map(
      CNTR_SIZE      => CNTR_SIZE
   )
   port map(
      -- common signals
      CLK            => CLK,
      RESET          => RESET,

      -- inputs
      LINE_UP        => LINE_UP_3,
      PACKET         => PACKET_3,

      -- output
      LED            => LED_3
   );

end architecture led_ctrl_top4_arch;
