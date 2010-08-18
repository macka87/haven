
-- flow_ctrl.vhd: AURVC Flow Control Unit 
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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
-- TODO: - 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on
use work.math_pack.all; 

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity flow_ctrl is
   generic (
      CHANNELS             : integer      -- Number of channels
   );
   port (
      -- Common Interface
      CLK               : in std_logic;
      RESET             : in std_logic;

      -- Input
      ALMOST_FULL       : in std_logic_vector(CHANNELS-1 downto 0);
      BUSY              : in std_logic;

      -- Output
      XON               : out std_logic;
      XOFF              : out std_logic;
      IFC_ID            : out std_logic_vector(max(log2(CHANNELS)-1, 0) downto 0)
   );
end flow_ctrl;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of flow_ctrl is

component xon_xoff_buffer is
   port (
      -- Common Interface
      CLK               : in std_logic;
      RESET             : in std_logic;

      -- Input
      ALMOST_FULL       : in std_logic;
      READ              : in std_logic;
      
      -- Output
      XON_XOFF          : out std_logic; 
      EMPTY             : out std_logic

   );
end component;

component first_one_detector is
   generic (
      DATA_WIDTH  : integer
   );
   port (
      -- Input
      MASK     : in std_logic_vector(DATA_WIDTH-1 downto 0);

      -- Output
      FIRST_ONE_ONEHOT  : out std_logic_vector(DATA_WIDTH-1 downto 0);         -- Position of the first 'one' in ONEHOT coding
      FIRST_ONE_BINARY  : out std_logic_vector(max(log2(DATA_WIDTH)-1, 0) downto 0);   -- Position of the first 'one' in BINARY coding
      FIRST_ONE_PRESENT : out std_logic                                        -- Deasserted if no 'one' is present in input MASK
   );
end component;

component flow_ctrl_fsm is
   port (
      -- Common Input
      CLK      : in std_logic;
      RESET    : in std_logic;

      -- Input
      CHNL_VALID     : in std_logic;
      XON_XOFF       : in std_logic;
      BUSY           : in std_logic;

      -- Output
      READ           : out std_logic;
      XON            : out std_logic;
      XOFF           : out std_logic;
      REG_CHNL_MASK_RST  : out std_logic 
   );
end component;

signal read : std_logic_vector(CHANNELS-1 downto 0);
signal read_i  : std_logic;
signal xon_xoff : std_logic_vector(CHANNELS-1 downto 0);
signal xon_xoff_i : std_logic;
signal empty : std_logic_vector(CHANNELS-1 downto 0);

-- Arbiter signals
signal active_chnl_onehot  : std_logic_vector(CHANNELS-1 downto 0);
signal active_chnl_binary  : std_logic_vector(max(log2(CHANNELS)-1, 0) downto 0);
signal channel_valid       : std_logic;

-- reg_chnl_mask signals
signal reg_chnl_mask : std_logic_vector(CHANNELS-1 downto 0);
signal reg_chnl_mask_rst   : std_logic_vector(CHANNELS-1 downto 0);
signal reg_chnl_mask_set   : std_logic_vector(CHANNELS-1 downto 0);
signal reg_chnl_mask_rst_enable  : std_logic;
signal reg_chnl_mask_set_enable  : std_logic;

begin

xon_xoff_buffer_gen: for i in 0 to CHANNELS-1 generate
xon_xoff_buffer_u: xon_xoff_buffer
   port map(
      -- Common Interface
      CLK               => CLK,
      RESET             => RESET,

      -- Input
      ALMOST_FULL       => ALMOST_FULL(i),
      READ              => read(i),
      
      -- Output
      XON_XOFF          => xon_xoff(i),
      EMPTY             => empty(i)
   );
end generate;

-- -------------------------------------------------------------
-- CHANNEL ARBITER
chnl_arbiter_u: first_one_detector
   generic map (
      DATA_WIDTH  => CHANNELS
   )
   port map(
      -- Input
      MASK     => reg_chnl_mask,

      -- Output
      FIRST_ONE_ONEHOT  => active_chnl_onehot,
      FIRST_ONE_BINARY  => active_chnl_binary,
      FIRST_ONE_PRESENT => channel_valid
   );
reg_chnl_mask_set_enable <= not channel_valid;
IFC_ID <= active_chnl_binary;

-- -------------------------------------------------------------
-- reg_chnl_mask
reg_chnl_mask_set_gen: for i in 0 to CHANNELS-1 generate
   reg_chnl_mask_set(i) <= (not empty(i)) and reg_chnl_mask_set_enable;
end generate;

reg_chnl_mask_rst_gen: for i in 0 to CHANNELS-1 generate
   reg_chnl_mask_rst(i) <= active_chnl_onehot(i) and reg_chnl_mask_rst_enable;
end generate;

reg_chnl_mask_gen: for i in 0 to CHANNELS-1 generate
   process (CLK, RESET)
   begin
      if (RESET = '1') then
         reg_chnl_mask(i) <= '0';
      elsif (CLK'event and CLK = '1') then
         if (reg_chnl_mask_rst(i) = '1') then
            reg_chnl_mask(i) <= '0';
         elsif (reg_chnl_mask_set(i) = '1') then
            reg_chnl_mask(i) <= '1';
         end if;
      end if;
   end process;
end generate;

-- -------------------------------------------------------------
-- XON/XOFF Buffer multiplexer
process (active_chnl_binary, xon_xoff, read_i)
begin
   READ <= (others => '0');
   xon_xoff_i <= '0';
   for i in 0 to CHANNELS-1 loop
      if (active_chnl_binary = conv_std_logic_vector(i,max(log2(CHANNELS), 1))) then
         xon_xoff_i <= xon_xoff(i);
         read(i) <= read_i;
      end if;
   end loop;
end process;


-- -------------------------------------------------------------
-- Flow Controller FSM
flow_ctrl_fsm_u: flow_ctrl_fsm
   port map(
      -- Common Input
      CLK      => CLK,
      RESET    => RESET,

      -- Input
      CHNL_VALID     => channel_valid,
      XON_XOFF       => xon_xoff_i,
      BUSY           => BUSY,

      -- Output
      READ           => read_i,
      XON            => XON,
      XOFF           => XOFF,
      REG_CHNL_MASK_RST  => reg_chnl_mask_rst_enable
   );

end behavioral;

