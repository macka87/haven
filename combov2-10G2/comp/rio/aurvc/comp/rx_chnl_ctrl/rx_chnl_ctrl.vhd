
-- rx_chnl_ctrl.vhd: RX Channel Controller 
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

entity rx_chnl_ctrl is
   generic (
      DATA_PATHS           : integer;     -- Number of bytes of data port
      CHANNELS             : integer      -- Number of channels
   );
   port (
      -- Common Interface
      CLK               : in std_logic;
      RESET             : in std_logic;

      -- Data Multiplexers Control
      RX_IFC_ID         : out std_logic_vector(max(log2(CHANNELS)-1, 0) downto 0);

      -- RX Buffer Control Interface
      FIFO_WRITE        : out std_logic;
      FIFO_ALMOST_FULL  : in std_logic_vector(CHANNELS-1 downto 0);

      -- Aurora LocalLink RX Interface
      RX_D              : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      RX_SRC_RDY_N      : in std_logic;
      RX_SOF_N          : in std_logic;
      RX_EOF_N          : in std_logic;

      -- Aurora UFC TX Inteface
      UFC_TX_DATA      : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      UFC_TX_REQ_N     : out std_logic;
      UFC_TX_MS        : out std_logic_vector(0 to 2);
      UFC_TX_ACK_N     : in std_logic
   );
end rx_chnl_ctrl;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of rx_chnl_ctrl is

component rx_chnl_ctrl_fsm is
   port (
      -- Common Input
      CLK      : in std_logic;
      RESET    : in std_logic;

      -- Input
      AUR_RX_SRC_RDY_N              : in std_logic;
      AUR_RX_SOF_N                  : in std_logic;
      AUR_RX_EOF_N                  : in std_logic;

      -- Output
      FIFO_WRITE                    : out std_logic;
      REG_IFC_ID_WE                 : out std_logic 
   );
end component;

component flow_ctrl is
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
end component;

component message_tx is
   generic (
      DATA_PATHS  : integer      -- Number of bytes of data port
   );
   port (
      -- Common Input
      CLK   : in std_logic;
      RESET : in std_logic;

      -- Flow Controller Interface
      IFC_ID   : in std_logic_vector(7 downto 0);
      XON      : in std_logic;
      XOFF     : in std_logic;
      BUSY     : out std_logic;

      -- Aurora UFC TX Interface
      UFC_TX_DATA    : out std_logic_vector((DATA_PATHS*8)-1 downto 0); -- Big Endian format!!!
      UFC_TX_REQ_N   : out std_logic;
      UFC_TX_MS      : out std_logic_vector(0 to 2);
      UFC_TX_ACK_N   : in std_logic
   );
end component;

   signal reg_ifc_id : std_logic_vector(max(log2(CHANNELS)-1, 0) downto 0);
   signal reg_ifc_id_we : std_logic;
   
   -- Message TX Controller signals
   signal txmsg_busy : std_logic;
   signal txmsg_xon : std_logic;
   signal txmsg_xoff : std_logic;
   signal txmsg_ifc_id_i : std_logic_vector(max(log2(CHANNELS)-1, 0) downto 0);
   signal txmsg_ifc_id : std_logic_vector(7 downto 0);

begin

process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_ifc_id <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (reg_ifc_id_we = '1') then
         reg_ifc_id <= RX_D(((DATA_PATHS-1)*8) + max(log2(CHANNELS)-1, 0) downto (DATA_PATHS-1)*8);
      end if;
   end if;
end process;

RX_IFC_ID <= reg_ifc_id;

rx_chnl_ctrl_fsm_u: rx_chnl_ctrl_fsm
   port map(
      -- Common Input
      CLK      => CLK,
      RESET    => RESET,

      -- Input
      AUR_RX_SRC_RDY_N              => RX_SRC_RDY_N,
      AUR_RX_SOF_N                  => RX_SOF_N,
      AUR_RX_EOF_N                  => RX_EOF_N,

      -- Output
      FIFO_WRITE                    => FIFO_WRITE,
      REG_IFC_ID_WE                 => reg_ifc_id_we
   );

flow_ctrl_u: flow_ctrl
   generic map(
      CHANNELS             => CHANNELS
   )
   port map(
      -- Common Interface
      CLK               => CLK,
      RESET             => RESET,

      -- INPUT
      ALMOST_FULL       => FIFO_ALMOST_FULL,
      BUSY              => txmsg_busy,

      -- Output
      XON               => txmsg_xon,
      XOFF              => txmsg_xoff,
      IFC_ID            => txmsg_ifc_id_i
   );

-- -------------------------------------------------------------
-- Message TX Controller
txmsg_ifc_id_gen: for i in 0 to 7 generate
   tx_ifc_id_asgn_gen: if (i < log2(CHANNELS)) generate
      txmsg_ifc_id(i) <= txmsg_ifc_id_i(i);
   end generate;
   zero_asgn_gen: if (i >= log2(CHANNELS)) generate
      txmsg_ifc_id(i) <= '0';
   end generate;
end generate;

message_tx_u: message_tx
   generic map(
      DATA_PATHS  => DATA_PATHS
   )
   port map(
      -- Common Input
      CLK   => CLK,
      RESET => RESET,

      -- Flow Controller Interface
      IFC_ID   => txmsg_ifc_id,
      XON      => txmsg_xon,
      XOFF     => txmsg_xoff,
      BUSY     => txmsg_busy,

      -- Aurora UFC TX Interface
      UFC_TX_DATA    => UFC_TX_DATA,
      UFC_TX_REQ_N   => UFC_TX_REQ_N,
      UFC_TX_MS      => UFC_TX_MS,
      UFC_TX_ACK_N   => UFC_TX_ACK_N
   );


end behavioral;

