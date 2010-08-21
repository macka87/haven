
-- tx_chnl_ctrl.vhd: TX Channel Controller 
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
use work.aurvc_pkg.all; 

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity tx_chnl_ctrl is
   generic (
      DATA_PATHS           : integer;     -- Number of bytes of data port
      CHANNELS             : integer      -- Number of channels
   );
   port (
      -- Common Interface
      CLK               : in std_logic;
      RESET             : in std_logic;

      -- Data Multiplexers Control
      TX_IFC_ID         : out std_logic_vector(max(log2(CHANNELS)-1, 0) downto 0);
      DATA_ID_MX        : out std_logic;

      -- TX Buffer Control Interface
      FIFO_READ         : out std_logic;
      FIFO_DV           : in std_logic;
      FIFO_EOP          : in std_logic;
      FIFO_EMPTY        : in std_logic;
      BYTE_QUOTA_MET    : in std_logic;
      BYTE_QUOTA_RST    : out std_logic;
      FIFO_EMPTY_VECTOR : in std_logic_vector(CHANNELS-1 downto 0);

      -- Aurora LocalLink TX Interface
      TX_SRC_RDY_N      : out std_logic;
      TX_SOF_N          : out std_logic;
      TX_EOF_N          : out std_logic;
      TX_DST_RDY_N      : in std_logic;

      -- Aurora UFC RX Interface
      UFC_RX_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      UFC_RX_SRC_RDY_N  : in std_logic;
      UFC_RX_SOF_N      : in std_logic;
      UFC_RX_EOF_N      : in std_logic;
      UFC_RX_REM        : in std_logic_vector(log2(DATA_PATHS)-1 downto 0)
   );
end tx_chnl_ctrl;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of tx_chnl_ctrl is

component GEN_DEMUX is
   generic(
      DATA_WIDTH  : integer;
      DEMUX_WIDTH : integer   -- demultiplexer width (number of outputs)
   );
   port(
      DATA_IN     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      SEL         : in  std_logic_vector(log2(DEMUX_WIDTH)-1 downto 0);
      DATA_OUT    : out std_logic_vector(DATA_WIDTH*DEMUX_WIDTH-1 downto 0)
   );
end component GEN_DEMUX;

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

component message_rx is
   generic (
      DATA_PATHS  : integer      -- Number of bytes of data port
   );
   port (
      -- Common Input
      CLK   : in std_logic;
      RESET : in std_logic;

      -- Aurora UFC RX Interface
      UFC_RX_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      UFC_RX_SRC_RDY_N  : in std_logic;
      UFC_RX_SOF_N      : in std_logic;
      UFC_RX_EOF_N      : in std_logic;
      UFC_RX_REM        : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);

      -- Decoded Output
      IFC_ID            : out std_logic_vector(7 downto 0);
      XON               : out std_logic;
      XOFF              : out std_logic
   );
end component;

component tx_chnl_ctrl_fsm is
   port (
      -- Common Input
      CLK      : in std_logic;
      RESET    : in std_logic;

      -- Input
      CHANNEL_VALID                 : in std_logic;
      FIFO_DV                       : in std_logic;
      FIFO_EOP                      : in std_logic;
      FIFO_EMPTY                    : in std_logic;
      AUR_TX_DST_RDY_N              : in std_logic;
      CHANNEL_BYTE_QUOTA_MET        : in std_logic;

      -- Output
      CHANNEL_DATA_ID_MX            : out std_logic;
      AUR_TX_SRC_RDY_N              : out std_logic;
      AUR_TX_SOF_N                  : out std_logic;
      AUR_TX_EOF_N                  : out std_logic;
      FIFO_READ                     : out std_logic;
      REG_CHNL_MASK_RST_ENABLE      : out std_logic
   );
end component;

-- reg_chnl_mask signals
signal reg_chnl_mask : std_logic_vector(CHANNELS-1 downto 0);
signal reg_chnl_mask_rst   : std_logic_vector(CHANNELS-1 downto 0);
signal reg_chnl_mask_set   : std_logic_vector(CHANNELS-1 downto 0);
signal reg_chnl_mask_rst_enable  : std_logic;
signal reg_chnl_mask_set_enable  : std_logic;

-- reg_chnl_status signals
signal reg_chnl_status     : std_logic_vector(CHANNELS-1 downto 0);
signal reg_chnl_status_rst : std_logic_vector(CHANNELS-1 downto 0);
signal reg_chnl_status_set : std_logic_vector(CHANNELS-1 downto 0);
signal chnl_status_mx      : std_logic_vector(7 downto 0);

-- Arbiter signals
signal chnl_rdy            : std_logic_vector(CHANNELS-1 downto 0);
signal active_chnl_onehot  : std_logic_vector(CHANNELS-1 downto 0);
signal active_chnl_binary  : std_logic_vector(max(log2(CHANNELS)-1, 0) downto 0);
signal reg_active_chnl_binary : std_logic_vector(max(log2(CHANNELS)-1, 0) downto 0);
signal channel_valid       : std_logic;
   
signal data_transmition_active_n : std_logic;
signal xon  : std_logic;
signal xoff : std_logic;

begin

-- -------------------------------------------------------------
-- Flow Control Message Decoder
message_rx_u: message_rx
   generic map(
      DATA_PATHS  => DATA_PATHS
   )
   port map(
      -- Common Input
      CLK   => CLK,
      RESET => RESET,

      -- Aurora UFC RX Interface
      UFC_RX_DATA       => UFC_RX_DATA,
      UFC_RX_SRC_RDY_N  => UFC_RX_SRC_RDY_N,
      UFC_RX_SOF_N      => UFC_RX_SOF_N,
      UFC_RX_EOF_N      => UFC_RX_EOF_N,
      UFC_RX_REM        => UFC_RX_REM,

      -- Decoded Output
      IFC_ID            => chnl_status_mx,
      XON               => xon,
      XOFF              => xoff
   );

-- -------------------------------------------------------------
-- reg_chnl_status
no_demux_gen: if (CHANNELS = 1) generate
   reg_chnl_status_set(0) <= xon;
   reg_chnl_status_rst(0) <= xoff;
end generate;
demux_gen: if (CHANNELS > 1) generate
   chnl_xon_status_demux_u: GEN_DEMUX
      generic map(
         DATA_WIDTH  => 1,
         DEMUX_WIDTH => CHANNELS
      )
      port map(
         DATA_IN(0)  => xon,
         SEL         => chnl_status_mx(log2(CHANNELS)-1 downto 0),
         DATA_OUT    => reg_chnl_status_set
      );
   
   chnl_xoff_status_demux_u: GEN_DEMUX
      generic map(
         DATA_WIDTH  => 1,
         DEMUX_WIDTH => CHANNELS
      )
      port map(
         DATA_IN(0)  => xoff,
         SEL         => chnl_status_mx(log2(CHANNELS)-1 downto 0),
         DATA_OUT    => reg_chnl_status_rst
      );
end generate;
reg_chnl_status_gen: for i in 0 to CHANNELS-1 generate
   process (CLK, RESET)
   begin
      if (RESET = '1') then
         reg_chnl_status(i) <= C_XON;
      elsif (CLK'event and CLK = '1') then
         if (reg_chnl_status_rst(i) = '1') then
            reg_chnl_status(i) <= C_XOFF;
         elsif (reg_chnl_status_set(i) = '1') then
            reg_chnl_status(i) <= C_XON;
         end if;
      end if;
   end process;
end generate;

-- -------------------------------------------------------------
-- chnl_rdy
chnl_rdy_gen: for i in 0 to CHANNELS-1 generate
   chnl_rdy(i) <= '1' when (reg_chnl_status(i) = C_XON) and (FIFO_EMPTY_VECTOR(i) = '0') else
                  '0';
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

-- -------------------------------------------------------------
-- reg_chnl_mask
reg_chnl_mask_set_gen: for i in 0 to CHANNELS-1 generate
   reg_chnl_mask_set(i) <= chnl_rdy(i) and reg_chnl_mask_set_enable;
end generate;

reg_chnl_mask_rst_gen: for i in 0 to CHANNELS-1 generate
   reg_chnl_mask_rst(i) <= (active_chnl_onehot(i) and reg_chnl_mask_rst_enable)
                           or not chnl_rdy(i);
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
-- TX Buffer Controller
tx_chnl_ctrl_fsm_u: tx_chnl_ctrl_fsm
   port map(
      -- Common Input
      CLK      => CLK,
      RESET    => RESET,

      -- Input
      CHANNEL_VALID                 => channel_valid,
      FIFO_DV                       => FIFO_DV,
      FIFO_EOP                      => FIFO_EOP,
      FIFO_EMPTY                    => FIFO_EMPTY,
      AUR_TX_DST_RDY_N              => TX_DST_RDY_N,
      CHANNEL_BYTE_QUOTA_MET        => BYTE_QUOTA_MET,

      -- Output
      CHANNEL_DATA_ID_MX            => DATA_ID_MX,
      AUR_TX_SRC_RDY_N              => data_transmition_active_n,
      AUR_TX_SOF_N                  => TX_SOF_N,
      AUR_TX_EOF_N                  => TX_EOF_N,
      FIFO_READ                     => FIFO_READ,
      REG_CHNL_MASK_RST_ENABLE      => reg_chnl_mask_rst_enable
   );

   -- Pipeline register to improve net timing
   -- TX_IFC_ID can be one-clock-delayed because the chnl_ctrl_fsm is in 'wait_for_chnl' state 
   -- and TX_IFC_ID is needed not until the 'send_ifc_id' state.
   process (CLK, RESET)
   begin
      if (RESET = '1') then
         reg_active_chnl_binary <= (others => '0');
      elsif (CLK'event and CLK = '1') then
         reg_active_chnl_binary <= active_chnl_binary;
      end if;
   end process;

TX_IFC_ID <= reg_active_chnl_binary;
TX_SRC_RDY_N <= data_transmition_active_n;
BYTE_QUOTA_RST <= reg_chnl_mask_set_enable or reg_chnl_mask_rst_enable;

end behavioral;



