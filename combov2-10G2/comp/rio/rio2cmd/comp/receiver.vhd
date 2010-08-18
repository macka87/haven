
-- receiver.vhd: Receiver for command protocol via RocketIO 
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
use work.rio_codes.ALL;
use work.commands.ALL;

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity receiver is
   port (
      -- Common Input
      USRCLK2  : in std_logic;
      CMDCLK   : in std_logic;
      RESET    : in std_logic;
      
      -- Command protocol interface
      DO       : out std_logic_vector(31 downto 0);
      DO_CMD   : out std_logic_vector(3 downto 0);
      DO_DV    : out std_logic;
      FULL     : in std_logic;

      -- Status inteface
      STATUS   : out std_logic_vector(7 downto 0);
      STATUS_DV: out std_logic;

      -- RocketIO controller interface
      RXDATA         : in std_logic_vector(31 downto 0);
      RXCHARISK      : in std_logic_vector(3 downto 0);
      RXREALIGN      : in std_logic;
      RXCOMMADET     : in std_logic;
      RXCHECKINGCRC  : in std_logic;
      RXCRCERR       : in std_logic
   );
end receiver;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of receiver is

component align_comma_32
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
END component align_comma_32;

component asfifo 
   generic(
      -- Data Width
      DATA_WIDTH  : integer;
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS : integer;
      -- Distributed Ram Type(capacity) only 16, 32, 64 bits
      DISTMEM_TYPE : integer := 16;

      -- Width of status information of fifo fullness
      -- Note: 2**STATUS_WIDTH MUST BE!! less or equal
      --       than ITEMS
      STATUS_WIDTH : integer
   );
   port(
      RESET    : in  std_logic;

      -- Write interface
      CLK_WR   : in  std_logic;
      DI       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      WR       : in  std_logic;
      FULL     : out std_logic;
      STATUS      : out std_logic_vector(STATUS_WIDTH-1 downto 0);

      -- Read interface
      CLK_RD   : in  std_logic;
      DO       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      RD       : in  std_logic;
      EMPTY    : out std_logic
   );
end component asfifo;

component cmd_decoder is
   port (
      -- Input: RocketIO characters
      DI       : in std_logic_vector(7 downto 0);
      DIISK    : in std_logic;

      -- Output: Command protocol
      DO       : out std_logic_vector(7 downto 0);
      DO_CMD   : out std_logic
   );
end component;

component recv_fsm is
   port (
      RESET       : in std_logic;
      CLK         : in std_logic;
      
      -- Input
      SOC_OCC     : in std_logic;
      TERM_OCC    : in std_logic;
      EMPTY       : in std_logic;
      CRC_VALID   : in std_logic;
      FULL        : in std_logic;

      -- Output
      STATUS_DV   : out std_logic;
      DO_DV       : out std_logic;
      FIFO_RD     : out std_logic;
      CRC_WE      : out std_logic
   );
end component;

-- Data signals
signal data_from_rio    : std_logic_vector(31 downto 0);
signal k_from_rio       : std_logic_vector(3 downto 0);
signal data_to_fifo     : std_logic_vector(35 downto 0);
signal data_from_fifo   : std_logic_vector(35 downto 0);
signal do_i             : std_logic_vector(31 downto 0);
signal do_cmd_i         : std_logic_vector(3 downto 0);

-- Control signals
signal rx_algn_sync     : std_logic;
signal rxcharissop1     : std_logic;
signal rxcharissop3     : std_logic;
signal fifo_wr          : std_logic;
signal fifo_full        : std_logic;
signal fifo_rd          : std_logic;
signal fifo_rd_fsm      : std_logic;
signal fifo_empty       : std_logic;
signal soc_occ          : std_logic;
signal eop_occ          : std_logic;
signal term_occ         : std_logic;
signal crc_we           : std_logic;

-- Registers
signal reg_buffer_ov : std_logic;
signal reg_crcvalid  : std_logic;
signal reg_crcvalid_we  : std_logic;
signal reg_crcerr    : std_logic;

begin

-- This component aligns SOP comma byte to MSB position
SOP_ALIGN_32_U: align_comma_32
port map(
   ALIGNED_DATA      => data_from_rio,
   ALIGNED_RXISK     => k_from_rio,
   SYNC              => rx_algn_sync,
   USRCLK2           => USRCLK2,
   RXRESET           => RESET,
   RXDATA            => RXDATA,
   RXISK             => RXCHARISK,
   RXCOMMADET        => RXCOMMADET,
   RXREALIGN         => RXREALIGN,
   RXCHARISCOMMA3    => rxcharissop3,
   RXCHARISCOMMA1    => rxcharissop1
  );

  rxcharissop3 <= '1' when (RXCHARISK(3) = '1' and RXDATA(31 downto 24) = K_SOP) else
                  '0';
  rxcharissop1 <= '1' when (RXCHARISK(1) = '1' and RXDATA(15 downto 8) = K_SOP) else
                  '0';


-- ASFIFO and depending logic
asfifo_u: asfifo 
   generic map(
      -- Data Width
      DATA_WIDTH     => 36,
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS          => 16,
      -- Distributed Ram Type(capacity) only 16, 32, 64 bits
      DISTMEM_TYPE   => 16,

      -- Width of status information of fifo fullness
      -- Note: 2**STATUS_WIDTH MUST BE!! less or equal
      --       than ITEMS
      STATUS_WIDTH   => 1
   )
   port map(
      RESET    => reset,

      -- Write interface
      CLK_WR   => USRCLK2,
      DI       => data_to_fifo,
      WR       => fifo_wr,
      FULL     => fifo_full,
      STATUS   => open,

      -- Read interface
      CLK_RD   => CMDCLK,
      DO       => data_from_fifo,
      RD       => fifo_rd,
      EMPTY    => fifo_empty
   );
   
   data_to_fifo <= k_from_rio & data_from_rio;
   fifo_wr <= '1' when (rx_algn_sync = '1') and (data_to_fifo /= X"ABC50BC50") else
              '0';
   fifo_rd <= not FULL and fifo_rd_fsm;


-- EOP and CRC logic
   soc_occ <= '1' when (((data_from_fifo(31 downto 24) = K_SOC) and (data_from_fifo(35) = '1')) or
                        ((data_from_fifo(15 downto 8) = K_SOC) and (data_from_fifo(33) = '1'))) else
              '0';
              
   term_occ <= '1' when ((data_from_fifo(31 downto 24) = K_TERM) and (data_from_fifo(35) = '1')) or
                        ((data_from_fifo(23 downto 16) = K_TERM) and (data_from_fifo(34) = '1')) or
                        ((data_from_fifo(15 downto 8) = K_TERM) and (data_from_fifo(33) = '1')) or
                        ((data_from_fifo(7 downto 0) = K_TERM) and (data_from_fifo(32) = '1')) else
               '0';
              
   eop_occ <= '1' when ((data_from_fifo(31 downto 24) = K_EOP) and (data_from_fifo(35) = '1')) or
                       ((data_from_fifo(23 downto 16) = K_EOP) and (data_from_fifo(34) = '1')) or
                       ((data_from_fifo(15 downto 8) = K_EOP) and (data_from_fifo(33) = '1')) or
                       ((data_from_fifo(7 downto 0) = K_EOP) and (data_from_fifo(32) = '1')) else
              '0';

-- Command protocol decoders
cmd_decoder_u0: cmd_decoder
   port map(
      -- Input: RocketIO characters
      DI       => data_from_fifo(7 downto 0),
      DIISK    => data_from_fifo(32),

      -- Output: Command protocol
      DO       => do_i(7 downto 0),
      DO_CMD   => do_cmd_i(0)
   );
              
cmd_decoder_u1: cmd_decoder
   port map(
      -- Input: RocketIO characters
      DI       => data_from_fifo(15 downto 8),
      DIISK    => data_from_fifo(33),

      -- Output: Command protocol
      DO       => do_i(15 downto 8),
      DO_CMD   => do_cmd_i(1)
   );
              
cmd_decoder_u2: cmd_decoder
   port map(
      -- Input: RocketIO characters
      DI       => data_from_fifo(23 downto 16),
      DIISK    => data_from_fifo(34),

      -- Output: Command protocol
      DO       => do_i(23 downto 16),
      DO_CMD   => do_cmd_i(2)
   );
              
cmd_decoder_u3: cmd_decoder
   port map(
      -- Input: RocketIO characters
      DI       => data_from_fifo(31 downto 24),
      DIISK    => data_from_fifo(35),

      -- Output: Command protocol
      DO       => do_i(31 downto 24),
      DO_CMD   => do_cmd_i(3)
   );
              
-- Reorder the bytes according to the Command protocol specification
DO <= do_i(7 downto 0) & do_i(15 downto 8) & do_i(23 downto 16) & do_i(31 downto 24);
DO_CMD <= do_cmd_i(0) & do_cmd_i(1) & do_cmd_i(2) & do_cmd_i(3);

-- Recieve FSM
recv_fsm_u: recv_fsm
   port map(
      RESET       => RESET,
      CLK         => CMDCLK,
      
      -- Input
      SOC_OCC     => soc_occ,
      TERM_OCC    => term_occ,
      EMPTY       => fifo_empty,
      CRC_VALID   => reg_crcvalid,
      FULL        => FULL,

      -- Output
      STATUS_DV   => STATUS_DV,
      DO_DV       => DO_DV,
      FIFO_RD     => fifo_rd_fsm,
      CRC_WE      => crc_we
   );

-- Status logic
process(RESET, CMDCLK)
begin
   if (RESET = '1') then
      reg_buffer_ov <= '0';
   elsif (CMDCLK'event AND CMDCLK = '1') then
      if (eop_occ = '1') then
         reg_buffer_ov <= '0';
      elsif (fifo_full = '1' and fifo_wr = '1') then
         reg_buffer_ov <= '1';
      end if;
   end if;
end process;

reg_crcvalid_we <= RXCHECKINGCRC and crc_we;
process(RESET, CMDCLK)
begin
   if (RESET = '1') then
      reg_crcvalid <= '0';
   elsif (CMDCLK'event AND CMDCLK = '1') then
      if (eop_occ = '1') then
         reg_crcvalid <= '0';
      elsif (reg_crcvalid_we = '1') then
         reg_crcvalid <= '1';
      end if;
   end if;
end process;

process(RESET, CMDCLK)
begin
   if (RESET = '1') then
      reg_crcerr <= '0';
   elsif (CMDCLK'event AND CMDCLK = '1') then
      if (eop_occ = '1') then
         reg_crcerr <= '0';
      elsif (reg_crcvalid = '1') then
         reg_crcerr <= RXCRCERR;
      end if;
   end if;
end process;

-- Status interface mapping
STATUS(0) <= reg_crcerr;
STATUS(1) <= reg_buffer_ov;
STATUS(7 downto 2) <= "000000"; -- reserved
end behavioral;

