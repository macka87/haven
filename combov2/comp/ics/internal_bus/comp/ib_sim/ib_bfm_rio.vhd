-- ib_bfm_rio.vhd: Simulation component for internal bus
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.math_pack.all;
use work.ib_pkg.all;
use work.ib_sim_oper.all;
use work.ib_bfm_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_BFM_RIO is
   generic (
       MEMORY_BASE_ADDR : std_logic_vector(63 downto 0) := X"FFFFFFFF00000000"; -- Memory Base ADDR
       MEMORY_SIZE      : integer := 1024; -- Defaul 1024 Bytes
       MEMORY_DELAY     : integer := 10    -- Delay before sending completition
       );
   port(
      -- Common interface
      IB_RESET          : in  std_logic;
      IB_CLK            : in  std_logic;
      FCLK              : in  std_logic;

      -- Internal Bus Interface
      TXN2              : out std_logic;
      TXP2              : out std_logic;
      RXP2              : in std_logic;
      RXN2              : in std_logic;
      TXN3              : out std_logic;
      TXP3              : out std_logic;
      RXP3              : in std_logic;
      RXN3              : in std_logic
      );
end entity IB_BFM_RIO;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_BFM_RIO_ARCH of IB_BFM_RIO is

   signal ibus          : t_internal_bus64; 
   signal usrclk        : std_logic := '0';  
   signal usrclk2       : std_logic := '0';  

begin

   IB_BFM_I : entity work.IB_BFM
   GENERIC MAP (
       MEMORY_BASE_ADDR => MEMORY_BASE_ADDR,
       MEMORY_SIZE      => MEMORY_SIZE,
       MEMORY_DELAY     => MEMORY_DELAY
       )
   PORT MAP(
      CLK          => IB_CLK,
      -- Internal Bus Interface
      IB           => ibus
   );

   RIO_DCLK_DIV: process(usrclk)
   begin
      if usrclk'event and usrclk = '0' then
         usrclk2 <= not usrclk2;
      end if;
   end process; 

   usrclk <= FCLK after 1 ns;

   IB_AURORA: entity work.aurfc 
   generic map (
      LANES           => 2,
      DATA_PATHS      => 8,
      RX_IS_HEADER    => false,
      RX_IS_FOOTER    => false,
      TX_FIFO_ITEMS   => 512,      -- TX_FIFO_ITEMS = 2^n
      RX_FIFO_ITEMS   => 512       -- RX_FIFO_ITEMS = 2^n
   )
   port map (
      -- Common Input
      RESET        => IB_RESET,
      REFCLK       => FCLK,
      USRCLK       => usrclk,
      USRCLK2      => usrclk2,
      CMDCLK       => IB_CLK,
      -- FrameLink TX
      TX_D         => ibus.down.data,
      TX_REM       => "111",
      TX_SRC_RDY_N => ibus.down.src_rdy_n,
      TX_SOF_N     => ibus.down.sop_n,
      TX_SOP_N     => ibus.down.sop_n,
      TX_EOF_N     => ibus.down.eop_n,
      TX_EOP_N     => ibus.down.eop_n,
      TX_DST_RDY_N => ibus.down.dst_rdy_n,
      -- FrameLink RX 
      RX_D         => ibus.up.data,     
      RX_REM       => open, 
      RX_SRC_RDY_N => ibus.up.src_rdy_n,
      RX_SOF_N     => ibus.up.sop_n,    
      RX_SOP_N     => open,
      RX_EOF_N     => ibus.up.eop_n,    
      RX_EOP_N     => open,
      RX_DST_RDY_N => ibus.up.dst_rdy_n,
      -- Upper Layer
      HARD_ERROR   => open,
      SOFT_ERROR   => open,
      FRAME_ERROR  => open,
      -- Status Interface
      TX_STATUS    => open,
      RX_STATUS    => open,
      -- MGT Interface
      RXN(0)         => RXN2,
      RXN(1)         => RXN3,
      RXP(0)         => RXP2,
      RXP(1)         => RXP3,
      TXN(0)         => TXN2,
      TXN(1)         => TXN3,
      TXP(0)         => TXP2,
      TXP(1)         => TXP3
   ); 

end architecture IB_BFM_RIO_ARCH;

