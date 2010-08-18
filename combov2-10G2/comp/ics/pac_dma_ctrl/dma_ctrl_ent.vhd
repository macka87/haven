-- dma_ctrl_ent.vhd: dma control block entity
-- Copyright (C) 2009 CESNET
-- Author(s): Petr Kastovsky <kastovsky@liberouter.org>
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
-- KEYWORDS : TODO, DEBUG
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity pac_dma_ctrl is
   generic (
      IFCS              : integer := 4
   );
   port(
      -- Common signals
      CLK      : in std_logic;  
      RESET    : in std_logic;

      -- pulse with one clk tick wide stride
      INTERRUPT   : out std_logic_vector(2*IFCS-1 downto 0);

      -- Data interface
      -- Write interface
      IB_WR_ADDR     : in  std_logic_vector(31 downto 0);
      IB_WR_DATA     : in  std_logic_vector(63 downto 0);
      IB_WR_BE       : in  std_logic_vector(7 downto 0);
      IB_WR_REQ      : in  std_logic;
      IB_WR_RDY      : out std_logic;
      -- Read interface
      IB_RD_ADDR     : in  std_logic_vector(31 downto 0);
      IB_RD_DATA     : out std_logic_vector(63 downto 0);
      IB_RD_BE       : in  std_logic_vector(7 downto 0);
      IB_RD_REQ      : in  std_logic;
      IB_RD_ARDY     : out std_logic;
      IB_RD_SRC_RDY  : out std_logic;

      -- BM interface
      IB_BM_GADDR    : out std_logic_vector(63 downto 0); -- Global Address 
      IB_BM_LADDR    : out std_logic_vector(31 downto 0); -- Local Address
      IB_BM_LENGTH   : out std_logic_vector(11 downto 0); -- Length
      IB_BM_TAG      : out std_logic_vector(15 downto 0); -- Operation TAG
      IB_BM_TTYPE    : out std_logic_vector(1  downto 0); -- Type of transaction
      IB_BM_REQ      : out std_logic;                     -- Request
      IB_BM_ACK      : in  std_logic;                     -- Ack
      IB_BM_OP_TAG   : in  std_logic_vector(15 downto 0); -- Operation TAG
      IB_BM_OP_DONE  : in  std_logic;                     -- Acknowledge
                 
      -- SW memory interface
      MI_SW_DWR      : in  std_logic_vector(31 downto 0);
      MI_SW_ADDR     : in  std_logic_vector(31 downto 0);
      MI_SW_RD       : in  std_logic;
      MI_SW_WR       : in  std_logic;
      MI_SW_BE       : in  std_logic_vector(3  downto 0);
      MI_SW_DRD      : out std_logic_vector(31 downto 0);
      MI_SW_ARDY     : out std_logic;
      MI_SW_DRDY     : out std_logic;

      -- Receive buffer interface
      RX_NEWLEN       : in  std_logic_vector(IFCS*16-1 downto 0);
      RX_NEWLEN_DV    : in  std_logic_vector(IFCS-1 downto 0);
      RX_NEWLEN_RDY   : out std_logic_vector(IFCS-1 downto 0);
      RX_RELLEN       : out std_logic_vector(IFCS*16-1 downto 0);
      RX_RELLEN_DV    : out std_logic_vector(IFCS-1 downto 0);

      -- Transmit buffer interface
      TX_NEWLEN       : out std_logic_vector(IFCS*16-1 downto 0);
      TX_NEWLEN_DV    : out std_logic_vector(IFCS-1 downto 0);
      TX_NEWLEN_RDY   : in  std_logic_vector(IFCS-1 downto 0);
      TX_RELLEN       : in  std_logic_vector(IFCS*16-1 downto 0);
      TX_RELLEN_DV    : in  std_logic_vector(IFCS-1 downto 0)

   );
end entity pac_dma_ctrl;

