-- top_level.vhd: Control Bus Root toplevel for synthesis
-- Copyright (C) 2007 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
use work.cb_pkg.all; -- Control Bus package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cb_root_top is
   port(
      -- Common interface
      CB_CLK       : in  std_logic;
      CB_RESET     : in  std_logic;
      
      -- RX, TX queues interface
      QADDR        : in  std_logic_vector(9 downto 0);--Address
      QWR          : in  std_logic;                       -- Write Request
      QRD          : in  std_logic;                       -- Read Request
      QDWR         : in  std_logic_vector(63 downto 0);   -- Data Write
      QBE          : in  std_logic_vector(7 downto 0);    -- Byte Enable
      QDRD         : out std_logic_vector(63 downto 0);   -- Data Read
      QDRDY        : out std_logic;                       -- Data Ready

      -- Control/Status interface
      CADDR        : in  std_logic_vector(7 downto 0);    -- Address
      CWR          : in  std_logic;                       -- Write Request
      CRD          : in  std_logic;                       -- Read Request
      CDWR         : in  std_logic_vector(31 downto 0);   -- Data Write
      CBE          : in  std_logic_vector(3 downto 0);    -- Byte Enable
      CDRD         : out std_logic_vector(31 downto 0);   -- Data Read
      CDRDY        : out std_logic;                       -- Data Ready

      -- Control Bus interfaces
      CB           : inout t_control_bus
   );
end entity cb_root_top;

ARCHITECTURE synth OF cb_root_top IS
   begin
   uut: entity work.CB_ROOT
   generic map(
      QADDR_WIDTH    => 10
   )
   port map(
      CB_CLK         => CB_CLK,
      CB_RESET       => CB_RESET,
      
      -- RX, TX queues interface
      QADDR          => QADDR,
      QWR            => QWR,
      QRD            => QRD,
      QDWR           => QDWR,
      QBE            => QBE,
      QDRD           => QDRD,
      QDRDY          => QDRDY,

      -- Control/Status interface
      CADDR          => CADDR,
      CWR            => CWR,
      CRD            => CRD,
      CDWR           => CDWR,
      CBE            => CBE,
      CDRD           => CDRD,
      CDRDY          => CDRDY,

      -- Control Bus interfaces
      CB             => CB
   );
end;
