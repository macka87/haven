-- rep_2port_sdr_top_ent.vhd: The entity that encapsulates rep_2port component
--     (which contains repeater), over- and underflow counters, enable
--     registers for enabling functionality of the repeater. These components
--     are available through MI32 interface.                
--
-- Copyright (C) 2009 CESNET
-- Author(s): Michal Kajan <kajan@liberouter.org>
--            Jiri Novotnak <xnovot87@stud.fit.vutbr.cz>
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
use IEEE.std_logic_arith.all;

entity rep_2port_sdr_top is
   generic (
      -- size of ASFIFO
      FIFO_SIZE  : integer := 512
   );
   port (
      -- common signals
      RESET      :  in std_logic;

      -- XGMII Receiver 0 input
      RX_CLK0    :  in std_logic;
      RX_D0      :  in std_logic_vector(63 downto 0);
      RX_C0      :  in std_logic_vector(7 downto 0);

      -- XGMII Receiver 1 input
      RX_CLK1    :  in std_logic;
      RX_D1      :  in std_logic_vector(63 downto 0);
      RX_C1      :  in std_logic_vector(7 downto 0);

      -- XGMII Transmitter 0 output
      TX_CLK0    :  in std_logic;
      TX_D0      : out std_logic_vector(63 downto 0);
      TX_C0      : out std_logic_vector(7 downto 0);

      -- XGMII Transmitter 1 output
      TX_CLK1    :  in std_logic;
      TX_D1      : out std_logic_vector(63 downto 0);
      TX_C1      : out std_logic_vector(7 downto 0);

      -- XGMII Receiver 0 output to IBUF
      IBUF0_CLK  : out std_logic;
      IBUF0_DATA : out std_logic_vector(63 downto 0);
      IBUF0_CMD  : out std_logic_vector(7 downto 0);

      -- XGMII Receiver 1 output to IBUF
      IBUF1_CLK  : out std_logic;
      IBUF1_DATA : out std_logic_vector(63 downto 0);
      IBUF1_CMD  : out std_logic_vector(7 downto 0);

      -- MI32 interface
      MI32_DWR   :  in std_logic_vector(31 downto 0);
      MI32_ADDR  :  in std_logic_vector(31 downto 0);  
      MI32_RD    :  in std_logic;
      MI32_WR    :  in std_logic;
      MI32_BE    :  in std_logic_vector(3 downto 0);
      MI32_DRD   : out std_logic_vector(31 downto 0);
      MI32_ARDY  : out std_logic;
      MI32_DRDY  : out std_logic;

      -- MI32 clock
      MI32_CLK   :  in std_logic
   );

end entity rep_2port_sdr_top;
