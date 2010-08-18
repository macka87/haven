--
-- uh_top_hfe_debug.vhd: Unified Header FIFO, architecture for HFE debugging
-- Copyright (C) 2003 CESNET, Liberouter project
-- Author(s): Filip Hofer fil@liberouter.org
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
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;
library unisim;
use unisim.all;

architecture behavioral of UH_TOP is
-- ---------------------- Component instantion --------------------------
component RAMB16_S18_S36 is
   -- pragma translate_off
   generic (
      WRITE_MODE_A : string := "READ_FIRST" ;
      WRITE_MODE_B : string := "WRITE_FIRST" ;
      );
   -- pragma translate_on
   port (
      -- First port
      DIA     : in std_logic_vector (15 downto 0);
      DIPA    : in std_logic_vector (1  downto 0);
      ADDRA   : in std_logic_vector (9  downto 0);
      ENA     : in std_logic;
      WEA     : in std_logic;
      SSRA    : in std_logic;
      CLKA    : in std_logic;
      DOA     : out std_logic_vector (15 downto 0);
      DOPA    : out std_logic_vector ( 1 downto 0);
      -- Second port
      DIB     : in std_logic_vector (31 downto 0);
      DIPB    : in std_logic_vector (3 downto 0);
      ADDRB   : in std_logic_vector (8 downto 0);
      ENB     : in std_logic;
      WEB     : in std_logic;
      SSRB    : in std_logic;
      CLKB    : in std_logic;
      DOB     : out std_logic_vector (31 downto 0);
      DOPB    : out std_logic_vector (3 downto 0)
   );
end component;

-- ----------------------- Signal assignement ---------------------------
-- LBCONN_MEM signals
signal addr          : std_logic_vector(11 downto 0); -- Address to BlockRAM
signal rw            : std_logic;                    -- Write/Read#
signal en            : std_logic;                    -- enable
signal data_to_lb    : std_logic_vector(15 downto 0);
signal data_from_lb  : std_logic_vector(15 downto 0);

-- Empty signals - warning elimination
signal empty_sig_in  : std_logic_vector(400 downto 0);
signal empty_sig_out : std_logic;

-- Unified header
signal uh_we         : std_logic_vector( 3 downto 0);  -- Writing to UH_FIFO
signal uh_sel        : std_logic_vector( 3 downto 0);  -- Select UH_FIFO
signal uh0_data      : std_logic_vector(15 downto 0);  -- Output data
signal uh1_data      : std_logic_vector(15 downto 0);  -- Output data
signal uh2_data      : std_logic_vector(15 downto 0);  -- Output data
signal uh3_data      : std_logic_vector(15 downto 0);  -- Output data

-- signal ready         : std_logic;     -- Ready to local bus

begin

   -- Local bus communication component. Here is neccessary specify base
   -- address and width of address buss.
   LB_CONNECT: entity work.LBCONN_MEM
   generic map(
      ADDR_WIDTH => 12,      -- address bus width
      BASE       => 16#200#  -- base address 0x200
   )
   port map(
      DATA_OUT => data_from_lb,
      DATA_IN  => data_to_lb,
      ADDR     => addr,
      EN       => en,
      RW       => rw,
      RDY      => '1',
      RESET    => reset,
      LBCLK    => LBCLK,
      LBFRAME  => lbframe,
      LBAS     => lbas,
      LBRW     => lbrw,
      LBLAST   => lblast,
      LBAD     => lbad,
      LBHOLDA  => lbholda,
      LBRDY    => lbrdy
   );

   -- UH FIFO (0) - Unified header fifo for interface 0
   UH_0: RAMB16_S18_S36
   port map (
      -- This port is connected to PCI bus
      DIA     => data_from_lb,         -- input data from
      DIPA    => (1 downto 0 => '0'),  -- input parity port
      ADDRA   => addr(9 downto 0),     -- addres bus
      ENA     => uh_sel(0),   -- enable signal
      WEA     => rw,          -- write enable signal
      SSRA    => '0',         -- set/reset signal
      CLKA    => LBCLK,       -- clock signal
      DOA     => uh0_data,    -- 32 bits data out bus
      DOPA    => open,        -- 4 bits parity data out bus
      -- This port is connected Lookup processor
      DIB     => (31 downto 0 => '0'), -- 32 bits data in bus
      DIPB    => ( 3 downto 0 => '0'), -- 4 bits parity data in bus
      ADDRB   => UH1_LUP_ADDR,-- 9 bits address bus
      ENB     => '1',         -- enable signal
      WEB     => '0',         -- write enable signal
      SSRB    => '0',         -- set/reset signal
      CLKB    => LUP_CLK,     -- clock signal
      DOB     => UH1_LUP_DATA,-- 32 bits data out bus
      DOPB    => open         -- 4 bits parity data out bus
   );

   -- UH FIFO (1) - Unified header fifo for interface 1
   UH_1: RAMB16_S18_S36
   port map (
      -- This port is connected to PCI bus
      DIA     => data_from_lb,         -- input data from
      DIPA    => (1 downto 0 => '0'),  -- input parity port
      ADDRA   => addr(9 downto 0),     -- addres bus
      ENA     => uh_sel(1),   -- enable signal
      WEA     => rw,        -- write enable signal
      SSRA    => '0',         -- set/reset signal
      CLKA    => LBCLK,       -- clock signal
      DOA     => uh1_data,    -- 32 bits data out bus
      DOPA    => open,        -- 4 bits parity data out bus
      -- This port is connected Lookup processor
      DIB     => (31 downto 0 => '0'), -- 32 bits data in bus
      DIPB    => ( 3 downto 0 => '0'), -- 4 bits parity data in bus
      ADDRB   => UH2_LUP_ADDR,-- 9 bits address bus
      ENB     => '1',         -- enable signal
      WEB     => '0',         -- write enable signal
      SSRB    => '0',         -- set/reset signal
      CLKB    => LUP_CLK,     -- clock signal
      DOB     => UH2_LUP_DATA,-- 32 bits data out bus
      DOPB    => open         -- 4 bits parity data out bus
   );

   -- UH FIFO (2) - Unified header fifo for interface 2
   UH_2: RAMB16_S18_S36
   port map (
      -- This port is connected to PCI bus
      DIA     => data_from_lb,         -- input data from
      DIPA    => (1 downto 0 => '0'),  -- input parity port
      ADDRA   => addr(9 downto 0),     -- addres bus
      ENA     => uh_sel(2),   -- enable signal
      WEA     => rw,        -- write enable signal
      SSRA    => '0',         -- set/reset signal
      CLKA    => LBCLK,       -- clock signal
      DOA     => uh2_data,    -- 32 bits data out bus
      DOPA    => open,        -- 4 bits parity data out bus
      -- This port is connected Lookup processor
      DIB     => (31 downto 0 => '0'), -- 32 bits data in bus
      DIPB    => ( 3 downto 0 => '0'), -- 4 bits parity data in bus
      ADDRB   => UH3_LUP_ADDR,-- 9 bits address bus
      ENB     => '1',         -- enable signal
      WEB     => '0',         -- write enable signal
      SSRB    => '0',         -- set/reset signal
      CLKB    => LUP_CLK,     -- clock signal
      DOB     => UH3_LUP_DATA,-- 32 bits data out bus
      DOPB    => open         -- 4 bits parity data out bus
   );

   -- UH FIFO (3) - Unified header fifo for interface 3
   UH_3: RAMB16_S18_S36
   port map (
      -- This port is connected to PCI bus
      DIA     => data_from_lb,         -- input data from
      DIPA    => (1 downto 0 => '0'),  -- input parity port
      ADDRA   => addr(9 downto 0),     -- addres bus
      ENA     => uh_sel(3),   -- enable signal
      WEA     => rw,        -- write enable signal
      SSRA    => '0',         -- set/reset signal
      CLKA    => LBCLK,       -- clock signal
      DOA     => uh3_data,    -- 32 bits data out bus
      DOPA    => open,        -- 4 bits parity data out bus
      -- This port is connected Lookup processor
      DIB     => (31 downto 0 => '0'), -- 32 bits data in bus
      DIPB    => ( 3 downto 0 => '0'), -- 4 bits parity data in bus
      ADDRB   => UH4_LUP_ADDR,-- 9 bits address bus
      ENB     => '1',         -- enable signal
      WEB     => '0',         -- write enable signal
      SSRB    => '0',         -- set/reset signal
      CLKB    => LUP_CLK,     -- clock signal
      DOB     => UH4_LUP_DATA,-- 32 bits data out bus
      DOPB    => open         -- 4 bits parity data out bus
   );


   -- ----------------------- Control logic -----------------------------
   -- BlockRAM select signal
   uh_sel(0)   <= '1' when addr(11 downto 10) = "00" else '0';
   uh_sel(1)   <= '1' when addr(11 downto 10) = "01" else '0';
   uh_sel(2)   <= '1' when addr(11 downto 10) = "10" else '0';
   uh_sel(3)   <= '1' when addr(11 downto 10) = "11" else '0';

   -- ------------------ Write signal generating ------------------------
   uh_we  <=  uh_sel and (3 downto 0 => rw);

   -- --------------------- Output data select --------------------------
   data_to_lb <= uh0_data when uh_sel(0)='1' else
                 uh1_data when uh_sel(1)='1' else
                 uh2_data when uh_sel(2)='1' else
                 uh3_data;

   -- Rdy signal delayed
   --  ready <= en when LBCLK'event and LBCLK='1';



   -- Unconnected port in this debug design. All input and output signals
   -- are connected to empty_sig. We can eliminate a lot of warnings this
   -- way.

   -- Input sinals
   empty_sig_in(15 downto    0)<= UH1_HFE_DOUT;
   empty_sig_in(21 downto   16)<= UH1_HFE_ADDR;
   empty_sig_in(22)            <= UH1_HFE_REQ;
   empty_sig_in(23)            <= UH1_HFE_WEN;
   empty_sig_in(115 downto 100)<= UH2_HFE_DOUT;
   empty_sig_in(121 downto 116)<= UH2_HFE_ADDR;
   empty_sig_in(122)           <= UH2_HFE_REQ;
   empty_sig_in(123)           <= UH2_HFE_WEN;
   empty_sig_in(215 downto 200)<= UH3_HFE_DOUT;
   empty_sig_in(221 downto 216)<= UH3_HFE_ADDR;
   empty_sig_in(222)           <= UH3_HFE_REQ;
   empty_sig_in(223)           <= UH3_HFE_WEN;
   empty_sig_in(315 downto 300)<= UH4_HFE_DOUT;
   empty_sig_in(321 downto 316)<= UH4_HFE_ADDR;
   empty_sig_in(322)           <= UH4_HFE_REQ;
   empty_sig_in(323)           <= UH4_HFE_WEN;

   -- Output signals
   UH1_HFE_RDY   <= empty_sig_out;
   UH2_HFE_RDY   <= empty_sig_out;
   UH3_HFE_RDY   <= empty_sig_out;
   UH4_HFE_RDY   <= empty_sig_out;

end behavioral;
