--
-- ope_tb.vhd: Testbench of RIO2CMD component
-- Copyright (C) 2006 CESNET
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
-- TODO:
-- 
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

use work.math_pack.all; 
use work.aurvc_pkg.all; 
use work.AURORA.AURORA_LANE_WIDTH; 

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant DATA_PATHS  : integer   := 2;
   constant TX_CHANNELS : integer   := 4;
   constant RX_CHANNELS : integer   := 4;

   constant buffers_param : t_aurvc_buffers_param := (
      (
         (channel_size => 1023, byte_quota => 64),
         (channel_size => 1023, byte_quota => 64),
         (channel_size => 1023, byte_quota => 64),
         (channel_size => 1023, byte_quota => 64),
         others => (channel_size => 1023, byte_quota => 64)
      ),
      (
         (channel_size => 1023, xon_limit => "011", xoff_limit => "110"),
         (channel_size => 1023, xon_limit => "011", xoff_limit => "110"),
         (channel_size => 1023, xon_limit => "011", xoff_limit => "110"),
         (channel_size => 1023, xon_limit => "011", xoff_limit => "110"),
         others => (channel_size => 1023, xon_limit => "011", xoff_limit => "110")
      )
   );

   -- clock signals
   signal refclk     : std_logic;
   signal usrclk     : std_logic;
   signal usrclk2    : std_logic;
   signal flclk      : std_logic;
   signal reset      : std_logic;

   -- FrameLink TX Interface
   signal tx_d             : std_logic_vector((TX_CHANNELS*(DATA_PATHS*8))-1 downto 0);
   signal tx_rem           : std_logic_vector((TX_CHANNELS*log2(DATA_PATHS))-1 downto 0);
   signal tx_src_rdy_n     : std_logic_vector(TX_CHANNELS-1 downto 0);
   signal tx_sof_n         : std_logic_vector(TX_CHANNELS-1 downto 0);
   signal tx_sop_n         : std_logic_vector(TX_CHANNELS-1 downto 0);
   signal tx_eof_n         : std_logic_vector(TX_CHANNELS-1 downto 0);
   signal tx_eop_n         : std_logic_vector(TX_CHANNELS-1 downto 0);
   signal tx_dst_rdy_n     : std_logic_vector(TX_CHANNELS-1 downto 0);

   -- FrameLink RX Interface
   signal rx_d             : std_logic_vector((RX_CHANNELS*(DATA_PATHS*8))-1 downto 0);
   signal rx_rem           : std_logic_vector((RX_CHANNELS*log2(DATA_PATHS))-1 downto 0);
   signal rx_src_rdy_n     : std_logic_vector(RX_CHANNELS-1 downto 0);
   signal rx_sof_n         : std_logic_vector(RX_CHANNELS-1 downto 0);
   signal rx_sop_n         : std_logic_vector(RX_CHANNELS-1 downto 0);
   signal rx_eof_n         : std_logic_vector(RX_CHANNELS-1 downto 0);
   signal rx_eop_n         : std_logic_vector(RX_CHANNELS-1 downto 0);
   signal rx_dst_rdy_n     : std_logic_vector(RX_CHANNELS-1 downto 0);

   -- RIO signals
   signal txn        : std_logic_vector((DATA_PATHS/AURORA_LANE_WIDTH)-1 downto 0);
   signal txp        : std_logic_vector((DATA_PATHS/AURORA_LANE_WIDTH)-1 downto 0);
   signal rxp        : std_logic_vector((DATA_PATHS/AURORA_LANE_WIDTH)-1 downto 0);
   signal rxn        : std_logic_vector((DATA_PATHS/AURORA_LANE_WIDTH)-1 downto 0);

   constant refclkper   : time := 8 ns;
   constant usrclkper   : time := 8 ns;
   constant flclkper   : time := 10 ns;

   constant data_file1  : string := "../data/aurvc_data1.txt";
   constant data_file2  : string := "../data/aurvc_data2.txt";


-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------

begin
uut: entity work.aurvc
   generic map(
      DATA_PATHS           => DATA_PATHS,
      TX_CHANNELS          => TX_CHANNELS,
      RX_CHANNELS          => RX_CHANNELS,
      BUFFERS_PARAM        => buffers_param,
      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      LOOPBACK             => "10"
   )
   port map(
      -- Common Input
      RESET          => reset,
      REFCLK         => refclk,
      USRCLK         => usrclk,
      USRCLK2        => usrclk2,
      FLCLK          => flclk,
      
      -- FrameLink TX Interface
      TX_D             => tx_d,
      TX_REM           => tx_rem,
      TX_SRC_RDY_N     => tx_src_rdy_n,
      TX_SOF_N         => tx_sof_n,
      TX_SOP_N         => tx_sop_n,
      TX_EOF_N         => tx_eof_n,
      TX_EOP_N         => tx_eop_n,
      TX_DST_RDY_N     => tx_dst_rdy_n,

      -- FrameLink RX Interface
      RX_D             => rx_d,
      RX_REM           => rx_rem,
      RX_SRC_RDY_N     => rx_src_rdy_n,
      RX_SOF_N         => rx_sof_n,
      RX_SOP_N         => rx_sop_n,
      RX_EOF_N         => rx_eof_n,
      RX_EOP_N         => rx_eop_n,
      RX_DST_RDY_N     => rx_dst_rdy_n,

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     => open,
      SOFT_ERROR     => open,
      FRAME_ERROR    => open,

      -- MGT Interface
      RXN            => rxn,
      RXP            => rxp,
      TXN            => txn,
      TXP            => txp
   );

-- ----------------------------------------------------
-- refclk clock generator
refclkgen : process
begin
   refclk <= '1';
   wait for refclkper/2;
   refclk <= '0';
   wait for refclkper/2;
end process;

-- flclk clock generator
flclkgen : process
begin
   flclk <= '1';
   wait for flclkper/2;
   flclk <= '0';
   wait for flclkper/2;
end process;

-- usrclk clock generator
usrclkgen : process
begin
   usrclk <= '1';
   wait for usrclkper/2;
   usrclk <= '0';
   wait for usrclkper/2;
end process;

-- usrclk2 clock generator
usrclk2gen : process (reset, usrclk)
begin
   if (reset'event and reset = '1') then
      usrclk2 <= '0';
   elsif (usrclk'event and usrclk = '0') then
      usrclk2 <= not usrclk2;
   end if;
end process;

-- rx_dst_rdy_n generator
process
begin
   rx_dst_rdy_n     <= (others => '1');
   wait for 80 us;
   rx_dst_rdy_n     <= (0 => '0', others => '1');
   wait;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------

tb : process

procedure process_file(data_file : string; id : integer) is

   file infile: text;
   variable l : line;
   variable d : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   variable good : boolean;
   
begin
      -- process cmd_file
      wait for 20*flclkper;
      file_open(infile,data_file,READ_MODE);
      tx_rem(((id+1)*log2(DATA_PATHS))-1 downto id*log2(DATA_PATHS)) <= (others => '1');
      tx_src_rdy_n(id) <= '0';
      tx_sof_n(id)     <= '0';
      tx_sop_n(id)     <= '0';
      readline(infile,l);
      hread(l,d,good);
      tx_d(((id+1)*DATA_PATHS*8)-1 downto id*DATA_PATHS*8)     <= d;
      wait for flclkper;
      while not (endfile(infile)) loop
         if (tx_dst_rdy_n(id) = '1') then
            wait until tx_dst_rdy_n(id) = '0';
         end if;
         readline(infile,l);
         hread(l,d,good);
         tx_d(((id+1)*DATA_PATHS*8)-1 downto id*DATA_PATHS*8)  <= d;
         tx_sof_n(id)                                          <= '1';
         tx_sop_n(id)                                          <= '1';
         wait for flclkper;
      end loop;
      if (tx_dst_rdy_n(id) = '1') then
         wait until tx_dst_rdy_n(id) = '0';
      end if;
      tx_d(((id+1)*DATA_PATHS*8)-1 downto id*DATA_PATHS*8)             <= X"abba";
      tx_rem(((id+1)*log2(DATA_PATHS))-1 downto id*log2(DATA_PATHS))   <= "1";
      tx_eof_n(id)         <= '0';
      tx_eop_n(id)         <= '0';
      wait for flclkper;
      tx_src_rdy_n(id)     <= '1';
      tx_eof_n(id)         <= '1';
      tx_eop_n(id)         <= '1';
      file_close(infile);
end process_file; 

-- ----------------------------------------------------------------
--                        Testbench Body
-- ----------------------------------------------------------------

begin
tx_d             <= (others => '0');
tx_rem           <= (others => '0');
tx_src_rdy_n     <= (others => '1');
tx_sof_n         <= (others => '1');
tx_sop_n         <= (others => '1');
tx_eof_n         <= (others => '1');
tx_eop_n         <= (others => '1');

reset <= '1';
wait for 10 us;
reset <= '0';


for i in 0 to 80 loop
   process_file(data_file1,0);
   process_file(data_file1,1);
end loop;

wait;


end process;

end architecture behavioral;
