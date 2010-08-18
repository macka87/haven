-- ib_tx8.vhd : Internal bus TX interface
-- Copyright (C) 2008 CESNET
-- Author(s): Stepan Friedl <friedl@liberouter.org>
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
-- TODO list :
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
library UNISIM;
use UNISIM.Vcomponents.ALL;
use work.math_pack.all;

entity ib_tx8 is
   generic (
      DATA_WIDTH      : natural := 64;   -- 8, 15, 32 or 64
      TXCLK_PHASE_REV : boolean := false -- Reverse TXCLK (TX_PAD_8) phase
      ); 
   port (
      CLK          : in  std_logic;
      RESET        : in  std_logic;
      -- RX interface
      TX_DATA      : in  std_logic_vector(DATA_WIDTH-1  downto 0);
      TX_SOP_N     : in  std_logic;
      TX_EOP_N     : in  std_logic;
      TX_SRC_RDY_N : in  std_logic;
      TX_DST_RDY_N : out std_logic;
      -- TX interface
      TX_PAD       : out std_logic_vector(7 downto 0);
      TX_RDY_N_PAD : in  std_logic
   );
end entity ib_tx8;

-- ----------------------------------------------------------------------------
--                              Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of ib_tx8 is

component FDDRRSE
generic (
   INIT : bit := '0'
);
port(
   Q  : out std_logic;
   D0 : in  std_logic;
   D1 : in  std_logic;
   C0 : in  std_logic;
   C1 : in  std_logic;
   CE : in  std_logic;
   S  : in  std_logic;
   R  : in  std_logic 
);
end component;

signal pwr_rem         : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal clk_inv         : std_logic;
signal reset_n         : std_logic;
signal reg_tx_rdy_n    : std_logic := '0';
signal tx_data8        : std_logic_vector(7 downto 0);
signal tx_sop8         : std_logic;
signal tx_eop8         : std_logic;
signal tx_src_rdy8     : std_logic;
signal tx_dst_rdy8     : std_logic;   
signal reg_tx_data8    : std_logic_vector(7 downto 0);
signal reg_tx_sop8     : std_logic;
signal reg_tx_eop8     : std_logic;
signal reg_tx_src_rdy8 : std_logic;
signal tx_data_fall    : std_logic_vector(3 downto 0);
signal tx_sof_fall     : std_logic;
signal tx_eof_fall     : std_logic;
signal tx_src_rdy_fall : std_logic;
signal tx_data_rise    : std_logic_vector(3 downto 0);
signal tx_sof_rise     : std_logic;
signal tx_eof_rise     : std_logic;
signal tx_src_rdy_rise : std_logic;

signal regiob_tx_data    : std_logic_vector(3 downto 0);
signal regiob_tx_sop     : std_logic;
signal regiob_tx_eop     : std_logic;
signal regiob_tx_src_rdy : std_logic;
signal transf_dst_rdy_n  : std_logic := '0';
signal even              : std_logic := '0';
signal tx_even           : std_logic := '0';
signal tx_sync           : std_logic := '0';
signal tx_sync_rise      : std_logic := '0';
signal tx_packet         : std_logic := '0';
signal tx_valid_n        : std_logic;
signal reg_tx_sync       : std_logic := '0';

attribute INIT : string;
attribute INIT of regiob_tx_sop : signal is "S";
attribute INIT of regiob_tx_eop : signal is "S";
attribute INIT of regiob_tx_src_rdy : signal is "S";

begin

pwr_rem <= (others => '1');
   
TXRDY_IN_REG: process(CLK)
begin
   if CLK' event and CLK = '1' then -- Falling edge
      reg_tx_rdy_n <= TX_RDY_N_PAD;
   end if;
end process;
   

TRANSFORM64_TO_8: entity work.FL_TRANSFORMER_DOWN_8
generic map (
   RX_DATA_WIDTH  => DATA_WIDTH
)
port map (
   CLK            => CLK,
   RESET          => RESET,
   -- RX interface
   RX_DATA        => TX_DATA,
   RX_REM         => pwr_rem,
   RX_SOF_N       => TX_SOP_N,
   RX_EOF_N       => TX_EOP_N,
   RX_SOP_N       => TX_SOP_N,
   RX_EOP_N       => TX_EOP_N,
   RX_SRC_RDY_N   => TX_SRC_RDY_N,
   RX_DST_RDY_N   => TX_DST_RDY_N,
   -- TX interface
   TX_DATA        => tx_data8,
   TX_SOF_N       => tx_sop8,
   TX_EOF_N       => tx_eop8,
   TX_SOP_N       => open,
   TX_EOP_N       => open,
   TX_SRC_RDY_N   => tx_src_rdy8,
   TX_DST_RDY_N   => tx_dst_rdy8
);

tx_dst_rdy8 <= transf_dst_rdy_n;

TX_REGS8: process(RESET, CLK)
begin
   if RESET = '1' then
      reg_tx_sop8     <= '1';
      reg_tx_eop8     <= '1';
      reg_tx_src_rdy8 <= '1';
   elsif CLK' event and CLK = '1' then
      if transf_dst_rdy_n = '0' then
         reg_tx_data8    <= tx_data8;
         reg_tx_sop8     <= tx_sop8;
         reg_tx_eop8     <= tx_eop8;
         reg_tx_src_rdy8 <= tx_src_rdy8;
      end if;
   end if;
end process;

ODD_EVEN_PROC: process(RESET, CLK)
begin
   if RESET = '1' then
      even <= '1';
   elsif CLK'event and CLK='1' then
--       if (tx_sop8 = '0') and (tx_src_rdy8 = '0') then
--          transf_dst_rdy_n <= '1';
--       elsif (tx_dst_rdy8 = '0') then
         transf_dst_rdy_n <= (not even) or reg_tx_rdy_n;
         even             <= not even;
--       end if;
   end if;
end process;

tx_sync      <= '1' when (reg_tx_sop8 = '0') and (reg_tx_src_rdy8 = '0') else '0';
tx_sync_rise <= '1' when (tx_sync = '1') and (reg_tx_sync = '0') else '0';
tx_valid_n   <= reg_tx_src_rdy8 or (not (tx_packet or tx_sync)); 

IOB_REGS_PROC: process(RESET, CLK)
begin
   if RESET = '1' then 
      regiob_tx_sop     <= '1';
      regiob_tx_eop     <= '1';
      regiob_tx_src_rdy <= '1';
      reg_tx_sync       <= '0';
      tx_even           <= '0';
      tx_packet         <= '0';       
   elsif CLK'event and CLK='1' then
      reg_tx_sync <= tx_sync;
      -- SRC_RDY before SOF bug workaround
      if (tx_sync = '1') then 
         tx_packet <= '1';
      elsif ((reg_tx_eop8 = '0') and (reg_tx_src_rdy8 = '0')) and (tx_even = '1') then
         tx_packet <= '0';
      end if;
      if (tx_sync_rise = '1') then
         tx_even <= '1';
      else
         tx_even <= not tx_even;
      end if;
      if (tx_even = '0') or (tx_sync_rise = '1') then
         regiob_tx_data    <= reg_tx_data8(3 downto 0);
         regiob_tx_sop     <= reg_tx_sop8; 
         regiob_tx_eop     <= '1';
         regiob_tx_src_rdy <= tx_valid_n;
      elsif (tx_even = '1') then
         regiob_tx_data    <= reg_tx_data8(7 downto 4);
         regiob_tx_sop     <= '1';
         regiob_tx_eop     <= reg_tx_eop8;
         regiob_tx_src_rdy <= tx_valid_n;
      end if;
   end if;
end process;

TX_PAD(3 downto 0) <= regiob_tx_data after 1 ns;
TX_PAD(4) <= regiob_tx_sop after 1 ns;
TX_PAD(5) <= regiob_tx_eop  after 1 ns;
TX_PAD(6) <= regiob_tx_src_rdy  after 1 ns;

clk_inv <= not CLK;

GEN_TXCLK: if (not TXCLK_PHASE_REV) generate
   TXCLK_DDR: FDDRRSE
   port map (
      Q  => TX_PAD(7),
      D0 => '1', -- 
      D1 => '0',
      C0 => CLK,
      C1 => clk_inv,
      CE => '1',
      R  => '0',
      S  => '0'
   );
end generate;

GEN_TXCLK_PHREV: if (TXCLK_PHASE_REV) generate
   TXCLK_DDR: FDDRRSE
   port map (
      Q  => TX_PAD(7),
      D0 => '0', -- 
      D1 => '1',
      C0 => CLK,
      C1 => clk_inv,
      CE => '1',
      R  => '0',
      S  => '0'
   );
end generate;


-- OLD section ---------------------------------------------------------------

-- TX_REGS_RISE: process(CLK)
-- begin
--    if CLK'event and CLK = '1' then -- Rising edge
--       tx_data_rise    <= reg_tx_data8(3 downto 0) after 1 ns;
--       tx_sof_rise     <= reg_tx_sop8 after 1 ns;
--       tx_eof_rise     <= reg_tx_eop8 after 1 ns;
--       tx_src_rdy_rise <= reg_tx_src_rdy8 after 1 ns;
--    end if;
-- end process;

-- TX_REGS_FALL: process(CLK)
-- begin
--    if CLK' event and CLK = '0' then -- Falling edge
--       tx_data_fall    <= reg_tx_data8(7 downto 4) after 1 ns;
--       tx_sof_fall     <= '1' after 1 ns;
--       tx_eof_fall     <= '1' after 1 ns;
--       tx_src_rdy_fall <= '1' after 1 ns;
--    end if;
-- end process;


-- --- DDR cells instantion ---

-- GEN_TXD_DDR_REGS: for i in 0 to 3 generate
--    TXD_DDR: FDDRRSE
--    generic map ( INIT => '1')
--    port map (
--       Q  => TX_PAD(i),
--       D0 => tx_data_rise(i),
--       D1 => tx_data_fall(i),
--       C0 => CLK,
--       C1 => clk_inv,
--       CE => '1',
--       R  => '0',
--       S  => '0'
--    );
-- end generate;
--     
-- TXSOF_DDR: FDDRRSE
-- generic map ( INIT => '1')
-- port map (
--    Q  => TX_PAD(4),
--    D0 => tx_sof_rise,
--    D1 => tx_sof_fall,
--    C0 => CLK,
--    C1 => clk_inv,
--    CE => '1',
--    R  => '0',
--    S  => '0'
-- );
--    
-- TXEOF_DDR: FDDRRSE
-- generic map ( INIT => '1')
-- port map (
--    Q  => TX_PAD(5),
--    D0 => tx_eof_rise,
--    D1 => tx_eof_fall,
--    C0 => CLK,
--    C1 => clk_inv,
--    CE => '1',
--    R  => '0',
--    S  => '0'
-- );
--     
-- TXSRCRDY_DDR: FDDRRSE
-- generic map ( INIT => '1')
-- port map (
--    Q  => TX_PAD(6),
--    D0 => tx_src_rdy_rise,
--    D1 => tx_src_rdy_fall,
--    C0 => CLK,
--    C1 => clk_inv,
--    CE => '1',
--    R  => '0',
--    S  => '0'
-- );

end architecture behavioral;
