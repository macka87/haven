--
-- pcs_mx_out: Conversion of data path from GMII to MX (SFP and ser/des)
-- Copyright (C) 2004 CESNET
-- Author(s): Jiri Novotny <novotny@liberouter.org>
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
-- TODO: More tests (first set is done)
--
--
library IEEE;
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity pcs_mx_out is
   port(
      RESET	: in std_logic;
      TX_CLK	: in std_logic;
      TX_D	: in std_logic_vector (7 downto 0);
      TX_EN	: in std_logic;
      TX_ERR	: in std_logic;
      
      DATA_8   : out std_logic_vector (7 downto 0);
      DATA_8_K : out std_logic;
      DATA_10	: out std_logic_vector (9 downto 0)
   );
end pcs_mx_out;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of pcs_mx_out is
   type t_state is (IDLE_K_S, IDLE_D_S, IDLE1_D_S, SPD_S, DATA_S, EPD_S, CER_S);
   signal present_state, next_state : t_state;

   signal data_0 : std_logic_vector (7 downto 0);
   signal data_1 : std_logic_vector (7 downto 0);
   signal data_del : std_logic_vector (7 downto 0);
   signal data_to_enc : std_logic_vector (7 downto 0);

   signal k_d : std_logic;
   signal disp_out : std_logic;

   signal del2 : std_logic;
   signal tx_en_0 : std_logic;
   signal tx_en_del : std_logic;
   signal even : std_logic;

   constant IDLE_K : std_logic_vector (7 downto 0) := X"BC";
   constant IDLE_D : std_logic_vector (7 downto 0) := X"50";
   constant IDLE1_D : std_logic_vector (7 downto 0) := X"C5";
   constant SPD : std_logic_vector (7 downto 0) := X"FB";
   constant EPD : std_logic_vector (7 downto 0) := X"FD";
   constant CER : std_logic_vector (7 downto 0) := X"F7";


begin

DATA_8_K <= k_d;
DATA_8   <= data_to_enc;

ENC_U0 : entity work.dual_enc_8b10b
port map(
      CLK0      => TX_CLK,
      RESET0    => RESET,
      DIN0	=> data_to_enc,
      KIN0	=> k_d,
      DISP_IN0	=> '0',
      FORCE_DISP0 => '0',
      DOUT0	=> DATA_10,
      DISP_OUT0	=> disp_out,
      KERR0	=> open,

      CLK1      => '1',
      RESET1    => '1',
      DIN1	=> X"00",
      KIN1	=> '1',
      DISP_IN1	=> '0',
      FORCE_DISP1 => '0',
      DOUT1	=> open,
      DISP_OUT1	=> open,
      KERR1	=> open

    );

-- -------------------------------------------------------
process(RESET, TX_CLK)
begin
   if (RESET = '1') then
      data_0 <= (others => '0');
      tx_en_0 <= '0';
    elsif (TX_CLK'event AND TX_CLK = '1') then
      data_0 <=  TX_D;
      tx_en_0 <= TX_EN;
   end if;
end process;

process(RESET, TX_CLK)
begin
   if (RESET = '1') then
      data_1 <= (others => '0');
    elsif (TX_CLK'event AND TX_CLK = '1') then
      data_1 <= data_0;
   end if;
end process;

process(RESET, TX_CLK)
begin
   if (RESET = '1') then
      del2 <= '0';
    elsif (TX_CLK'event AND TX_CLK = '1') then
      if (present_state = IDLE_K_S) then  -- add IDLE1_K_S later on
         del2 <= TX_EN;
      else
         del2 <= del2;
      end if;
   end if;
end process;

data_del <= data_0 when del2 = '0' else data_1;
tx_en_del <= TX_EN when del2 = '0' else tx_en_0;

-- -------------------------------------------------------
even_odd_logic : process(RESET, TX_CLK)
begin
   if (RESET = '1') then
      even <= '0';
   elsif (TX_CLK'event AND TX_CLK = '1') then
      if present_state = SPD_S then
         even <= '0';
      else
         even <= not even;
      end if;
   end if;
end process even_odd_logic;

-- -------------------------------------------------------
sync_logic : process(RESET, TX_CLK)
begin
   if (RESET = '1') then
      present_state <= IDLE_K_S;
   elsif (TX_CLK'event AND TX_CLK = '1') then
      present_state <= next_state;
   end if;
end process sync_logic;

-- -------------------------------------------------------


next_state_logic : process (present_state, tx_en_del, even, disp_out)

begin
   case (present_state) is
   -- -----------------------------
   when IDLE_K_S =>
      next_state <= IDLE_D_S;
      if (disp_out = '1') then
         next_state <= IDLE1_D_S;
      end if;
   -- -----------------------------
   when IDLE_D_S =>
      next_state <= IDLE_K_S;
      if (TX_EN = '1') then
         next_state <= SPD_S;
      end if;
   -- -----------------------------
   when IDLE1_D_S =>
      next_state <= IDLE_K_S;
      if (TX_EN = '1') then
         next_state <= SPD_S;
      end if;
   -- -----------------------------
   when SPD_S =>
      next_state <= DATA_S;
   -- -----------------------------
   when DATA_S =>
      next_state <= DATA_S;
      if (tx_en_del = '0') then
         next_state <= EPD_S;
      end if;
   -- -----------------------------
   when EPD_S =>
      next_state <= CER_S;
   -- -----------------------------
   when CER_S =>
      next_state <= IDLE_K_S;
      if (even = '1') then
         next_state <= CER_S;
      end if;
   -- -----------------------------
    when others =>
      next_state <= IDLE_K_S;
   end case;
end process next_state_logic;

-- -------------------------------------------------------
output_logic : process(present_state, data_del)
begin
   case (present_state) is
   -- -----------------------------
   when IDLE_K_S =>
      data_to_enc <= IDLE_K;
      k_d <= '1';
   -- -----------------------------
   when IDLE_D_S =>
      data_to_enc <= IDLE_D;
      k_d <= '0';
   -- -----------------------------
  when IDLE1_D_S =>
      data_to_enc <= IDLE1_D;
      k_d <= '0';
   -- -----------------------------
   when SPD_S =>
      data_to_enc <= SPD;
      k_d <= '1';
   -- -----------------------------
   when DATA_S =>
      data_to_enc <= data_del;
      k_d <= '0';
   -- -----------------------------
   when EPD_S =>
      data_to_enc <= EPD;
      k_d <= '1';
   -- -----------------------------
   when CER_S =>
      data_to_enc <= CER;
      k_d <= '1';
   -- -----------------------------
   when others =>
   end case;
end process output_logic;

-- -------------------------------------------------------

end architecture behavioral;




