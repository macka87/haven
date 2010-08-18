--
-- pcs_mx_in: Conversion of data path from MX (SFP and ser/des) to GMII
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
-- TODO: more tests, use of dual port dec
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity pcs_mx_in is
   port(
      -- Input signals
      RESET	: in std_logic;
      RX_CLK	: in std_logic;
      DATA_10	: in std_logic_vector (9 downto 0);
      RXLOST	: in std_logic;

      -- Output signals
      RX_D	   : out std_logic_vector (7 downto 0);
      RX_DV	   : out std_logic;
      RX_ERR	: out std_logic;
      LSTAT    : out std_logic
   );
end pcs_mx_in;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of pcs_mx_in is

   signal k_d : std_logic;
   signal err : std_logic;
   signal err_dec : std_logic;
   signal dout : std_logic_vector (7 downto 0);
   signal k_d_data : std_logic_vector (8 downto 0);
   signal k_d_data_del : std_logic_vector (8 downto 0);

   constant spd : std_logic_vector (8 downto 0) := '1' & X"fb";
   constant epd : std_logic_vector (8 downto 0) := '1' & X"fd";

   -- RXLOST correction constants and signals
   constant CNTPPMS_SIZE   : integer := 17;
   constant CNTPPS_SIZE    : integer := 10;

   constant PPMS_INIT_VAL  : integer := 0;
   constant PPS_INIT_VAL   : integer := 0;

   signal cnt_ppms      : std_logic_vector(CNTPPMS_SIZE-1 downto 0);
   signal cnt_ppms_ce   : std_logic;
   signal cnt_ppms_ld   : std_logic;
   signal cnt_pps       : std_logic_vector(CNTPPS_SIZE-1 downto 0);
   signal cnt_pps_ce    : std_logic;
   signal cnt_pps_ld    : std_logic;
   signal ppms          : std_logic;
   signal pps           : std_logic;

   signal fsm_init      : std_logic;
   signal fsm_cntce     : std_logic;
   signal rxlost_int    : std_logic;
   signal ones          : std_logic_vector(31 downto 0);

begin

-- --------------------------------------------------------
--               RXLOST signal correction
-- --------------------------------------------------------

ones <= (others => '1');

-- cnt_ppms counter
cnt_ppms_ce <= fsm_init or fsm_cntce;
cnt_ppms_ld <= fsm_init;
process(RESET, RX_CLK)
begin
   if (RESET = '1') then
      cnt_ppms <= (others => '0');
   elsif (RX_CLK'event AND RX_CLK = '1') then
      if (cnt_ppms_ce = '1') then
         if (cnt_ppms_ld = '1') then
            cnt_ppms <= conv_std_logic_vector(PPMS_INIT_VAL, CNTPPMS_SIZE);
         else
            cnt_ppms <= cnt_ppms + 1;
         end if;
      end if;
   end if;
end process;


-- ppms comparator
ppms <= '1' when (cnt_ppms = ones(CNTPPMS_SIZE-1 downto 0)) else
        '0';

-- cnt_pps counter
cnt_pps_ce <= fsm_init or (ppms and fsm_cntce);
cnt_pps_ld <= fsm_init;
process(RESET, RX_CLK)
begin
   if (RESET = '1') then
      cnt_pps <= (others => '0');
   elsif (RX_CLK'event AND RX_CLK = '1') then
      if (cnt_pps_ce = '1') then
         if (cnt_pps_ld = '1') then
            cnt_pps <= conv_std_logic_vector(PPS_INIT_VAL, CNTPPS_SIZE);
         else
            cnt_pps <= cnt_pps + 1;
         end if;
      end if;
   end if;
end process;

-- pps comparator
pps <= '1' when ((cnt_pps = ones(CNTPPS_SIZE-1 downto 0)) and (fsm_cntce = '1')) else
       '0';

-- FSM instantion
FSM_U : entity work.pcs_mx_in_fsm
port map(
   -- Common signals
   RESET    => RESET,
   CLK      => RX_CLK,

   -- Input signals
   RXLOST   => RXLOST,
   PPS      => pps,

   -- Output signals
   FSM_INIT => fsm_init,
   FSM_CNTCE=> fsm_cntce
);

rxlost_int  <= fsm_cntce;
LSTAT       <= fsm_cntce;
-- --------------------------------------------------------
--                   Decoder 8/10
-- --------------------------------------------------------
-- it is ugly, but we can live with ... for some time
DEC_U0 : entity work.dual_dec_8b10b
port map(
      CLK0      => RX_CLK,
      RESET0    => RESET,
      DIN0      => DATA_10,
      DOUT0     => dout,
      K0        => k_d,
      INVALID0  => err_dec,

      CLK1      => '1',
      RESET1    => '1',
      DIN1      => "00" & X"00",
      DOUT1     => open,
      K1        => open,
      INVALID1  => open
   );

err <= '0' when err_dec = '0' and rxlost_int = '0' else '1';

RX_D <= k_d_data_del (7 downto 0) ;
k_d_data <= k_d & dout;

process(RESET, RX_CLK)
begin
   if (RESET = '1') then
      k_d_data_del <= (others => '0');
   elsif (RX_CLK'event AND RX_CLK = '1') then
      if k_d_data = spd then
         k_d_data_del <= '0' & X"55"; -- Insert preamble symbol instead of SPD
      else
         k_d_data_del <= k_d_data;
      end if;
   end if;
end process;


process(RESET, RX_CLK)
begin
   if (RESET = '1') then
      RX_DV  <= '0';
      RX_ERR <= '0';
   elsif (RX_CLK'event AND RX_CLK = '1') then
      if err = '1' then
         RX_DV <= '0';
      elsif k_d_data = epd then
         RX_DV <= '0';
      elsif k_d_data = spd then
         RX_DV <= '1';
      end if;
      RX_ERR <= err;
   end if;
end process;

end architecture behavioral;
