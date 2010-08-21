--
-- enc_dec_tb.vhd: Testbench to compare 8b/10b encoders and decoders
-- Copyright (C) 2004 CESNET
-- Author(s): Petr Mikusek <mikusek@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

component enc_dec
   port (
      CLK         : in  std_logic;
      RESET       : in  std_logic;

      -- Enc0
      E0_DIN      : in  std_logic_vector(7 downto 0);
      E0_K        : in  std_logic;
      E0_DOUT     : out std_logic_vector(9 downto 0);
      E0_RDISP    : out std_logic;

      -- Enc1
      E1_DIN      : in  std_logic_vector(7 downto 0);
      E1_K        : in  std_logic;
      E1_DOUT     : out std_logic_vector(9 downto 0);
      E1_RDISP    : out std_logic;

      -- Dec0
      D0_DOUT     : out std_logic_vector(7 downto 0);
      D0_K        : out std_logic;
      D0_INVALID  : out std_logic;

      -- Dec1
      D1_DOUT     : out std_logic_vector(7 downto 0);
      D1_K        : out std_logic;
      D1_INVALID  : out std_logic
   );
end component;

   -- Common signals
   signal clk125     : std_logic;
   signal reset      : std_logic;

   -- Encoders input data
   signal enc_din    : std_logic_vector(7 downto 0);
   signal enc_k      : std_logic;

   -- Enc0
   signal e0_dout    : std_logic_vector(9 downto 0);
   signal e0_rdisp   : std_logic;

   -- Enc1
   signal e1_dout    : std_logic_vector(9 downto 0);
   signal e1_rdisp   : std_logic;

   -- Dec0
   signal d0_dout    : std_logic_vector(7 downto 0);
   signal d0_k       : std_logic;
   signal d0_invalid : std_logic;

   -- Dec1
   signal d1_dout    : std_logic_vector(7 downto 0);
   signal d1_k       : std_logic;
   signal d1_invalid : std_logic;

   constant C_CLKPER  : time := 8 ns; -- 125 MHz clock

begin

   UUT: enc_dec
   port map (
      CLK        => clk125,
      RESET      => reset,

      -- Enc0
      E0_DIN     => enc_din,
      E0_K       => enc_k,
      E0_DOUT    => e0_dout,
      E0_RDISP   => e0_rdisp,

      -- Enc1
      E1_DIN     => enc_din,
      E1_K       => enc_k,
      E1_DOUT    => e1_dout,
      E1_RDISP   => e1_rdisp,

      -- Dec0
      D0_DOUT    => d0_dout,
      D0_K       => d0_k,
      D0_INVALID => d0_invalid,

      -- Dec1
      D1_DOUT    => d1_dout,
      D1_K       => d1_k,
      D1_INVALID => d1_invalid
   );

   P_CLK125_GEN: process
   begin
      clk125 <= '1';
      wait for C_CLKPER/2;
      clk125 <= '0';
      wait for C_CLKPER/2;
   end process;

   reset <= '1', '0' after 10.5*C_CLKPER;

   process
      variable i : integer;
      variable disp : integer;
   begin
      enc_din <= (others => '0');
      enc_k   <= '0';

      wait until reset'event and reset = '0';

      for disp in 0 to 1 loop
         -- Test for Dxx.x code-groups
         enc_k <= '0';
         for i in 0 to 2**enc_din'length-1 loop
            enc_din <= conv_std_logic_vector(i, enc_din'length) after 1 ns;
            wait until clk125'event and clk125 = '1';
         end loop;

         -- Test for Kxx.x code-groups
      end loop;

   end process;

end behavioral;

