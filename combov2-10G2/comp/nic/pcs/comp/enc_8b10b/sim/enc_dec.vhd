--
-- enc_dec.vhd: Entity for testbench enc_dec_tb.vhd
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity enc_dec is
   port (
      CLK         : in  std_logic; -- Clock signal
      RESET       : in  std_logic; -- Reset signal

      -- Enc0
      E0_DIN      : in  std_logic_vector(7 downto 0); -- 8 bit data input
      E0_K        : in  std_logic; -- Special code-group
      E0_DOUT     : out std_logic_vector(9 downto 0); -- 10 bit data output
      E0_RDISP    : out std_logic; -- Current running disparity

      -- Enc1
      E1_DIN      : in  std_logic_vector(7 downto 0); -- 8 bit data input
      E1_K        : in  std_logic; -- Special code-group
      E1_DOUT     : out std_logic_vector(9 downto 0); -- 10 bit data output
      E1_RDISP    : out std_logic; -- Current running disparity

      -- Dec0
      --D0_DIN0     : in  std_logic_vector(9 downto 0); -- 10 bit data input
      D0_DOUT     : out std_logic_vector(7 downto 0); -- 8 bit data output
      D0_K        : out std_logic; -- Special code-group
      D0_INVALID  : out std_logic; -- Invalid code-group

      -- Dec1
      --D1_DIN1     : in  std_logic_vector(9 downto 0); -- 10 bit data input
      D1_DOUT     : out std_logic_vector(7 downto 0); -- 8 bit data output
      D1_K        : out std_logic; -- Special code-group
      D1_INVALID  : out std_logic  -- Invalid code-group
   );
end enc_dec;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of enc_dec is

component dual_enc_8b10b
   port (
      CLK0        : in  std_logic;
      RESET0      : in  std_logic;
      DIN0        : in  std_logic_vector(7 downto 0);
      KIN0        : in  std_logic;
      DISP_IN0    : in  std_logic;
      FORCE_DISP0 : in  std_logic;
      DOUT0       : out std_logic_vector(9 downto 0);
      DISP_OUT0   : out std_logic;
      KERR0       : out std_logic;

      CLK1        : in  std_logic;
      RESET1      : in  std_logic;
      DIN1        : in  std_logic_vector(7 downto 0);
      KIN1        : in  std_logic;
      DISP_IN1    : in  std_logic;
      FORCE_DISP1 : in  std_logic;
      DOUT1       : out std_logic_vector(9 downto 0);
      DISP_OUT1   : out std_logic;
      KERR1       : out std_logic
   );
end component;

component enc_8b10b_logic
   port (
      CLK         : in  std_logic;
      RESET       : in  std_logic;
      DIN         : in  std_logic_vector(7 downto 0);
      K           : in  std_logic;
      DOUT        : out std_logic_vector(9 downto 0);
      RDISP       : out std_logic;

      BRAM_CLK    : out std_logic;
      BRAM_RESET  : out std_logic;
      BRAM_ADDR   : out std_logic_vector(9 downto 0);
      BRAM_DATA   : in  std_logic_vector(10 downto 0)
   );
end component;

component enc_8b10b_bram
   port (
      CLK0    : in  std_logic;
      RESET0  : in  std_logic;
      ADDR0   : in  std_logic_vector(9 downto 0);
      DATA0   : out std_logic_vector(10 downto 0);

      CLK1    : in  std_logic;
      RESET1  : in  std_logic;
      ADDR1   : in  std_logic_vector(9 downto 0);
      DATA1   : out std_logic_vector(10 downto 0)
   );
end component;

component dual_dec_8b10b
   port (
      CLK0      : in  std_logic;
      RESET0    : in  std_logic;
      DIN0      : in  std_logic_vector(9 downto 0);
      DOUT0     : out std_logic_vector(7 downto 0);
      K0        : out std_logic;
      INVALID0  : out std_logic;

      CLK1      : in  std_logic;
      RESET1    : in  std_logic;
      DIN1      : in  std_logic_vector(9 downto 0);
      DOUT1     : out std_logic_vector(7 downto 0);
      K1        : out std_logic;
      INVALID1  : out std_logic
   );
end component;

component dec_8b10b_logic
   port (
      CLK         : in  std_logic;
      RESET       : in  std_logic;
      DIN         : in  std_logic_vector(9 downto 0);
      DOUT        : out std_logic_vector(7 downto 0);
      K           : out std_logic;
      INVALID     : out std_logic;

      BRAM_CLK    : out std_logic;
      BRAM_RESET  : out std_logic;
      BRAM_ADDR   : out std_logic_vector(9 downto 0);
      BRAM_DATA   : in  std_logic_vector(13 downto 0)
   );
end component;

component dec_8b10b_bram
   port (
      CLK0    : in  std_logic;
      RESET0  : in  std_logic;
      ADDR0   : in  std_logic_vector(9 downto 0);
      DATA0   : out std_logic_vector(13 downto 0);

      CLK1    : in  std_logic;
      RESET1  : in  std_logic;
      ADDR1   : in  std_logic_vector(9 downto 0);
      DATA1   : out std_logic_vector(13 downto 0)
   );
end component;

   signal e1_bram_clk   : std_logic;
   signal e1_bram_reset : std_logic;
   signal e1_bram_addr  : std_logic_vector(9 downto 0);
   signal e1_bram_data  : std_logic_vector(10 downto 0);

   signal d1_bram_clk   : std_logic;
   signal d1_bram_reset : std_logic;
   signal d1_bram_addr  : std_logic_vector(9 downto 0);
   signal d1_bram_data  : std_logic_vector(13 downto 0);

   signal data10_0   : std_logic_vector(9 downto 0);
   signal data10_1   : std_logic_vector(9 downto 0);

begin

   E0_DOUT <= data10_0;
   E1_DOUT <= data10_1;

   ENC0: dual_enc_8b10b
   port map (
      CLK0        => CLK,
      RESET0      => RESET,
      DIN0        => E0_DIN,
      KIN0        => E0_K,
      DISP_IN0    => '0',
      FORCE_DISP0 => '0',
      DOUT0       => data10_0,
      DISP_OUT0   => E0_RDISP,
      KERR0       => open,

      CLK1        => '1',
      RESET1      => '1',
      DIN1        => "00000000", --(others => '0'),
      KIN1        => '0',
      DISP_IN1    => '0',
      FORCE_DISP1 => '0',
      DOUT1       => open,
      DISP_OUT1   => open,
      KERR1       => open
   );

   ENC1: enc_8b10b_logic
   port map (
      CLK   => CLK,
      RESET => RESET,
      DIN   => E1_DIN,
      K     => E1_K,
      DOUT  => data10_1,
      RDISP => E1_RDISP,

      BRAM_CLK   => e1_bram_clk,
      BRAM_RESET => e1_bram_reset,
      BRAM_ADDR  => e1_bram_addr,
      BRAM_DATA  => e1_bram_data
   );

   ENC1_BRAM: enc_8b10b_bram
   port map (
      CLK0    => e1_bram_clk,
      RESET0  => e1_bram_reset,
      ADDR0   => e1_bram_addr,
      DATA0   => e1_bram_data,

      CLK1    => '1',
      RESET1  => '1',
      ADDR1   => "0000000000", --(others => '0'),
      DATA1   => open
   );

   DEC0: dual_dec_8b10b
   port map (
      CLK0     => CLK,
      RESET0   => RESET,
      DIN0     => data10_0,
      DOUT0    => D0_DOUT,
      K0       => D0_K,
      INVALID0 => D0_INVALID,

      CLK1     => '1',
      RESET1   => '1',
      DIN1     => "0000000000", --(others => '0'),
      DOUT1    => open,
      K1       => open,
      INVALID1 => open
   );

   DEC1: dec_8b10b_logic
   port map (
      CLK     => CLK,
      RESET   => RESET,
      DIN     => data10_1,
      DOUT    => D1_DOUT,
      K       => D1_K,
      INVALID => D1_INVALID,

      BRAM_CLK   => d1_bram_clk,
      BRAM_RESET => d1_bram_reset,
      BRAM_ADDR  => d1_bram_addr,
      BRAM_DATA  => d1_bram_data
   );

   DEC1_BRAM: dec_8b10b_bram
   port map (
      CLK0    => d1_bram_clk,
      RESET0  => d1_bram_reset,
      ADDR0   => d1_bram_addr,
      DATA0   => d1_bram_data,

      CLK1    => '1',
      RESET1  => '1',
      ADDR1   => "0000000000", --(others => '0'),
      DATA1   => open
   );

end behavioral;

