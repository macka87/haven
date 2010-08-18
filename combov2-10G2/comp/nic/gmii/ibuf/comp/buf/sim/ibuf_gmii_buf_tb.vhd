--
-- ibuf_gmii_buf_tb.vhd: Testbench for ibuf gmii buf part
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant rd_clkper  : time    := 10 ns;
   constant wr_clkper  : time    :=  8 ns;
   constant DATA_PATHS : integer := 2;

   signal reset        : std_logic;

   signal wrclk        : std_logic;
   signal di           : std_logic_vector(7 downto 0);
   signal di_dv        : std_logic;
   signal stat         : std_logic_vector(1 downto 0);
   signal stat_dv      : std_logic;
   signal sop          : std_logic;
   
   signal rdclk        : std_logic;
   signal dfifo_do     : std_logic_vector(DATA_PATHS*9-1 downto 0);
   signal dfifo_rd     : std_logic;
   signal dfifo_dv     : std_logic;
   signal dfifo_empty  : std_logic;

   signal cfifo_do     : std_logic_vector(1 downto 0);
   signal cfifo_rd     : std_logic;
   signal cfifo_dv     : std_logic;
   signal cfifo_empty  : std_logic;

   signal ctrl_di      : std_logic_vector(7 downto 0);
   signal ctrl_dv      : std_logic;
   signal sau_accept   : std_logic;
   signal sau_dv       : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

-- ----------------------------------------------------
-- UUT mapping
-- ----------------------------------------------------

UUT : entity work.ibuf_gmii_buf
generic map(
   DATA_PATHS => DATA_PATHS,
   CTRL_LEN   => 2,
   DFIFO_SIZE => 10*384,
   MAX_PACKETS => 10

)
port map(
   RESET => reset,

   WRCLK        => wrclk,
   DI           => di,
   DI_DV        => di_dv,
   STAT         => stat,
   STAT_DV      => stat_dv,
   SOP          => sop,

   CTRL_DI     => ctrl_di,
   CTRL_DV     => ctrl_dv,

   -- sampling unit interface
   SAU_ACCEPT => sau_accept,
   SAU_DV     => sau_dv,

   -- ibuf_gmii_cmd interface
   RDCLK        => rdclk,

   DFIFO_DO     => dfifo_do,
   DFIFO_RD     => dfifo_rd,
   DFIFO_DV     => dfifo_dv,
   DFIFO_EMPTY  => dfifo_empty,
   
   CFIFO_DO     => cfifo_do,
   CFIFO_RD     => cfifo_rd,
   CFIFO_DV     => cfifo_dv,
   CFIFO_EMPTY  => cfifo_empty,
	  
   ADC_RD       => '0',
   ADC_WR       => '0',
   ADC_ADDR     => (others=>'0'),
   ADC_DI       => (others=>'0'),
   ADC_DO       => open,
   ADC_DRDY     => open
);


-- ----------------------------------------------------
-- wrclk clock generator
wrclk_clkgen : process
begin
   wrclk <= '1';
   wait for wr_clkper/2;
   wrclk <= '0';
   wait for wr_clkper/2;
end process;

-- rdclk clock generator
rdclk_clkgen : process
begin
   rdclk <= '1';
   wait for rd_clkper/2;
   rdclk <= '0';
   wait for rd_clkper/2;
end process;

-- di <= (others=>'0');----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------

in_p : process

begin
   di       <= (others=>'0');
   di_dv    <= '0';
   stat     <= (others=>'0');
   stat_dv  <= '0';
   sop      <= '0';

   reset <= '1';
   wait for 100 ns;
   reset <= '0';

   wait until (wrclk='1' and wrclk'event);

   sop <= '1';
   wait until (wrclk='1' and wrclk'event);
   sop <= '0';
   wait until (wrclk='1' and wrclk'event);
   wait until (wrclk='1' and wrclk'event);
   wait until (wrclk='1' and wrclk'event);
      di_dv <= '1';
   for i in 1 to 20 loop
      di    <= conv_std_logic_vector(i, di'length);
      wait until (wrclk='1' and wrclk'event);
   end loop;

   di_dv <= '0';
   di <= (others=>'0');

   wait until (wrclk='1' and wrclk'event);
   wait until (wrclk='1' and wrclk'event);
   wait until (wrclk='1' and wrclk'event);
   wait until (wrclk='1' and wrclk'event);
   stat_dv <= '1';
   stat <= "00";
   wait until (wrclk='1' and wrclk'event);
   stat_dv <= '0';

   wait;
end process;

out_p : process
begin
   dfifo_rd <= '0';
   cfifo_rd <= '0';

   wait until reset='0';
   
   wait until (rdclk='1' and rdclk'event);
   dfifo_rd <= '1';
   wait until (dfifo_dv='1' and rdclk='1' and rdclk'event);
   wait until ((dfifo_do(DATA_PATHS*9-1 downto DATA_PATHS*8) /="11") and rdclk='1' and rdclk'event);
   dfifo_rd <= '0';
   wait until (cfifo_empty='0' and rdclk='1' and rdclk'event);
   cfifo_rd <= '1';
   wait until (rdclk='1' and rdclk'event);
   cfifo_rd <= '0';

   wait;
end process;

end architecture behavioral;
