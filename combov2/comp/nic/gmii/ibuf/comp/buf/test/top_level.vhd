-- top_level.vhd : Combo top level entity
-- Copyright (C) 2005 CESNET
-- Author(s): Jiri Tobola <tobola@liberouter.org>
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
-- --------------------------------------------------------------------
--                          Entity declaration
-- --------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
--use work.addr_space.all;
--
-- pragma translate_off
--library unisim;
--use unisim.vcomponents.all;
-- pragma translate_on
entity fpga is
   port(
      RESET   : in  std_logic;

      -- ibuf_gmii_rx interface
      WRCLK       : in  std_logic;
      DI          : in  std_logic_vector(7 downto 0);
      DI_DV       : in  std_logic;
      STAT        : in  std_logic_vector(1 downto 0);
      STAT_DV     : in  std_logic;
      SOP         : in  std_logic;

      -- backend interface
      RDCLK       : in  std_logic;
      DFIFO_DO    : out std_logic_vector(2*9-1 downto 0);
      DFIFO_RD    : in  std_logic;
      DFIFO_DV    : out std_logic;

      SFIFO_DO    : out std_logic_vector(1 downto 0);
      SFIFO_RD    : in  std_logic;
      SFIFO_EMPTY : out std_logic;

      -- Address decoder interface
      ADC_RD      : in  std_logic; -- Read Request
      ADC_WR      : in  std_logic; -- Write Request
      ADC_ADDR    : in  std_logic_vector(1 downto 0);  -- Address
      ADC_DI      : in  std_logic_vector(31 downto 0); -- Input Data
      ADC_DO      : out std_logic_vector(31 downto 0);  -- Output Data
      ADC_DRDY    : out std_logic
   );
end entity fpga;
-- --------------------------------------------------------------------
--                      Architecture declaration
-- --------------------------------------------------------------------
architecture behavioral of fpga is

-- ------------------------ Clk generation -----------------------------



-- ------------------------------------------------------------------
--                      Signal declaration
-- ------------------------------------------------------------------
      signal reg_DI        : std_logic_vector(7 downto 0);
      signal reg_DI_DV     : std_logic;
      signal reg_STAT      : std_logic_vector(1 downto 0);
      signal reg_STAT_DV   : std_logic;
      signal reg_SOP       : std_logic;

      -- backend interface
      signal DFIFO_DO_i    : std_logic_vector(2*9-1 downto 0);
      signal reg_DFIFO_DO    : std_logic_vector(2*9-1 downto 0);
      signal reg_DFIFO_RD  : std_logic;
      signal DFIFO_DV_i    : std_logic;
      signal reg_DFIFO_DV    : std_logic;

      signal SFIFO_DO_i    : std_logic_vector(1 downto 0);
      signal reg_SFIFO_DO    : std_logic_vector(1 downto 0);
      signal reg_SFIFO_RD  : std_logic;
      signal SFIFO_EMPTY_i : std_logic;
      signal reg_SFIFO_EMPTY : std_logic;
-- ------------------------------------------------------------------
--                       Architecture body
-- ------------------------------------------------------------------

begin
UUT : entity work.ibuf_gmii_buf
generic map(
   ADDR_BASE  => 0,
   ADDR_WIDTH => 2,

   DATA_PATHS => 2,

   DFIFO_SIZE => 4095,
   SFIFO_SIZE => 20

)
port map(
   RESET => reset,

   WRCLK        => wrclk,
   DI           => reg_di,
   DI_DV        => reg_di_dv,
   STAT         => reg_stat,
   STAT_DV      => reg_stat_dv,
   SOP          => reg_sop,

   -- ibuf_gmii_cmd interface
   RDCLK        => rdclk,

   DFIFO_DO     => dfifo_do_i,
   DFIFO_RD     => reg_dfifo_rd,
   DFIFO_DV     => dfifo_dv_i,
   
   SFIFO_DO     => sfifo_do_i,
   SFIFO_RD     => reg_sfifo_rd,
   SFIFO_EMPTY  => sfifo_empty_i,
	  
   -- FIXME!!!! register inputs and outputs
   ADC_RD       => ADC_RD,
   ADC_WR       => ADC_WR,
   ADC_ADDR     => ADC_ADDR,
   ADC_DI       => ADC_DI,
   ADC_DO       => ADC_DO,
   ADC_DRDY     => ADC_DRDY
);

-- ----------------------------------------------------------------------
reg_rd_p: process(RESET,RDCLK)
begin
   if (RESET='1') then
      reg_dfifo_rd <= '0';
      reg_sfifo_rd <= '0';
      reg_dfifo_do     <= (others=>'0');
      reg_dfifo_dv     <= '0';
      reg_sfifo_do     <= (others=>'0');
      reg_sfifo_empty  <= '0';
   elsif (rdclk'event and rdclk='1') then
      reg_dfifo_rd <= dfifo_rd;
      reg_sfifo_rd <= sfifo_rd;
      reg_dfifo_do     <= dfifo_do_i;
      reg_dfifo_dv     <= dfifo_dv_i;
      reg_sfifo_do     <= sfifo_do_i;
      reg_sfifo_empty  <= sfifo_empty_i;
   end if;
end process;

reg_wr_p: process(RESET,WRCLK)
begin
   if (RESET='1') then
      reg_DI           <= (others=>'0');
      reg_DI_DV        <= '0';
      reg_STAT         <= (others=>'0');
      reg_STAT_DV      <= '0';
      reg_SOP          <= '0';
   elsif (wrclk'event and wrclk='1') then
      reg_DI           <= DI;
      reg_DI_DV        <= DI_DV;
      reg_STAT         <= STAT;
      reg_STAT_DV      <= STAT_DV;
      reg_SOP          <= SOP;
   end if;
end process;

DFIFO_DO <= reg_DFIFO_DO;
DFIFO_DV <= reg_DFIFO_DV;
SFIFO_DO <= reg_SFIFO_DO;
SFIFO_EMPTY <= reg_SFIFO_EMPTY;

end architecture behavioral;

