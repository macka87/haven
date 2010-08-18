-- mdio.vhd MDIO design architecture
-- Copyright (C) 2003 CESNET
-- Author(s): Michal Janousek <xjanou11@stud.fit.vutbr.cz>
--            Stepan Friedl <friedl@liberouter.org>
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

architecture full of mdio_ctrl is

   --signal for connection with LBConnmem
   signal data_out   : std_logic_vector(15 downto 0);   -- Data output
   signal data_in    : std_logic_vector(15 downto 0);   -- Data input
   signal addr       : std_logic_vector(ADDR_WIDTH - 1  downto 0);
   signal rw         : std_logic;                       -- Write/Read#
   signal en         : std_logic;                       -- Data Enable
   signal sel        : std_logic;                       -- Select

   signal mdio_do    : std_logic_vector(15 downto 0);
   signal mdio_frame : std_logic_vector(31 downto 0);
   signal mdio_start : std_logic;
   signal mdio_busy  : std_logic;

--------------------------------------------------------
-- component LBConn_MEM
--------------------------------------------------------
component lbconn_mem is
   Generic ( BASE       : integer := 16#0010000#; -- Base address (28 bit)
             ADDR_WIDTH : integer := 2           -- Width of address,
           );                                     -- max. 28
   Port (
      DATA_OUT : out std_logic_vector(15 downto 0);  -- Data output
      DATA_IN  : in std_logic_vector(15 downto 0);   -- Data input
      ADDR     : out std_logic_vector(ADDR_WIDTH-1 downto 0); -- Address output
      RW       : out std_logic;                      -- Write/Read#
      EN       : out std_logic;                      -- Data Enable
      SEL      : out std_logic;                      -- Select
      DRDY     : in std_logic;                       -- Data ready input
      ARDY     : in std_logic;                       -- Address Ready (ACK)
      -- local bus interconnection
      RESET   : IN std_logic;
      LBCLK   : IN std_logic;
      LBFRAME : IN std_logic;
      LBAS    : IN std_logic;
      LBRW    : IN std_logic;
      LBLAST  : IN std_logic;
      LBAD    : INOUT std_logic_vector(15 downto 0);
      LBHOLDA : OUT std_logic;
      LBRDY   : OUT std_logic
      );
end component lbconn_mem;


begin

LB_CONNECTION: lbconn_mem
generic map (
   BASE       => BASE,
   ADDR_WIDTH => ADDR_WIDTH
)
port map (
   RESET   => RESET,
   LBCLK   => LBCLK,
   LBFRAME => LBFRAME,
   LBAS    => LBAS,
   LBRW    => LBRW,
   LBLAST  => LBLAST,
   LBAD    => LBAD,
   LBHOLDA => LBHOLDA,
   LBRDY   => LBRDY,
   DATA_OUT=> data_out,
   DATA_IN => data_in,
   ADDR    => addr,
   RW      => rw,
   EN      => en,
   SEL     => sel,
   DRDY    => '1',
   ARDY    => '1'
);

MDIO_CTRL  : entity work.mdio_c
port map(
   CLK       => LBCLK,                -- Input clock
   DIV_CLK   => "01100",              -- Divider ratio (for 100 MHz CLK)
   START_OP  => mdio_frame(1 downto 0),
   OPERATION => mdio_frame(3 downto 2),
   PHY_ADDR  => mdio_frame(8 downto 4),
   REG_ADDR  => mdio_frame(13 downto 9),
   DATA_IN   => mdio_frame(31 downto 16),
   DATA_OUT  => mdio_do,
   DATA_RDY  => open,
   RUN_OP    => mdio_start,
   BUSY      => mdio_busy,
   MDC       => MDC,                  -- MDIO Clock output
   MDIO      => MDIO                  -- MDIO Data - Input/Output
);

MDIO_REGS : process(LBCLK,RESET)
begin
   if (RESET = '1') then
      mdio_frame <= (others => '1');
      mdio_start <= '0';
      data_in    <= (others => '0');
   elsif (LBCLK'event AND LBCLK = '1') then
      mdio_start <= '0';
      -- Write to MDIO registers
      if (en = '1') and (rw = '1') then
         case addr(2 downto 0) is
            when "000" | "010" => mdio_frame(15 downto 0)  <= data_out;
            when "001" | "011" => mdio_frame(31 downto 16) <= data_out;
                                  mdio_start               <= '1';
            when others => null;
         end case;
      end if;
      -- read from MDIO registers
      case addr(2 downto 0)  is
         when "000"  => data_in <= mdio_frame(15 downto 0);    -- 0x0
         when "001"  => data_in <= mdio_frame(31 downto 16);   -- 0x2
         when "100"  => data_in <= mdio_do;                    -- 0x8
         when "110"  => data_in <= X"000" & "000" & mdio_busy; -- 0xC
         when others => data_in <= (others => '0');
      end case;
   end if;
end process;

end full;
-----------------------------------------------------------------
