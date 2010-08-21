-- rx_tb.vhd: Testbench File
-- Copyright (C) 2009 CESNET
-- Author: Martin Spinler <xspinl00@stud.fit.vutbr.cz>
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
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.numeric_std.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   -- Constant declaration
   constant CLKPER       : time := 10 ns;
   constant IFC_COUNT    : integer := 4;
   constant IFC_WIDTH    : integer := log2(IFC_COUNT);
   constant DMA_DATA_WIDTH : integer := 32;

   signal CLK            : std_logic;
   signal RESET          : std_logic;

   signal DMA_ADDR       : std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
   signal DMA_DOUT       : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal DMA_REQ        : std_logic;
   signal DMA_ACK        : std_logic;
   signal DMA_DONE       : std_logic;

   -- Receive buffer interface
   signal BUF_NEWLEN     : std_logic_vector(15 downto 0);
   signal BUF_NEWLEN_DV  : std_logic;
   signal BUF_NEWLEN_IFC : std_logic_vector(IFC_WIDTH-1 downto 0);

   signal BUF_RELLEN     : std_logic_vector(15 downto 0);
   signal BUF_RELLEN_DV  : std_logic;
   signal BUF_RELLEN_IFC : std_logic_vector(IFC_WIDTH-1 downto 0);
   
   signal DESC_DATA      : std_logic_vector(63 downto 0);
   signal DESC_EMPTY     : std_logic;
   signal DESC_IFC       : std_logic_vector(IFC_WIDTH-1 downto 0);
   signal DESC_READ      : std_logic;
   signal DESC_DV        : std_logic;

   signal INTERRUPT      : std_logic;
   signal INTERRUPT_IFC  : std_logic_vector(IFC_WIDTH-1 downto 0);

   signal ENABLE         : std_logic_vector(IFC_COUNT-1 downto 0);

   signal SW_ADDR        : std_logic_vector(31 downto 0);
   signal SW_ARDY        : std_logic;
   signal SW_BE          : std_logic_vector(3 downto 0);
   signal SW_DRD         : std_logic_vector(31 downto 0);
   signal SW_DRDY        : std_logic;
   signal SW_DWR         : std_logic_vector(31 downto 0);
   signal SW_RD          : std_logic;
   signal SW_WR          : std_logic;

begin

   -- ------------------------------------------------------------------
   -- UUT Instantion
   uut : entity work.rx_dma_ctrl_arch
   port map(
      -- Common interface
      PIN_CLK         => CLK,
      PIN_RESET       => RESET,
      
      BUFFER_ADDR     => X"01230000",
      
      -- Receive buffer interface
      BUF_NEWLEN     => BUF_NEWLEN,
      BUF_NEWLEN_DV  => BUF_NEWLEN_DV,
      BUF_NEWLEN_IFC => BUF_NEWLEN_IFC,

      BUF_RELLEN     => BUF_RELLEN,
      BUF_RELLEN_DV  => BUF_RELLEN_DV,
      BUF_RELLEN_IFC => BUF_RELLEN_IFC,

      DMA_ADDR       => DMA_ADDR,
      DMA_DOUT       => DMA_DOUT,
      DMA_REQ        => DMA_REQ,
      DMA_ACK        => DMA_ACK,
      DMA_DONE       => DMA_DONE,

      DESC_IFC       => DESC_IFC,
      DESC_READ      => DESC_READ,
      DESC_DATA      => DESC_DATA,
      DESC_EMPTY     => DESC_EMPTY,
      DESC_DV        => DESC_DV,

      INTERRUPT      => INTERRUPT,
      INTERRUPT_IFC  => INTERRUPT_IFC,
      ENABLE         => ENABLE,

      SW_ADDR        => SW_ADDR,
      SW_ARDY        => SW_ARDY,
      SW_BE          => SW_be,
      SW_DRD         => SW_drd,
      SW_DRDY        => SW_drdy,
      SW_DWR         => SW_dwr,
      SW_RD          => SW_rd,
      SW_WR          => SW_wr
   );

   -- clk clock generator
   clkgen_CLK: process
   begin
      CLK <= '1';
      wait for CLKPER/2;
      CLK <= '0';
      wait for CLKPER/2;
   end process;

   desc_manager : process (DESC_IFC, DESC_READ, CLK)
   begin
      DESC_EMPTY <= '0';
      if(CLK'event and CLK='1') then
         DESC_DV <= DESC_READ;
      end if;
      DESC_DATA <= X"DE5C000" & "00" & DESC_IFC & X"10000000";
   end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------

tb : process
begin
   RESET <= '1', '0' after 10 ns;
   BUF_NEWLEN_IFC <= "00";BUF_NEWLEN <= X"0000";BUF_NEWLEN_DV  <= '0';
   DMA_ADDR <= "00";
   SW_ADDR <= X"00000000"; SW_DWR <= X"00000000"; SW_RD <= '0'; SW_WR <='0'; SW_BE <= "1111";
   wait for 20*CLKPER;

   BUF_NEWLEN_IFC <= "00";BUF_NEWLEN <= X"0050";BUF_NEWLEN_DV  <= '1';wait for CLKPER;BUF_NEWLEN_DV  <= '0';wait for 10*CLKPER;
   BUF_NEWLEN_IFC <= "00";BUF_NEWLEN <= X"0040";BUF_NEWLEN_DV  <= '1';wait for CLKPER;BUF_NEWLEN_DV  <= '0';wait for 10*CLKPER;
   BUF_NEWLEN_IFC <= "00";BUF_NEWLEN <= X"0010";BUF_NEWLEN_DV  <= '1';wait for CLKPER;BUF_NEWLEN_DV  <= '0';wait for 10*CLKPER;

   SW_ADDR <=X"00000000";SW_DWR <= X"00000001"; SW_WR <= '1'; wait for CLKPER; SW_WR <= '0';wait for CLKPER; -- START
   SW_ADDR <=X"00000010";SW_DWR <= X"0000ffff"; SW_WR <= '1'; wait for CLKPER; SW_WR <= '0';wait for CLKPER;    -- SwBufferMask
  
   wait for 30*CLKPER;
   BUF_NEWLEN_IFC <= "00";BUF_NEWLEN <= X"0400";BUF_NEWLEN_DV  <= '1';wait for CLKPER;BUF_NEWLEN_DV  <= '0';
   BUF_NEWLEN_IFC <= "00";BUF_NEWLEN <= X"0400";BUF_NEWLEN_DV  <= '1';wait for CLKPER;BUF_NEWLEN_DV  <= '0';
   BUF_NEWLEN_IFC <= "00";BUF_NEWLEN <= X"0500";BUF_NEWLEN_DV  <= '1';wait for CLKPER;BUF_NEWLEN_DV  <= '0';
   BUF_NEWLEN_IFC <= "00";BUF_NEWLEN <= X"0300";BUF_NEWLEN_DV  <= '1';wait for CLKPER;BUF_NEWLEN_DV  <= '0';

   wait for 30*CLKPER;
   DMA_ADDR <= "00"; wait for CLKPER;
   DMA_ADDR <= "01"; wait for CLKPER;
   DMA_ADDR <= "10"; wait for CLKPER;
   DMA_ADDR <= "11"; wait for CLKPER;
   DMA_ACK <= '1'; wait for CLKPER;
   DMA_ACK <= '0'; wait for 5*CLKPER;
   DMA_DONE<= '1'; wait for CLKPER;
   DMA_DONE<= '0'; wait for CLKPER;

   wait;
end process;

end architecture behavioral;
-- ----------------------------------------------------------------------------

