-- ib_asfifo_8b.vhd : Async IB_FIFO composed of one virtex5 built-in FIFO
-- Copyright (C) 2009 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--	      Jan Stourac <xstour03@stud.fit.vutbr.cz>
--       Vaclav Bartos <washek@liberouter.org>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
Library UNISIM;
use UNISIM.vcomponents.all;

-- ----------------------------------------------------------------------------
--                              Entity declaration
-- ----------------------------------------------------------------------------
entity IB_ASFIFO_8B is
   port(
      RX_CLK         : in  std_logic;
      TX_CLK         : in  std_logic;
      RX_RESET       : in  std_logic;
      TX_RESET       : in  std_logic;

      RX_DATA        : in  std_logic_vector(7 downto 0);
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;

      TX_DATA        : out std_logic_vector(7 downto 0);
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic
   );
end IB_ASFIFO_8B;
-- ----------------------------------------------------------------------------
--                              Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ib_asfifo_8b is

signal par_in     : std_logic_vector(1 downto 0);
signal par_out    : std_logic_vector(1 downto 0);

signal data_in    : std_logic_vector(15 downto 0);
signal data_out   : std_logic_vector(15 downto 0);

signal reset_both : std_logic;

signal sig_empty  : std_logic;
signal sig_full   : std_logic;
signal sig_rden   : std_logic;
signal sig_wren   : std_logic;

begin
   reset_both <= RX_RESET or TX_RESET;
   
   data_in <= "00000000" & RX_DATA;
   par_in  <= RX_SOP_N & RX_EOP_N;
   RX_DST_RDY_N <= sig_full;
   sig_wren <= not RX_SRC_RDY_N;

   FIFO18_inst : FIFO18
   generic map (
      DATA_WIDTH => 18,               -- Sets width of data (4 or 9 or 18)
      ALMOST_FULL_OFFSET => X"0080",  -- Sets almost full threshold
      ALMOST_EMPTY_OFFSET => X"0080", -- Sets the almost empty threshold
      DO_REG => 1,                    -- Enable output register (0 or 1)
                                      -- Must be 1 if EN_SYN = FALSE 
      EN_SYN => FALSE,                -- Specifies FIFO as Asynchronous (FALSE)
                                      -- or Synchronous (TRUE)
      FIRST_WORD_FALL_THROUGH => TRUE,-- Sets the FIFO FWFT to TRUE or FALSE
      SIM_MODE => "SAFE") -- Simulation: "SAFE" vs "FAST", see "Synthesis and Simulation
                          -- Design Guide" for details
   port map (
      ALMOSTEMPTY => open,          -- 1-bit almost empty output flag
      ALMOSTFULL => open,           -- 1-bit almost full output flag
      DO => data_out,               -- 16-bit data output
      DOP => par_out,               -- 2-bit parity data output
      EMPTY => sig_empty,           -- 1-bit empty output flag
      FULL => sig_full,             -- 1-bit full output flag
      RDCOUNT => open,              -- 12-bit read count output
      RDERR => open,                -- 1-bit read error output
      WRCOUNT => open,              -- 12-bit write count output
      WRERR => open,                -- 1-bit write error
      DI => data_in,                -- 16-bit data input
      DIP => par_in,                -- 2-bit parity input
      RDCLK => TX_CLK,              -- 1-bit read clock input
      RDEN => sig_rden,             -- 1-bit read enable input
      RST => reset_both,            -- 1-bit reset input
      WRCLK => RX_CLK,              -- 1-bit write clock input
      WREN => sig_wren              -- 1-bit write enable input
   );

   TX_DATA     <= data_out(7 downto 0);
   TX_EOP_N    <= par_out(0);
   TX_SOP_N    <= par_out(1);
   TX_SRC_RDY_N <= sig_empty;
   sig_rden    <= not TX_DST_RDY_N;

end architecture full;

