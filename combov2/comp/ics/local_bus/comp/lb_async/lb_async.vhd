-- lb_async.vhd : Async LB_FIFO composed of two virtex5 built-in FIFOs
-- Copyright (C) 2009 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--	      Jan Stourac <xstour03@stud.fit.vutbr.cz>
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
entity LB_ASYNC is
   port(
      RX_CLK         : in  std_logic;
      TX_CLK         : in  std_logic;
      RX_RESET       : in  std_logic;
      TX_RESET       : in  std_logic;

      RX_DWR         : in  std_logic_vector(15 downto 0);           -- Input Data
      RX_BE          : in  std_logic_vector(1 downto 0);            -- Byte Enable
      RX_ADS_N       : in  std_logic;                               -- Address Strobe
      RX_RD_N        : in  std_logic;                               -- Read Request
      RX_WR_N        : in  std_logic;                               -- Write Request
      RX_DRD         : out std_logic_vector(15 downto 0);           -- Output Data
      RX_RDY_N       : out std_logic;                               -- Ready
      RX_ERR_N       : out std_logic;                               -- Error
      RX_ABORT_N     : in  std_logic;                               -- Abort Transaction

      TX_DWR         : out std_logic_vector(15 downto 0);           -- Input Data
      TX_BE          : out std_logic_vector(1 downto 0);            -- Byte Enable
      TX_ADS_N       : out std_logic;                               -- Address Strobe
      TX_RD_N        : out std_logic;                               -- Read Request
      TX_WR_N        : out std_logic;                               -- Write Request
      TX_DRD         : in  std_logic_vector(15 downto 0);           -- Output Data
      TX_RDY_N       : in  std_logic;                               -- Ready
      TX_ERR_N       : in  std_logic;                               -- Error
      TX_ABORT_N     : out std_logic                                -- Abort Transaction
   );
end LB_ASYNC;
-- ----------------------------------------------------------------------------
--                              Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of lb_async is

----- component FIFO36 -----
component FIFO36
	generic
	(
		ALMOST_FULL_OFFSET : bit_vector := X"0080";
		ALMOST_EMPTY_OFFSET : bit_vector := X"0080";
		DATA_WIDTH : integer := 4;
		DO_REG : integer := 1;
		EN_SYN : boolean := FALSE;
		FIRST_WORD_FALL_THROUGH : boolean := FALSE;
		SIM_MODE : string := "SAFE"
	);
	port
	(
		ALMOSTEMPTY : out std_ulogic;
		ALMOSTFULL : out std_ulogic;
		DO : out std_logic_vector (31 downto 0);
		DOP : out std_logic_vector (3 downto 0);
		EMPTY : out std_ulogic;
		FULL : out std_ulogic;
		RDCOUNT : out std_logic_vector (12 downto 0);
		RDERR : out std_ulogic;
		WRCOUNT : out std_logic_vector (12 downto 0);
		WRERR : out std_ulogic;
		DI : in std_logic_vector (31 downto 0);
		DIP : in std_logic_vector (3 downto 0);
		RDCLK : in std_ulogic;
		RDEN : in std_ulogic;
		RST : in std_ulogic;
		WRCLK : in std_ulogic;
		WREN : in std_ulogic
	);
end component;
attribute BOX_TYPE : string;
attribute BOX_TYPE of
	FIFO36 : component is "PRIMITIVE";

component FIFO18
	generic
	(
		ALMOST_FULL_OFFSET : bit_vector := X"080";
		ALMOST_EMPTY_OFFSET : bit_vector := X"080";
		DATA_WIDTH : integer := 4;
		DO_REG : integer := 1;
		EN_SYN : boolean := FALSE;
		FIRST_WORD_FALL_THROUGH : boolean := FALSE;
		SIM_MODE : string := "SAFE"
	);
	port
	(
		ALMOSTEMPTY : out std_ulogic;
		ALMOSTFULL : out std_ulogic;
		DO : out std_logic_vector (15 downto 0);
		DOP : out std_logic_vector (1 downto 0);
		EMPTY : out std_ulogic;
		FULL : out std_ulogic;
		RDCOUNT : out std_logic_vector (11 downto 0);
		RDERR : out std_ulogic;
		WRCOUNT : out std_logic_vector (11 downto 0);
		WRERR : out std_ulogic;
		DI : in std_logic_vector (15 downto 0);
		DIP : in std_logic_vector (1 downto 0);
		RDCLK : in std_ulogic;
		RDEN : in std_ulogic;
		RST : in std_ulogic;
		WRCLK : in std_ulogic;
		WREN : in std_ulogic
	);
end component;
attribute BOX_TYPE of
	FIFO18 : component is "PRIMITIVE";
   


signal tx_par_in  : std_logic_vector(1 downto 0);
signal tx_par_out : std_logic_vector(1 downto 0);
signal rx_par_in  : std_logic_vector(3 downto 0);
signal rx_par_out : std_logic_vector(3 downto 0);


signal rx_data_in : std_logic_vector(31 downto 0);
signal rx_data_out: std_logic_vector(31 downto 0);

signal reset_both : std_logic;

signal rx_sig_empty  : std_logic;
signal rx_sig_rden   : std_logic;
signal rx_sig_wren   : std_logic;
signal tx_sig_empty  : std_logic;
signal tx_sig_rden   : std_logic;
signal tx_sig_wren   : std_logic;

begin

   reset_both <= RX_RESET or TX_RESET;

   rx_data_in <= "00000000000000" & RX_BE & RX_DWR;
   rx_par_in <= RX_ABORT_N & RX_WR_N & RX_RD_N & RX_ADS_N;

   rx_sig_wren <= not (RX_ADS_N and RX_RD_N and RX_WR_N and RX_ABORT_N);

   -- ---------------------------------------------------------------------
   -- fifo in RX to TX direction
   RX_FIFO36_inst : FIFO36
   generic map (
      ALMOST_FULL_OFFSET => X"0080",  -- Sets almost full threshold
      ALMOST_EMPTY_OFFSET => X"0080", -- Sets the almost empty threshold
      DATA_WIDTH => 36,               -- Sets data width to 4, 9, 18, or 36
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
      DO => rx_data_out,            -- 32-bit data output
      DOP => rx_par_out,            -- 4-bit parity data output
      EMPTY => rx_sig_empty,        -- 1-bit empty output flag
      FULL => open,                 -- 1-bit full output flag
      RDCOUNT => open,              -- 13-bit read count output
      RDERR => open,                -- 1-bit read error output
      WRCOUNT => open,              -- 13-bit write count output
      WRERR => open,                -- 1-bit write error
      DI => rx_data_in,             -- 32-bit data input
      DIP => rx_par_in,             -- 4-bit parity input
      RDCLK => TX_CLK,              -- 1-bit read clock input
      RDEN => rx_sig_rden,          -- 1-bit read enable input
      RST => reset_both,            -- 1-bit reset input
      WRCLK => RX_CLK,              -- 1-bit write clock input
      WREN => rx_sig_wren           -- 1-bit write enable input
   );

   rx_sig_rden <= not rx_sig_empty;

   TX_DWR <= rx_data_out(15 downto 0);
   TX_BE  <= rx_data_out(17 downto 16);

   tx_out_mux : process(rx_sig_empty, rx_par_out)
   begin
      if rx_sig_empty = '0' then
         TX_ADS_N    <= rx_par_out(0);
         TX_RD_N     <= rx_par_out(1);
         TX_WR_N     <= rx_par_out(2);
         TX_ABORT_N  <= rx_par_out(3);
      else
         TX_ADS_N    <= '1';
         TX_RD_N     <= '1';
         TX_WR_N     <= '1';
         TX_ABORT_N  <= '1';
      end if;
   end process;

   -- ---------------------------------------------------------------------

   tx_par_in <= TX_ERR_N & TX_RDY_N;

   tx_sig_wren <= not (TX_RDY_N and TX_ERR_N);

   -- ---------------------------------------------------------------------
   -- fifo in TX to RX direction
   TX_FIFO18_inst : FIFO18
   generic map (
      ALMOST_FULL_OFFSET => X"080",  -- Sets almost full threshold
      ALMOST_EMPTY_OFFSET => X"080", -- Sets the almost empty threshold
      DATA_WIDTH => 18,               -- Sets data width to 4, 9 or 18
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
      DO => RX_DRD,                 -- 16-bit data output
      DOP => tx_par_out,            -- 2-bit parity data output
      EMPTY => tx_sig_empty,        -- 1-bit empty output flag
      FULL => open,                 -- 1-bit full output flag
      RDCOUNT => open,              -- 8-bit read count output
      RDERR => open,                -- 1-bit read error output
      WRCOUNT => open,              -- 8-bit write count output
      WRERR => open,                -- 1-bit write error
      DI => TX_DRD,                 -- 16-bit data input
      DIP => tx_par_in,             -- 2-bit parity input
      RDCLK => RX_CLK,              -- 1-bit read clock input
      RDEN => tx_sig_rden,          -- 1-bit read enable input
      RST => reset_both,            -- 1-bit reset input
      WRCLK => TX_CLK,              -- 1-bit write clock input
      WREN => tx_sig_wren           -- 1-bit write enable input
   );

   tx_sig_rden <= not tx_sig_empty;

   rx_out_mux : process(tx_sig_empty, tx_par_out)
   begin
      if tx_sig_empty = '0' then
         RX_RDY_N <= tx_par_out(0);
         RX_ERR_N <= tx_par_out(1);
      else
         RX_RDY_N <= '1';
         RX_ERR_N <= '1';
      end if;
   end process;

end architecture full;
											
