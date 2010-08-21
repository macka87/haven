-- comp_tb.vhd: FrameLink cutter testbench
-- Copyright (C) 2008 CESNET
-- Author(s): Bronislav Pribyl <xpriby12@stud.fit.vutbr.cz>
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
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
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

   -- ============================ CONSTANTS ===================================
   
   constant CLKPER     : time := 10 ns;
   constant RESET_TIME : time := 40 ns;
   
   constant DATA_WIDTH : integer := 32; -- FrameLink width
   constant PART       : integer := 1; -- Number of processed part, 0 = first part
   constant OFFSET     : integer := 2; -- Position from SOP, 0 = first byte
   constant SIZE       : integer := 1; -- Extracted block size, greater than 0
   constant MODIFY     : boolean := true; -- If set to true, remove extracted data from frame.


   -- ============================== SIGNALS ===================================
   
   signal reset      : std_logic;
   signal clk        : std_logic;
   
   -- Cut data
   signal cut_data  : std_logic_vector(SIZE*8 - 1 downto 0);
   signal cut_vld   : std_logic; -- cut data is valid (one cycle)

   -- write interface
   signal rx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal rx_rem       : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal rx_src_rdy_n : std_logic;
   signal rx_dst_rdy_n : std_logic;
   signal i_rx_dst_rdy_n: std_logic;--pseudointerface... modelsim bug ... etc.
   signal rx_sop_n     : std_logic;
   signal rx_eop_n     : std_logic;
   signal rx_sof_n     : std_logic;
   signal rx_eof_n     : std_logic;

   -- read interface
   signal tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal tx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal tx_src_rdy_n : std_logic;
   signal tx_dst_rdy_n : std_logic;
   signal tx_sop_n     : std_logic;
   signal tx_eop_n     : std_logic;
   signal tx_sof_n     : std_logic;
   signal tx_eof_n     : std_logic;


begin

   -- UUT Instantion
   uut : entity work.fl_cutter
   generic map(
      DATA_WIDTH   => DATA_WIDTH, -- FrameLink width
      PART         => PART, -- Number of processed part, 0 = first part
      OFFSET       => OFFSET,  -- Position from SOP, 0 = first byte
      SIZE         => SIZE, -- Extracted block size, greater than 0
      MODIFY       => MODIFY -- If set to true, remove extracted data from frame.
   )
   port map(
      CLK          => clk,
      RESET        => reset,

      -- Cut data
      CUT_DATA  => cut_data,
      CUT_VLD   => cut_vld, -- cut data is valid (one cycle)

      -- Write interface
      RX_DATA      => rx_data,
      RX_REM       => rx_rem,
      RX_SRC_RDY_N => rx_src_rdy_n,
      RX_DST_RDY_N => rx_dst_rdy_n,
      RX_SOP_N     => rx_sop_n,
      RX_EOP_N     => rx_eop_n,
      RX_SOF_N     => rx_sof_n,
      RX_EOF_N     => rx_eof_n,

      -- Read interface
      TX_DATA      => tx_data,
      TX_REM       => tx_rem,
      TX_SRC_RDY_N => tx_src_rdy_n,
      TX_DST_RDY_N => tx_dst_rdy_n,
      TX_SOP_N     => tx_sop_n,
      TX_EOP_N     => tx_eop_n,
      TX_SOF_N     => tx_sof_n,
      TX_EOF_N     => tx_eof_n
   );
   
   i_rx_dst_rdy_n <= rx_dst_rdy_n;--erase
   
   
   --clock generator
   process
   begin
      clk <= '1';
      wait for CLKPER/2;
      clk <= '0';
      wait for CLKPER/2;
   end process;

   --Generating reset
   process
   begin
      reset <= '1';
      wait for RESET_TIME;
      reset <= '0';
      wait;
   end process;


   -- --------------------------------------------------------------------------
   -- TESTBENCH
   -- --------------------------------------------------------------------------
   testbench : process
   begin
   
      wait for RESET_TIME;
   
      rx_data <= (others => 'U');
      rx_rem  <= (others => 'U');
      rx_src_rdy_n <= '1';
      tx_dst_rdy_n <= '1';
      rx_sop_n <= '1';
      rx_eop_n <= '1';
      rx_sof_n <= '1';
      rx_eof_n <= '1';
      wait for CLKPER;
   
      -- frame 1 - normal ======================================================
      -- destination ready
      rx_data <= X"03020100";
      tx_dst_rdy_n <= '0';
      wait for CLKPER;

      -- source ready, start of frame and part
      rx_src_rdy_n <= '0';
      rx_sof_n <= '0';
      rx_sop_n <= '0';
      wait for CLKPER;

      --2nd beat of header
      rx_data <= X"07060504";
      rx_sof_n <= '1';
      rx_sop_n <= '1';
      wait for CLKPER;

      --3rd beat of header
      rx_data <= X"0B0A0908";
      rx_rem <= (others => '1');
      rx_eop_n <= '0';
      wait for CLKPER;

      --1st beat of payload
      rx_data <= X"13121110";
      rx_rem <= (others => 'U');
      rx_sop_n <= '0';
      rx_eop_n <= '1';
      wait for CLKPER;

      --2nd beat of payload
      rx_data <= X"17161514";
      rx_sop_n <= '1';
      wait for CLKPER;
      
      --3rd beat of payload
      rx_data <= X"1B1A1918";
      wait for CLKPER;
      
      --4th beat of payload
      rx_data <= X"1F1E1D1C";
      rx_rem <= conv_std_logic_vector(2, rx_rem'length);
      rx_eop_n <= '0';
      wait for CLKPER;
      
      --1st beat of footer
      rx_rem <= (others => 'U');
      rx_eop_n <= '1';
      -- if DST not ready, wait one cycle
      -- (kind of work-around; you should check DST_RDY all the time)
      wait for CLKPER/100;
      if (i_rx_dst_rdy_n /= '0') then
         rx_data <= (others => 'U');
         wait until CLK'event and CLK = '1';
      end if;
      rx_data <= X"23222120";
      rx_sop_n <= '0';
      wait until CLK'event and CLK = '1';
      
--       --1st beat of footer
--       rx_eop_n <= '1';
--       rx_rem <= (others => 'U');
--       wait for CLKPER/100;
--       if (i_rx_dst_rdy_n /= '0') then
--          rx_data <= (others => 'U');
--          wait until CLK'event and CLK = '1';
--       end if;
--       rx_data <= X"23222120";
--       rx_sop_n <= '0';
--       wait until CLK'event and CLK = '1';

--       --2nd beat of footer
--       rx_data <= X"28272625";
--       rx_sop_n <= '1';
--       wait for CLKPER;

      --2nd beat of footer
      rx_sop_n <= '1';
      rx_data <= X"27262524";
      wait for CLKPER;

      --3rd beat of footer
      rx_data <= X"2B2A2928";
      rx_rem <= conv_std_logic_vector(1, rx_rem'length);
      rx_eop_n <= '0';
      rx_eof_n <= '0';
      wait for CLKPER;
      
      rx_data <= (others => 'U');
      rx_rem <= (others => 'U');
      rx_src_rdy_n <= '1';
--       tx_dst_rdy_n <= '1';
      rx_eop_n <= '1';
      rx_eof_n <= '1';
      wait for CLKPER;
      
      -- frame 2 - src not ready in payload ====================================
      wait for 5*CLKPER;

      -- start of frame and part
      rx_data <= X"33323130";
      rx_src_rdy_n <= '0';
--       tx_dst_rdy_n <= '0';
      rx_sof_n <= '0';
      rx_sop_n <= '0';
      wait for CLKPER;

      --2nd beat of header
      rx_data <= X"37363534";
      rx_sof_n <= '1';
      rx_sop_n <= '1';
      wait for CLKPER;

      --3rd beat of header
      rx_data <= X"3B3A3938";
      rx_rem <= (others => '1');
      rx_eop_n <= '0';
      wait for CLKPER;

      --1st beat of payload
      rx_data <= X"43424140";
      rx_rem <= (others => 'U');
      rx_sop_n <= '0';
      rx_eop_n <= '1';
      wait for CLKPER;

      -- source not ready
      rx_sop_n <= '1';
      rx_data <= (others => 'U');
      rx_src_rdy_n <= '1';
      wait for 2*CLKPER;
      rx_src_rdy_n <= '0';
      rx_data <= X"43424140";
      rx_sop_n <= '0';

      --2nd beat of payload
      rx_data <= X"47464544";
      rx_sop_n <= '1';
      wait for CLKPER;
      
      --3rd beat of payload
      rx_data <= X"4B4A4948";
      wait for CLKPER;

      --4th beat of payload
      rx_data <= X"4F4E4D4C";
      rx_rem <= conv_std_logic_vector(2, rx_rem'length);
      rx_eop_n <= '0';
      wait for CLKPER;

      --1st beat of footer
      rx_rem <= (others => 'U');
      rx_eop_n <= '1';
      -- if DST not ready, wait one cycle
      -- (kind of work-around; you should check DST_RDY all the time)
      wait for CLKPER/100;
      if (i_rx_dst_rdy_n /= '0') then
         rx_data <= (others => 'U');
         wait until CLK'event and CLK = '1';
      end if;
      rx_data <= X"53525150";
      rx_sop_n <= '0';
      wait until CLK'event and CLK = '1';

--       --2nd beat of footer
--       rx_data <= X"57565554";
--       rx_sop_n <= '1';
--       wait for CLKPER;
      
      --2nd beat of footer
      rx_sop_n <= '1';
      rx_data <= X"57565554";
      wait for CLKPER;

      --3rd beat of footer
      rx_data <= X"5B5A5958";
      rx_rem <= conv_std_logic_vector(1, rx_rem'length);
      rx_eop_n <= '0';
      rx_eof_n <= '0';
      wait for CLKPER;

      rx_data <= (others => 'U');
      rx_rem <= (others => 'U');
      rx_eop_n <= '1';
      rx_eof_n <= '1';
      rx_src_rdy_n <= '1';


   
      wait;
   end process;

end architecture behavioral;
