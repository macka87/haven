-- hw_header_sender.vhd: Sending of constant HW header
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity SWT_HW_HEADER_SENDER is
   generic(
      DATA_WIDTH                 : integer;
      CONSTANT_HW_HEADER_LENGTH  : integer;
      CONSTANT_HW_HEADER_DATA    : std_logic_vector(63 downto 0)
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;
      -- control interface
      SENDER_ENABLE  : in  std_logic;
      LAST_WORD      : out std_logic;
      -- output interface
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic
   );
end entity SWT_HW_HEADER_SENDER;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of SWT_HW_HEADER_SENDER is

   -- ------------------ Constants declaration --------------------------------
   constant C_BYTE_MAX     : integer := 8;
   constant C_WORD_COUNT   : integer := 
                           (CONSTANT_HW_HEADER_LENGTH + (DATA_WIDTH/8) - 1) / 
                           (DATA_WIDTH/8);
   constant C_WORD_MAX     : integer := C_BYTE_MAX / (DATA_WIDTH/8);
   constant C_TX_REM       : integer := 
                           CONSTANT_HW_HEADER_LENGTH rem (DATA_WIDTH/8)-1;

   -- ------------------ Signals declaration ----------------------------------
   -- multiplexers
   signal mx_tx_data          : std_logic_vector(DATA_WIDTH-1 downto 0);

   -- counters
   signal cnt_word            : std_logic_vector(abs(log2(C_WORD_MAX)-1) downto 0);
   signal cnt_word_ce         : std_logic;
   signal cnt_word_clr        : std_logic;

   -- others
   signal cmp_cnt_word_max    : std_logic;
   signal cmp_cnt_word_min    : std_logic;
   signal last_word_valid     : std_logic;

begin
   assert (C_BYTE_MAX >= (DATA_WIDTH/8)) 
      report "SW_TXBUF(HEADER_SENDER): output width larger than 64b!" 
      severity error;

   -- ------------------ directly mapped signals ------------------------------
   cnt_word_clr      <= last_word_valid;
   cnt_word_ce       <= (not TX_DST_RDY_N) and SENDER_ENABLE and 
                        (not cmp_cnt_word_max);

   last_word_valid   <= cmp_cnt_word_max and (not TX_DST_RDY_N);
   
   -- output ports
   LAST_WORD         <= last_word_valid;
   TX_DATA           <= mx_tx_data;
   TX_SRC_RDY_N      <= '0';
   TX_REM            <= conv_std_logic_vector(C_TX_REM, TX_REM'length);
   
   GEN_FULL_SENDER: if ((DATA_WIDTH/8) < C_BYTE_MAX) generate
      TX_SOP_N          <= not cmp_cnt_word_min;
      TX_EOP_N          <= not cmp_cnt_word_max;

      -- counter cnt_word 
      cnt_wordp: process (CLK) 
      begin
         if CLK='1' and CLK'event then
            if RESET = '1' or cnt_word_clr = '1' then
               cnt_word <= (others => '0');
            elsif cnt_word_ce = '1' then
               cnt_word <= cnt_word + 1;
            end if;
         end if;
      end process;
   
      -- comparator cmp_cnt_word_min
      cmp_cnt_word_minp : process (cnt_word)
      begin
         if (conv_std_logic_vector('0', cnt_word'length) = cnt_word) then
            cmp_cnt_word_min <= '1';
         else
            cmp_cnt_word_min <= '0';
         end if;
      end process;

      -- comparator cmp_cnt_word_max
      cmp_cnt_word_maxp : process (cnt_word)
      begin
         if (conv_std_logic_vector(C_WORD_COUNT-1, cnt_word'length) = cnt_word) then
            cmp_cnt_word_max <= '1';
         else
            cmp_cnt_word_max <= '0';
         end if;
      end process;
   
      -- get current data word
      TX_DATA_MUX : entity work.GEN_MUX
         generic map(
            DATA_WIDTH  => DATA_WIDTH,
            MUX_WIDTH   => C_WORD_MAX
         )
         port map(
            DATA_IN     => CONSTANT_HW_HEADER_DATA,
            SEL         => cnt_word,
            DATA_OUT    => mx_tx_data
         );
   end generate;

   GEN_LIGHT_SENDER: if ((DATA_WIDTH/8) = C_BYTE_MAX) generate
      cmp_cnt_word_max  <= '1';
      mx_tx_data        <= CONSTANT_HW_HEADER_DATA;

      TX_SOP_N          <= '0';
      TX_EOP_N          <= '0';
   end generate;

   

end architecture full;
