-- crc_shift.vhd: CRC_shift component from xgmii_enc part of XGMII OBUF
-- Copyright (C) 2008 CESNET
-- Author(s): Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
--            Libor Polcak <polcak_l@liberouter.org>
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


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.xgmii_pkg.all;

-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------
entity crc_shift is

   port(
      -- Clock signal
      CLK               : in std_logic;
      -- Synchronous reset
      RESET             : in std_logic;

      ----- CRC_shift inputs -----
      -- CRC
      CRC_DI            : in std_logic_vector(31 downto 0);

      -- control signals
      CE                : in std_logic;

      -- CRC position
      CNT               : in std_logic_vector(2 downto 0);

      ----- CRC_shift outputs -----
      DO                : out std_logic_vector(63 downto 0);
      DO_CMD            : out std_logic_vector(7 downto 0);

      -- last word with CRC
      LAST              : out std_logic
   );

end entity crc_shift;


-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture crc_shift_arch of crc_shift is
   
   -- constant for zero word (64b)
   constant ZERO_WORD   : std_logic_vector(63 downto 0) := (others => 'X');

   -- fsm states type
   --type state_type is (s_init, s_loaded_crc, s_crc_word_1, s_crc_word_2);
   type state_type is (s_init, s_crc_word_2);

   -- fsm states
   signal present_state, next_state : state_type;
   
   -- fsm outputs (that are not among crc_shift ports)
   signal word_2           : std_logic_vector(0 downto 0);

   -- barrel shifter outputs
   -- 127 downto 64 = crc_word_2
   -- 63 downto 0 = crc_word_1
   signal crc_word         : std_logic_vector(127 downto 0);
   signal reg_crc_word_2   : std_logic_vector(63 downto 0);
   signal mx_crc_data      : std_logic_vector(127 downto 0);
   -- 15 downto 8 = cmd_word_2
   -- 7 downto 0 = cmd_word_1
   signal cmd_word         : std_logic_vector(15 downto 0);
   signal reg_cmd_word_2   : std_logic_vector(7 downto 0);
   signal mx_cmd_data      : std_logic_vector(15 downto 0);

begin

   -- -------------------------------------------------------------------------
   --                               FSM
   -- -------------------------------------------------------------------------

   -- Present state logic -----------------------------------------------------
   present_state_logic : process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (RESET='1') then
            present_state <= s_init;
         else
            present_state <= next_state;
         end if;
      end if;
   end process present_state_logic;

   -- Next state logic --------------------------------------------------------
   next_state_logic : process (present_state, CE, CNT)
   begin
      case (present_state) is

         -- s_init
         when s_init =>
            if (CE='1' and CNT >= 3) then
               next_state <= s_crc_word_2;
            else
               next_state <= s_init;
            end if;

         -- s_crc_word_2
         when s_crc_word_2 =>
            next_state <= s_init;

         when others =>
            next_state <= s_init;

      end case;
   end process next_state_logic;

   -- Output logic ------------------------------------------------------------
   output_logic : process (present_state, CE, CNT)
   begin
      LAST      <= '0';
      word_2    <= "0";

      case (present_state) is

         -- s_init
         when s_init =>
            if (CE = '1' and CNT < 3) then
               LAST <= '1';
            end if;

         -- s_crc_word_2
         when s_crc_word_2 =>
            LAST <= '1';
            word_2 <= "1";

         -- s_init, s_loaded_crc
         when others =>
            null;

      end case;
   end process output_logic;


   -- -------------------------------------------------------------------------
   --                              Registers
   -- -------------------------------------------------------------------------

   -- reg_crc_word_2
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         reg_crc_word_2 <= crc_word(127 downto 64);
      end if;
   end process;

   -- reg_cmd_word_2
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         reg_cmd_word_2 <= cmd_word(15 downto 8);
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                              Barrel shifter
   -- -------------------------------------------------------------------------

   process (CRC_DI, CNT)
   begin
      case (CNT) is
         when "000" =>
            crc_word <= ZERO_WORD &
			               C_XGMII_IDLE & C_XGMII_IDLE &
                        C_XGMII_TERMINATE &
                        CRC_DI &
                        (7 downto 0 => 'X');
            cmd_word <= X"FFE0";
         when "001" =>
            crc_word <= ZERO_WORD &
			               C_XGMII_IDLE &
                        C_XGMII_TERMINATE &
                        CRC_DI &
                        (15 downto 0 => 'X');
            cmd_word <= X"FFC0";
         when "010" =>
            crc_word <= ZERO_WORD &
                        C_XGMII_TERMINATE &
                        CRC_DI &
                        (23 downto 0 => 'X');
            cmd_word <= X"FF80";
         when "011" =>
            crc_word <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
			               C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
			               C_XGMII_IDLE &
                        C_XGMII_TERMINATE &
			               CRC_DI &
                        (31 downto 0 => 'X');
            cmd_word <= X"FF00";
         when "100" =>
            crc_word <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
			               C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
                        C_XGMII_TERMINATE &
                        CRC_DI &
                        (39 downto 0 => 'X');
            cmd_word <= X"FE00";
         when "101" =>
            crc_word <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
			               C_XGMII_IDLE & C_XGMII_IDLE &
                        C_XGMII_TERMINATE &
                        CRC_DI &
                        (47 downto 0 => 'X');
            cmd_word <= X"FC00";
         when "110" =>
            crc_word <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
			               C_XGMII_IDLE &
                        C_XGMII_TERMINATE &
                        CRC_DI &
                        (55 downto 0 => 'X');
            cmd_word <= X"F800";
         when "111" =>
            crc_word <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
                        C_XGMII_TERMINATE &
                        CRC_DI &
                        (63 downto 0 => 'X');
            cmd_word <= X"F000";
         when others =>
            crc_word <= (others => 'X');
            cmd_word <= (others => 'X');
      end case;
   end process;
   
   -- -------------------------------------------------------------------------
   --                              Multiplexers
   -- -------------------------------------------------------------------------

   -- mx_final_crc
   mx_crc_data <= reg_crc_word_2 & crc_word(63 downto 0);
   mx_final_crc: entity work.GEN_MUX
      generic map(
         DATA_WIDTH     => 64,
         MUX_WIDTH      => 2
      )
      port map(
         DATA_IN        => mx_crc_data,
         SEL            => word_2,
         DATA_OUT       => DO
      );

   -- mx_final_cmd
   mx_cmd_data <= reg_cmd_word_2 & cmd_word(7 downto 0);
   mx_final_cmd: entity work.GEN_MUX
      generic map(
         DATA_WIDTH     => 8,
         MUX_WIDTH      => 2
      )
      port map(
         DATA_IN        => mx_cmd_data,
         SEL            => word_2,
         DATA_OUT       => DO_CMD
      );

end architecture crc_shift_arch;
