-- 128_to_96.vhd: Convert 128-bit FL to 96-bit FIFO interface
-- Copyright (C) 2009 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--  Entity declaration: CONV_128_TO_96
-- ----------------------------------------------------------------------------
entity CONV_128_TO_96 is
   port(
      -- common signals
      -- global FGPA clock
      CLK            : in  std_logic;

      -- global synchronous reset
      RESET          : in  std_logic;
     
      -- RX Framelink interface
      RX_DATA        : in  std_logic_vector(127 downto 0);
      RX_REM         : in  std_logic_vector(3 downto 0);
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      
      -- Fifo interface
      DATA           : out std_logic_vector(95 downto 0);
      SOF            : out std_logic;
      EOF            : out std_logic;
      VLD            : out std_logic;
      RDY            : in  std_logic
   );
end entity CONV_128_TO_96;

-- ----------------------------------------------------------------------------
--  Architecture: CONV_128_TO_96
-- ----------------------------------------------------------------------------
architecture full of CONV_128_TO_96 is
   type tstates is (START, READ_0, READ_1, READ_2, READ_CONT, STOP_START, STOP_0, STOP_1);
   
   signal current_state          : tstates;
   signal next_state             : tstates;
   
   signal reg_data               : std_logic_vector(127 downto 0);
   signal reg_data_we            : std_logic;
   
   signal mux_sel                : std_logic_vector(2 downto 0);
begin
   -- data register
   register_data: process (CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reg_data <= (others => '0');
         else
            if (reg_data_we = '1') then
               reg_data <= RX_DATA;
            end if;
         end if;
      end if;
   end process register_data;

   -- output data multiplexor
   mult_data_out: process (mux_sel, RX_DATA, reg_data)
   begin
      case mux_sel is
         when "000" =>
            DATA <= RX_DATA(95 downto 0);
         when "001" =>
            DATA <= RX_DATA(63 downto 0) & reg_data(127 downto 96);
         when "010" =>
            DATA <= RX_DATA(31 downto 0) & reg_data(127 downto 64);
         when "011" =>
            DATA <= reg_data(127 downto 32);
         when "100" =>
            DATA <= conv_std_logic_vector(0, 64) & reg_data(127 downto 96);
         when "101" =>
            DATA <= conv_std_logic_vector(0, 32) & reg_data(127 downto 64);
         when "110" =>
            DATA <= conv_std_logic_vector(0, 96);
         when "111" =>
            DATA <= conv_std_logic_vector(0, 96);
         when others => 

      end case;

   end process mult_data_out;

   -- FSM state register
   state_register: process (RESET, CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            current_state <= START;
         else
            current_state <= next_state;
         end if;
      end if;
   end process state_register;

   -- transitions in FSM
   transitions_FSM: process (current_state, RX_SRC_RDY_N, RDY, RX_SOF_N, RX_EOF_N, RX_REM)
   begin
      next_state <= current_state;
      case current_state is
         when START =>
            if (RX_SRC_RDY_N = '0' and RDY = '1' and RX_SOF_N = '0') then
               if (RX_EOF_N = '1') then
                  next_state <= READ_0;
               else
                  if (RX_REM > X"B") then
                     next_state <= STOP_START;
                  else
                     next_state <= START;
                  end if;
               end if;
            else
               next_state <= current_state;
            end if;
         when READ_0 =>
            if (RX_SRC_RDY_N = '0' and RDY = '1') then
               if (RX_EOF_N = '1') then
                  next_state <= READ_1;
               else
                  if (RX_REM > X"7") then
                     next_state <= STOP_0;
                  else
                     next_state <= START;
                  end if;
               end if;
            else
               next_state <= current_state;
            end if;
         when READ_1 =>
            if (RX_SRC_RDY_N = '0' and RDY = '1') then
               if (RX_EOF_N = '1') then
                  next_state <= READ_2;
               else
                  if (RX_REM > X"3") then
                     next_state <= STOP_1;
                  else
                     next_state <= START;
                  end if;
               end if;
            else
               next_state <= current_state;
            end if;
         when READ_2 =>
            if (RDY = '1') then
               --if (RX_EOF_N = '1') then
                  next_state <= READ_CONT;
               --else
               --   next_state <= START;
               --end if;
            else
               next_state <= current_state;
            end if;
         when READ_CONT =>
            if (RX_SRC_RDY_N = '0' and RDY = '1') then
               if (RX_EOF_N = '1') then
                  next_state <= READ_0;
               else
                  if (RX_REM > X"B") then
                     next_state <= STOP_START;
                  else
                     next_state <= START;
                  end if;
               end if;
            else
               next_state <= current_state;
            end if;
         when STOP_START =>
            if (RDY = '1') then
               next_state <= START;
            else
               next_state <= current_state;
            end if;
         when STOP_0 =>
            if (RDY = '1') then
               next_state <= START;
            else
               next_state <= current_state;
            end if;
         when STOP_1 =>
            if (RDY = '1') then
               next_state <= START;
            else
               next_state <= current_state;
            end if;
         when others =>
      end case;
   end process transitions_FSM;

   -- outputs of FSM
   outputs_FSM: process (current_state, RX_SRC_RDY_N, RDY, RX_SOF_N, RX_EOF_N, RX_REM)
   begin
      mux_sel <= "111";
      VLD <= '0';
      RX_DST_RDY_N <= '1';
      reg_data_we <= '0';
      SOF <= '0';
      EOF <= '0';
      
      case current_state is
         when START =>
            if (RX_SRC_RDY_N = '0' and RDY = '1' and RX_SOF_N = '0') then
               mux_sel <= "000";
               VLD <= '1';
               SOF <= '1';
               RX_DST_RDY_N <= '0';
               reg_data_we <= '1';
               if (RX_EOF_N = '0' and not (RX_REM > X"B")) then
                  EOF <= '1';
               end if;
            else
               if (RX_SRC_RDY_N = '1' and RDY = '0') then
                  RX_DST_RDY_N <= '1';
                  VLD <= '0';
               end if;
               if (RX_SRC_RDY_N = '1' and RDY = '1') then
                  RX_DST_RDY_N <= '0';
                  VLD <= '0';
               end if;
               if (RX_SRC_RDY_N = '0' and RDY = '0') then
                  RX_DST_RDY_N <= '1';
                  VLD <= '0';
               end if;
               if (RX_SRC_RDY_N = '0' and RDY = '1' and RX_SOF_N = '1') then
                  RX_DST_RDY_N <= '0';
                  VLD <= '0';
               end if;
            end if;
         when READ_0 =>
            if (RX_SRC_RDY_N = '0' and RDY = '1') then
               mux_sel <= "001";
               VLD <= '1';
               RX_DST_RDY_N <= '0';
               reg_data_we <= '1';
               if (RX_EOF_N = '0' and not (RX_REM > X"7")) then
                  EOF <= '1';
               end if;
            else
               if (RX_SRC_RDY_N = '0' and RDY = '0') then
                  RX_DST_RDY_N <= '1';
                  VLD <= '0';
               end if;
               if (RX_SRC_RDY_N = '1' and RDY = '1') then
                  RX_DST_RDY_N <= '0';
                  VLD <= '0';
               end if;
               if (RX_SRC_RDY_N = '1' and RDY = '0') then
                  RX_DST_RDY_N <= '1';
                  VLD <= '0';
               end if;
            end if;
         when READ_1 =>
            if (RX_SRC_RDY_N = '0' and RDY = '1') then
               mux_sel <= "010";
               VLD <= '1';
               RX_DST_RDY_N <= '0';
               reg_data_we <= '1';
               if (RX_EOF_N = '0' and not (RX_REM > X"3")) then
                  EOF <= '1';
               end if;
            else
               if (RX_SRC_RDY_N = '0' and RDY = '0') then
                  RX_DST_RDY_N <= '1';
                  VLD <= '0';
               end if;
               if (RX_SRC_RDY_N = '1' and RDY = '1') then
                  RX_DST_RDY_N <= '0';
                  VLD <= '0';
               end if;
               if (RX_SRC_RDY_N = '1' and RDY = '0') then
                  RX_DST_RDY_N <= '1';
                  VLD <= '0';
               end if;
            end if;
         when READ_2 =>
            if (RDY = '1') then
               mux_sel <= "011";
               VLD <= '1';
               RX_DST_RDY_N <= '1';
            else
               RX_DST_RDY_N <= '1';
               VLD <= '0';
            end if;
         when STOP_START =>
            if (RDY = '1') then
               mux_sel <= "100";
               EOF <= '1';
               VLD <= '1';
               RX_DST_RDY_N <= '1';
            else
               VLD <= '0';
               RX_DST_RDY_N <= '1';
            end if;
         when STOP_0 =>
            if (RDY = '1') then
               mux_sel <= "101";
               EOF <= '1';
               VLD <= '1';
               RX_DST_RDY_N <= '1';
            else
               VLD <= '0';
               RX_DST_RDY_N <= '1';
            end if;
         when STOP_1 =>
            if (RDY = '1') then
               mux_sel <= "011";
               EOF <= '1';
               VLD <= '1';
               RX_DST_RDY_N <= '1';
            else
               VLD <= '0';
               RX_DST_RDY_N <= '1';
            end if;
         when READ_CONT =>
         if (RX_SRC_RDY_N = '0' and RDY = '1') then
               mux_sel <= "000";
               VLD <= '1';
               RX_DST_RDY_N <= '0';
               reg_data_we <= '1';
               if (RX_EOF_N = '0' and not (RX_REM > X"B")) then
                  EOF <= '1';
               end if;
            else
               if (RX_SRC_RDY_N = '0' and RDY = '0') then
                  RX_DST_RDY_N <= '1';
                  VLD <= '0';
               end if;
               if (RX_SRC_RDY_N = '1' and RDY = '1') then
                  RX_DST_RDY_N <= '0';
                  VLD <= '0';
               end if;
               if (RX_SRC_RDY_N = '1' and RDY = '0') then
                  RX_DST_RDY_N <= '1';
                  VLD <= '0';
               end if;
            end if;
         when others =>
      end case;
   end process outputs_FSM;

end architecture full;
