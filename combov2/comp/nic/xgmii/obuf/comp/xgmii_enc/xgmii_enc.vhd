-- xgmii_enc.vhd: Architecture of XGMII OBUF's xgmii_enc part
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
-- TODO: Minimum IFG = 96 octets
--
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.xgmii_pkg.all;
use work.xgmii_enc_pkg.all;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture xgmii_obuf_xgmii_enc_arch of xgmii_obuf_xgmii_enc is

   -- FSM
   signal fsm_crc_filled_clr  : std_logic;
   signal fsm_shifter_ce      : std_logic;
   signal fsm_dsel_pos        : std_logic_vector(3 downto 0);
   signal fsm_mx_data_sel     : std_logic_vector(2 downto 0);
   signal fsm_rx_rd           : std_logic;

   -- Deficit idle count management
   signal reg_dic                : std_logic_vector(1 downto 0);
   signal reg_dic_we             : std_logic;
   signal new_dic                : std_logic_vector(1 downto 0);
   signal shorter_ifg            : std_logic;
   signal reg_shorter_ifg        : std_logic;
   signal reg_dic_mode           : std_logic;
   signal reg_dic_mode_in        : std_logic;
   signal reg_dic_mode_we        : std_logic;
   signal mx_dic_mode_in         : std_logic;
   signal reg_next_dic_mode      : std_logic;
   signal reg_next_dic_mode_in   : std_logic;
   signal reg_next_dic_mode_we   : std_logic;
   signal reg_set_next_dic_mode  : std_logic;

   -- crc_shift outputs
   signal crc_shift_do        : std_logic_vector(63 downto 0);
   signal crc_shift_do_cmd    : std_logic_vector(7 downto 0);
   signal crc_shift_last      : std_logic;

   -- data_sel outputs
   signal data_sel_do         : std_logic_vector(63 downto 0);
   signal data_sel_do_cmd     : std_logic_vector(7 downto 0);

   -- Registers
   signal reg0_data           : std_logic_vector(63 downto 0);
   signal reg0_crc_shift_do   : std_logic_vector(63 downto 0);
   signal reg0_crc_shift_do_cmd: std_logic_vector(7 downto 0);
   signal reg0_fsm_dsel_pos   : std_logic_vector(3 downto 0);
   signal reg0_fsm_mx_data_sel: std_logic_vector(2 downto 0);

   signal reg1_data           : std_logic_vector(63 downto 0);
   signal reg1_data_sel       : std_logic_vector(2 downto 0);
   signal reg1_cmd            : std_logic_vector(7 downto 0);
   signal reg2_data           : std_logic_vector(31 downto 0);
   signal reg2_cmd            : std_logic_vector(3 downto 0);
   
   -- Multiplexers input
   signal sig_c_xgmii_error   : std_logic_vector(63 downto 0);
   signal sig_c_xgmii_idle    : std_logic_vector(63 downto 0);

   -- Multiplexers output
   signal mx_data             : std_logic_vector(63 downto 0);
   signal mx_cmd              : std_logic_vector(7 downto 0);

begin

   -- -------------------------------------------------------------------------
   --                        Deficit Idle Count management
   -- -------------------------------------------------------------------------

   reg_dic_mode_in <= not reg_dic_mode;
   reg_next_dic_mode_in <= not reg_dic_mode;

   process(RX_EOP, RX_DV, RX_EOP_POS, reg_dic)
   begin
      reg_dic_we <= '0';
      new_dic <= reg_dic;
      shorter_ifg <= '0';
      reg_dic_mode_we <= '0';
      reg_next_dic_mode_we <= '0';

      if (RX_DV = '1' AND RX_EOP = '1') then
         reg_dic_we <= '1';
         case (RX_EOP_POS) is
            when "000" =>
               if (reg_dic = "00") then
                  shorter_ifg <= '0';
                  reg_dic_mode_we <= '1';
                  new_dic <= "11";
               else
                  shorter_ifg <= '1';
                  new_dic <= reg_dic - 1;
               end if;
            when "001" =>
               if (reg_dic <= "01") then
                  shorter_ifg <= '0';
                  reg_dic_mode_we <= '1';
                  new_dic <= reg_dic + 2;
               else
                  shorter_ifg <= '1';
                  new_dic <= reg_dic - 2;
               end if;
            when "010" =>
               if (reg_dic /= "11") then
                  shorter_ifg <= '0';
                  reg_dic_mode_we <= '1';
                  new_dic <= reg_dic + 1;
               else
                  shorter_ifg <= '1';
                  new_dic <= "00";
               end if;
            when "011" =>
               reg_next_dic_mode_we <= '1';
               shorter_ifg <= '1'; -- because the IFG is performed by word with terminate
            when "100" =>
               if (reg_dic = "00") then
                  shorter_ifg <= '0';
                  new_dic <= "11";
               else
                  shorter_ifg <= '1';
                  reg_next_dic_mode_we <= '1';
                  new_dic <= reg_dic - 1;
               end if;
            when "101" =>
               if (reg_dic <= "01") then
                  shorter_ifg <= '0';
                  new_dic <= reg_dic + 2;
               else
                  shorter_ifg <= '1';
                  reg_next_dic_mode_we <= '1';
                  new_dic <= reg_dic - 2;
               end if;
            when "110" =>
               if (reg_dic /= "11") then
                  shorter_ifg <= '0';
                  new_dic <= reg_dic + 1;
               else
                  shorter_ifg <= '1';
                  reg_next_dic_mode_we <= '1';
                  new_dic <= "00";
               end if;
            when "111" =>
               shorter_ifg <= '0';
            when others =>
         end case;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event AND CLK='1') then
         reg_shorter_ifg <= shorter_ifg;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event AND CLK='1') then
         if (RESET = '1') then
            -- Deficit idle count as specified by the IEE 802.3 standard: DIC = 3 - reg_dic
            reg_dic <= (others => '1');
         elsif (reg_dic_we = '1') then
            reg_dic <= new_dic;
         end if;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event AND CLK='1') then
         if (reg_next_dic_mode_we = '1') then
            reg_next_dic_mode <= reg_next_dic_mode_in;
         end if;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event AND CLK='1') then
         if (RESET = '1') then
            reg_set_next_dic_mode <= '0';
         else
            reg_set_next_dic_mode <= reg_next_dic_mode_we;
         end if;
      end if;
   end process;

   process(reg_dic_mode_in, reg_next_dic_mode, reg_dic_mode_we)
   begin
      if (reg_dic_mode_we = '1') then
         mx_dic_mode_in <= reg_dic_mode_in;
      else
         mx_dic_mode_in <= reg_next_dic_mode;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event AND CLK='1') then
         if (RESET = '1') then
            reg_dic_mode <= '0';
         elsif (reg_dic_mode_we = '1' or reg_set_next_dic_mode = '1') then
            reg_dic_mode <= mx_dic_mode_in;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                               FSM instantion
   -- -------------------------------------------------------------------------

   fsm: entity work.xgmii_obuf_xgmii_enc_fsm

      port map(
         CLK                  => CLK,
         RESET                => RESET,

         -- Inputs
         SHIFTER_LAST         => crc_shift_last,
         RX_SOP               => RX_SOP,
         RX_EOP               => RX_EOP,
         RX_DV                => RX_DV,
         RX_EOP_POS           => RX_EOP_POS,
         DIC_MODE             => reg_dic_mode,
         DIC_SHORTER_IFG      => reg_shorter_ifg,

         -- Outputs
         FSM_CRC_FILLED_CLR   => fsm_crc_filled_clr,
         FSM_SHIFTER_CE       => fsm_shifter_ce,
         FSM_DSEL_POS         => fsm_dsel_pos,
         FSM_MX_DATA_SEL      => fsm_mx_data_sel,
         FSM_RX_RD            => fsm_rx_rd
      );


   -- -------------------------------------------------------------------------
   --                           CRC_shift instantion
   -- -------------------------------------------------------------------------

   crc_shift: entity work.crc_shift

      port map(
         CLK                  => CLK,
         RESET                => RESET,
         
         -- Inputs
         CRC_DI               => RX_CRC,
         CE                   => fsm_shifter_ce,
         CNT                  => RX_EOP_POS,
         
         -- Outputs
         DO                   => crc_shift_do,
         DO_CMD               => crc_shift_do_cmd,
         LAST                 => crc_shift_last
      );


   -- -------------------------------------------------------------------------
   --                          Pipeline - stage 0
   -- -------------------------------------------------------------------------

   process(CLK)
   begin
      if (CLK='1' and CLK'event) then
         reg0_data <= RX_DATA;
         reg0_crc_shift_do <= crc_shift_do;
         reg0_crc_shift_do_cmd <= crc_shift_do_cmd;
         reg0_fsm_dsel_pos <= fsm_dsel_pos;
         reg0_fsm_mx_data_sel <= fsm_mx_data_sel;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                               data_sel
   -- -------------------------------------------------------------------------

   process (reg0_data, reg0_crc_shift_do, reg0_fsm_dsel_pos)
   begin
      case (reg0_fsm_dsel_pos) is
         when "0000" => data_sel_do <= reg0_crc_shift_do;
         when "0001" =>
            data_sel_do <= reg0_crc_shift_do(63 downto 8) & reg0_data(7 downto 0);
         when "0010" =>
            data_sel_do <= reg0_crc_shift_do(63 downto 16) & reg0_data(15 downto 0);
         when "0011" =>
            data_sel_do <= reg0_crc_shift_do(63 downto 24) & reg0_data(23 downto 0);
         when "0100" =>
            data_sel_do <= reg0_crc_shift_do(63 downto 32) & reg0_data(31 downto 0);
         when "0101" =>
            data_sel_do <= reg0_crc_shift_do(63 downto 40) & reg0_data(39 downto 0);
         when "0110" =>
            data_sel_do <= reg0_crc_shift_do(63 downto 48) & reg0_data(47 downto 0);
         when "0111" =>
            data_sel_do <= reg0_crc_shift_do(63 downto 56) & reg0_data(55 downto 0);
         when "1000" =>
            data_sel_do <= reg0_data;
         when others =>
            data_sel_do <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
                           C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
                           C_XGMII_IDLE & C_XGMII_IDLE;
      end case;
   end process;

   process (reg0_fsm_dsel_pos, reg0_crc_shift_do_cmd)
   begin
      case (reg0_fsm_dsel_pos) is
         when "1000" =>
            data_sel_do_cmd <= (others => '0');
         when others =>
            data_sel_do_cmd <= reg0_crc_shift_do_cmd;
      end case;
   end process;

   -- -------------------------------------------------------------------------
   --                               Registers
   -- -------------------------------------------------------------------------

   -- reg1_data
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         reg1_data <= data_sel_do;
      end if;
   end process;

   -- reg2_data
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         reg2_data <= reg1_data(63 downto 32);
      end if;
   end process;

   -- reg1_data_sel
   process (CLK, RESET)
   begin
      if (CLK='1' and CLK'event) then
         if (RESET='1') then
            reg1_data_sel <= C_XGMII_ENC_IDLE_IDLE; 	-- idle
         else
            reg1_data_sel <= reg0_fsm_mx_data_sel;
         end if;
      end if;
   end process;
   
   
   -- reg1_cmd
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         reg1_cmd <= data_sel_do_cmd;
      end if;
   end process;

   -- reg2_cmd
   process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         reg2_cmd <= reg1_cmd(7 downto 4);
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                              Multiplexers
   -- -------------------------------------------------------------------------

   sig_c_xgmii_error_gen: for i in 0 to 6 generate
      sig_c_xgmii_error(i*8+7 downto i*8) <= C_XGMII_ERROR; -- error signal
   end generate sig_c_xgmii_error_gen;
   -- eop at the end of the err signal
   sig_c_xgmii_error(63 downto 56) <= C_XGMII_TERMINATE;

   sig_c_xgmii_idle_gen: for i in 0 to 7 generate
	   sig_c_xgmii_idle(i*8+7 downto i*8) <= C_XGMII_IDLE;   -- idle signal
   end generate sig_c_xgmii_idle_gen;

   -- mx_data
   process (reg1_data_sel, reg1_data, reg2_data, sig_c_xgmii_idle, sig_c_xgmii_error)
   begin
      case reg1_data_sel is
         when C_XGMII_ENC_ERR_ERR =>
            mx_data <= sig_c_xgmii_error;
         when C_XGMII_ENC_IDLE_IDLE =>
            mx_data <= sig_c_xgmii_idle;
         when C_XGMII_ENC_IDLE_PREAMD =>
            mx_data(31 downto  0) <= sig_c_xgmii_idle(31 downto 0);
            mx_data(63 downto 32) <= C_PREAMBLE(31 downto 0);
         when C_XGMII_ENC_PREAMU_DATAD =>
            mx_data(31 downto  0) <= C_PREAMBLE(63 downto 32);
            mx_data(63 downto 32) <= reg1_data(31 downto 0);
         when C_XGMII_ENC_DATAU_DATAD =>
            mx_data(31 downto  0) <= reg2_data;
            mx_data(63 downto 32) <= reg1_data(31 downto 0);
         when C_XGMII_ENC_PREAMD_PREAMU =>
            mx_data <= C_PREAMBLE;
         when C_XGMII_ENC_DATAD_DATAU =>
            mx_data <= reg1_data;
         when C_XGMII_ENC_DATAU_IDLE =>
            mx_data(31 downto  0) <= reg2_data;
            mx_data(63 downto 32) <= sig_c_xgmii_idle(63 downto 32);
         when others =>
            mx_data <= sig_c_xgmii_idle;
      end case;
   end process;
   
   
   -- mx_cmd
   process (reg1_data_sel, reg1_cmd, reg2_cmd)
   begin
      case reg1_data_sel is
         when C_XGMII_ENC_ERR_ERR => mx_cmd <= X"FF";  -- error is over whole word
         when C_XGMII_ENC_IDLE_IDLE => mx_cmd <= X"FF"; -- idle is over whole word
         when C_XGMII_ENC_IDLE_PREAMD => mx_cmd <= X"1F";
         when C_XGMII_ENC_PREAMU_DATAD =>
            mx_cmd(3 downto 0) <= X"0";
            mx_cmd(7 downto 4) <= reg1_cmd(3 downto 0);
         when C_XGMII_ENC_DATAU_DATAD =>
            mx_cmd(3 downto 0) <= reg2_cmd;
            mx_cmd(7 downto 4) <= reg1_cmd(3 downto 0);
         when C_XGMII_ENC_PREAMD_PREAMU => mx_cmd <= X"01"; -- preamble
         when C_XGMII_ENC_DATAD_DATAU => mx_cmd <= reg1_cmd;
         when C_XGMII_ENC_DATAU_IDLE => mx_cmd <= X"F" & reg2_cmd;
         when others => null;
      end case;
   end process;


   -- -------------------------------------------------------------------------
   --                           XGMII_enc outputs
   -- -------------------------------------------------------------------------

   RX_DATA_READ   <= fsm_rx_rd;

   TX_DATA        <= mx_data;
   TX_CMD         <= mx_cmd;

end architecture xgmii_obuf_xgmii_enc_arch;
