-- xgmii_dec.vhd: Decodes the Aligned SDR XGMII protocol
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture XGMII_DEC_ARCH of XGMII_DEC is

   -- Signals declaration
   signal mask_term                 : std_logic_vector(7 downto 0);
   signal mask_cmd                  : std_logic_vector(7 downto 0);
   signal reg1_term_active          : std_logic_vector(7 downto 0);
   signal reg1_sop                  : std_logic;
   signal reg1_cmd_mask             : std_logic_vector(7 downto 0);
   signal reg1_preamble_ok_in       : std_logic;
   signal reg1_preamble_ok          : std_logic;

   signal pdec_term_pos             : std_logic_vector(7 downto 0);
   signal pdec_term_ok              : std_logic_vector(7 downto 0);
   signal reg2_pdec_do              : std_logic_vector(7 downto 0);
   signal reg2_term_in              : std_logic;
   signal reg2_term                 : std_logic;
   signal reg2_eop_pos              : std_logic_vector(7 downto 0);
   signal reg2_sop                  : std_logic;
   signal reg2_preamble_ok          : std_logic;
   signal reg2_cmd_mask             : std_logic_vector(7 downto 0);

   signal error_mask                : std_logic_vector(7 downto 0);
   signal reg3_term_ok_in           : std_logic;
   signal reg3_term_ok              : std_logic;
   signal reg3_term                 : std_logic;
   signal term_shift                : std_logic;
   signal reg3_eop_pos_in           : std_logic_vector(log2(8)-1 downto 0);
   signal reg3_eop_pos              : std_logic_vector(log2(8)-1 downto 0);
   signal reg3_sop                  : std_logic;
   signal cmd_non_first             : std_logic_vector(7 downto 0);
   signal cmd_non_first_present_n   : std_logic;
   signal reg3_sop_ok_in            : std_logic;
   signal reg3_sop_ok               : std_logic;
   signal reg3_cmd_in               : std_logic;
   signal reg3_cmd                  : std_logic;

   signal reg4_term_ok              : std_logic;
   signal reg4_term                 : std_logic;
   signal reg4_eop_pos              : std_logic_vector(2 downto 0);
   signal reg4_sop                  : std_logic;
   signal reg4_sop_ok               : std_logic;
   signal reg4_cmd                  : std_logic;

   signal mx_termok_shift_in_0      : std_logic;
   signal mx_termok_shift_in_1      : std_logic;
   signal mx_termok_shift           : std_logic;
   signal reg5_eop_ok               : std_logic;
   signal mx_term_shift             : std_logic;
   signal reg5_eop                  : std_logic;
   signal mx_eop_shift              : std_logic_vector(2 downto 0);
   signal reg5_eop_pos              : std_logic_vector(2 downto 0);
   signal reg5_sop                  : std_logic;
   signal reg5_sop_ok               : std_logic;
   signal reg5_cmd                  : std_logic;

   signal reg6_data                 : std_logic_vector(63 downto 0);
   signal reg6_eop                  : std_logic;
   signal reg6_eop_pos              : std_logic_vector(2 downto 0);
   signal reg6_sop                  : std_logic;
   signal reg6_err_in               : std_logic;
   signal reg6_err                  : std_logic;

begin
   -- mask_term generator
   mask_term_gen: for i in 0 to 7 generate
   begin
      mask_termp: process(RXD_ALIGNED((i+1)*8-1 downto i*8))
      begin
         if (RXD_ALIGNED((i+1)*8-1 downto i*8) = C_XGMII_TERMINATE) then
            mask_term(i) <= '1';
         else
            mask_term(i) <= '0';
         end if;
      end process;
   end generate mask_term_gen;


   -- mask_cmd assignment
   mask_cmd <= RXC_ALIGNED;


   -- -------------------------------------------------------------------------
   --                       1st pipeline stage
   -- -------------------------------------------------------------------------
   -- register reg1_term_active
   reg1_term_activep: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg1_term_active <= mask_cmd and mask_term;
      end if;
   end process;


   -- register reg1_sop
   reg1_sopp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg1_sop <= SOP_ALIGNED;
      end if;
   end process;

   -- register reg1_cmd_mask
   reg1_cmd_maskp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg1_cmd_mask <= mask_cmd;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                       2nd pipeline stage
   -- -------------------------------------------------------------------------
   -- priority decoder pdec_term_pos and pdec_term_ok
   pdec2e: entity work.xgmii_dec_pdec
   port map(
      -- Input
      DI                => reg1_term_active,
      -- Output
      DO1               => pdec_term_pos,
      DO2               => pdec_term_ok
   );

   -- register reg2_pdec_do
   reg2_pdec_dop: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg2_pdec_do <= pdec_term_ok;
      end if;
   end process;


   -- reg2_term input logic
   reg2_term_inp: process(reg1_term_active)
   begin
      if (reg1_term_active /= X"00") then
         reg2_term_in <= '1';
      else
         reg2_term_in <= '0';
      end if;
   end process;

   -- register reg2_term
   reg2_termp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg2_term <= reg2_term_in;
      end if;
   end process;


   -- register reg2_eop_pos
   reg2_eop_posp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg2_eop_pos <= pdec_term_pos(0) & pdec_term_pos(7 downto 1);
      end if;
   end process;


   -- register reg2_sop
   reg2_sopp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg2_sop <= reg1_sop;
      end if;
   end process;


   -- reg1_preamble_ok input logic
   reg1_preamble_ok_inp: process(RXD_ALIGNED)
   begin
      if (RXD_ALIGNED = C_PREAMBLE) then
         reg1_preamble_ok_in <= '1';
      else
         reg1_preamble_ok_in <= '0';
      end if;
   end process;

   -- register reg1_preamble_ok
   reg1_preamble_okp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg1_preamble_ok <= reg1_preamble_ok_in;
      end if;
   end process;


   -- register reg2_preamble_ok
   reg2_preamble_okp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg2_preamble_ok <= reg1_preamble_ok;
      end if;
   end process;

   
   -- register reg2_cmd_mask
   reg2_cmd_maskp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg2_cmd_mask <= reg1_cmd_mask;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                       3rd pipeline stage
   -- -------------------------------------------------------------------------
   -- reg3_term_ok input logic
   error_mask <= reg2_pdec_do and reg2_cmd_mask;

   reg3_term_ok_inp: process(error_mask)
   begin
      if (error_mask = X"00") then
         reg3_term_ok_in <= '1';
      else
         reg3_term_ok_in <= '0';
      end if;
   end process;

   -- register reg3_term_ok
   reg3_term_okp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg3_term_ok <= reg3_term_ok_in;
      end if;
   end process;

   
   -- register reg3_term
   reg3_termp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg3_term <= reg2_term;
      end if;
   end process;


   -- term_shift shift register
   term_shift_sh_reg: entity work.sh_reg
      generic map(
         NUM_BITS             => 2,
         INIT                 => X"0000"
      )
      port map(
         CLK                  => CLK,
         DIN                  => reg1_term_active(0),
         CE                   => '1',
         DOUT                 => term_shift
      );


   -- reg3_eop_pos input logic
   -- binary encoder
   bin_enc: entity work.GEN_ENC
      generic map(
         ITEMS                => 8
      )
      port map(
         DI                   => reg2_eop_pos,
         ADDR                 => reg3_eop_pos_in
      );

   -- register reg3_eop_pos
   reg3_eop_posp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg3_eop_pos <= reg3_eop_pos_in;
      end if;
   end process;


   -- register reg3_sop
   reg3_sopp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg3_sop <= reg2_sop;
      end if;
   end process;


   -- register reg3_sop_ok input logic
   cmd_non_first <= reg2_cmd_mask and "11111110";

   cmd_non_first_present_np: process(cmd_non_first)
   begin
      if (cmd_non_first = X"00") then
         cmd_non_first_present_n <= '1';
      else
         cmd_non_first_present_n <= '0';
      end if;
   end process;
   
   reg3_sop_ok_in <= cmd_non_first_present_n and reg2_preamble_ok;

   -- register reg3_sop_ok
   reg3_sop_okp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg3_sop_ok <= reg3_sop_ok_in;
      end if;
   end process;


   -- register reg3_cmd input logic
   reg3_cmd_inp: process(reg2_cmd_mask)
   begin
      if (reg2_cmd_mask /= X"00") then
         reg3_cmd_in <= '1';
      else
         reg3_cmd_in <= '0';
      end if;
   end process;

   -- register reg3_cmd
   reg3_cmdp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg3_cmd <= reg3_cmd_in;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                       4th pipeline stage
   -- -------------------------------------------------------------------------
   -- register reg4_term_ok
   reg4_term_okp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg4_term_ok <= reg3_term_ok;
      end if;
   end process;

   -- register reg4_term
   reg4_termp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg4_term <= reg3_term;
      end if;
   end process;

   -- register reg4_eop_pos
   reg4_eop_posp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg4_eop_pos <= reg3_eop_pos;
      end if;
   end process;

   -- register reg4_sop
   reg4_sopp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg4_sop <= reg3_sop;
      end if;
   end process;

   -- register reg4_sop_ok
   reg4_sop_okp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg4_sop_ok <= reg3_sop_ok;
      end if;
   end process;

   -- register reg4_cmd
   reg4_cmdp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg4_cmd <= reg3_cmd;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                       5th pipeline stage
   -- -------------------------------------------------------------------------
   -- register reg5_eop_ok input logic
   mx_termok_shift_in_1 <= ((not reg4_cmd) and reg3_term_ok);
   mx_termok_shift_in_0 <= reg4_term_ok;

   -- multiplexor mx_termok_shift
   mx_termok_shiftp: process(term_shift, mx_termok_shift_in_0,
                             mx_termok_shift_in_1)
   begin
      case term_shift is
         when '0' => mx_termok_shift <= mx_termok_shift_in_0;
         when '1' => mx_termok_shift <= mx_termok_shift_in_1;
         when others => mx_termok_shift <= 'X';
      end case;
   end process;

   -- register reg5_eop_ok
   reg5_eop_okp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg5_eop_ok <= mx_termok_shift;
      end if;
   end process;


   -- multiplexor mx_term_shift
   mx_term_shiftp: process(term_shift, reg3_term, reg4_term)
   begin
      case term_shift is
         when '0' => mx_term_shift <= reg4_term;
         when '1' => mx_term_shift <= reg3_term;
         when others => mx_term_shift <= 'X';
      end case;
   end process;

   -- register reg5_eop
   reg5_eopp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg5_eop <= mx_term_shift;
      end if;
   end process;


   -- multiplexor mx_eop_shift
   mx_eop_shiftp: process(term_shift, reg3_eop_pos, reg4_eop_pos)
   begin
      case term_shift is
         when '0' => mx_eop_shift <= reg4_eop_pos;
         when '1' => mx_eop_shift <= reg3_eop_pos;
         when others => mx_eop_shift <= (others => 'X');
      end case;
   end process;

   -- register reg5_eop_pos
   reg5_eop_posp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg5_eop_pos <= mx_eop_shift;
      end if;
   end process;


   -- register reg5_sop
   reg5_sopp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg5_sop <= reg4_sop;
      end if;
   end process;


   -- register reg5_sop_ok
   reg5_sop_okp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg5_sop_ok <= reg4_sop_ok;
      end if;
   end process;


   -- register reg5_cmd
   reg5_cmdp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg5_cmd <= reg4_cmd;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                       6th pipeline stage
   -- -------------------------------------------------------------------------
   -- Data shift register
   data_sh_reg: entity work.sh_reg_bus
      generic map(
         NUM_BITS             => 6,
         DATA_WIDTH           => 64
      )
      port map(
         CLK                  => CLK,
         DIN                  => RXD_ALIGNED,
         CE                   => '1',
         DOUT                 => reg6_data
      );


   -- register reg6_eop
   reg6_eopp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg6_eop <= reg5_eop;
      end if;
   end process;


   -- register reg6_eop_pos
   reg6_eop_posp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg6_eop_pos <= reg5_eop_pos;
      end if;
   end process;


   -- register reg6_sop
   reg6_sopp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg6_sop <= reg5_sop;
      end if;
   end process;


   -- register reg6_err input logic
   reg6_err_in <= (reg5_sop and (not reg5_sop_ok)) or
                  (not reg5_eop_ok) or
                  (((reg5_sop and reg5_sop_ok) nor (reg5_eop and reg5_eop_ok))
                                                                and reg5_cmd);

   -- register reg6_err
   reg6_errp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg6_err <= reg6_err_in;
      end if;
   end process;

   
   -- -------------------------------------------------------------------------
   --                               FSM
   -- -------------------------------------------------------------------------
   fsmi: entity work.XGMII_DEC_FSM
      port map(
         CLK               => CLK,
         RESET             => RESET,
         SOP_IN            => reg6_sop,
         EOP_IN            => reg6_eop,
         ERR_IN            => reg6_err,
         SOP_OUT           => SOP,
         EOP_OUT           => EOP,
         ERR_OUT           => ERR
     );


   -- -------------------------------------------------------------------------
   --                       Direct output signals
   -- -------------------------------------------------------------------------
   EOP_POS <= reg6_eop_pos;
   DATA <= reg6_data;

end architecture XGMII_DEC_ARCH;
