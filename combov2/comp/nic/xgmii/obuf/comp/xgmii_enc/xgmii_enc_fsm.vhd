-- xgmii_enc_fsm.vhd: XGMII OBUF's XGMII encoder FSM
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
use work.xgmii_enc_pkg.all;


-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------

entity xgmii_obuf_xgmii_enc_fsm is

   port(
      -- Clock
      CLK               : in std_logic;
      -- Synchronous reset
      RESET             : in std_logic;

      -- Inputs
      SHIFTER_LAST         : in std_logic;
      RX_SOP               : in std_logic;
      RX_EOP               : in std_logic;
      RX_DV                : in std_logic;
      RX_EOP_POS           : in std_logic_vector(2 downto 0);
      -- Current DIC mode (0: normal, 1: shifted)
      DIC_MODE             : in std_logic;
      -- If active, the ifg is shorter
      DIC_SHORTER_IFG      : in std_logic;

      -- Outputs
      FSM_CRC_FILLED_CLR   : out std_logic;
      FSM_SHIFTER_CE       : out std_logic;
      -- word is composed from FSM_DSEL_POS data bytes, rest of the word is CRC
      FSM_DSEL_POS         : out std_logic_vector(3 downto 0);
      FSM_MX_DATA_SEL      : out std_logic_vector(2 downto 0);
      FSM_RX_RD            : out std_logic
   );

end entity xgmii_obuf_xgmii_enc_fsm;


-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture xgmii_obuf_xgmii_enc_fsm_arch of xgmii_obuf_xgmii_enc_fsm is

   -- fsmrx states type
   type state_type is (s_wait_for_pream, s_data, s_end, s_ifg, s_ldata_ifg, s_err);

   -- fsmrx states
   signal present_state, next_state : state_type;
   
begin

   -- Present state logic -----------------------------------------------------
   present_state_logic : process (CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (RESET='1') then
            present_state <= s_wait_for_pream;
         else
            present_state <= next_state;
         end if;
      end if;
   end process present_state_logic;

   -- Next state logic --------------------------------------------------------
   next_state_logic : process (present_state, RX_SOP, RX_EOP, SHIFTER_LAST,
                               RX_DV, DIC_SHORTER_IFG, DIC_MODE)
   begin
      case (present_state) is

         -- s_wait_for_pream
         when s_wait_for_pream =>
            if (RX_SOP='0') then
               next_state <= s_wait_for_pream;
            else
               next_state <= s_data;
            end if;

         -- s_data
         when s_data =>
            if (RX_DV='0') then
               next_state <= s_err;
            elsif (RX_EOP='0') then
               next_state <= s_data;
            elsif (RX_EOP='1' and SHIFTER_LAST='1') then
               if (DIC_MODE='0') then
                  next_state <= s_ifg;
               else
                  next_state <= s_ldata_ifg;
               end if;
            else
               next_state <= s_end;
            end if;

         -- s_end
         when s_end =>
            if (DIC_MODE='1') then
               if (DIC_SHORTER_IFG='1') then
                  next_state <= s_ifg;
               else
                  next_state <= s_ldata_ifg;
               end if;
            else
               if (DIC_SHORTER_IFG='1') then
                  next_state <= s_wait_for_pream;
               else
                  next_state <= s_ifg;
               end if;
            end if;

         -- s_err
         when s_err =>
            if RX_EOP = '1' then
               next_state <= s_ifg;
            else
               next_state <= s_err;
            end if;

         -- s_ifg - interframe gap
         when s_ifg =>
            next_state <= s_wait_for_pream;

         -- s_ldata_ifg - last 1-4 octets of data and interframe gap
         when s_ldata_ifg =>
            if (DIC_MODE = '0') then
               next_state <= s_ifg;
            else
               next_state <= s_wait_for_pream;
            end if;

      end case;
   end process next_state_logic;

   -- Output logic ------------------------------------------------------------
   output_logic : process (present_state, RX_SOP, RX_EOP, RX_EOP_POS, RX_DV,
                           SHIFTER_LAST, RESET, DIC_MODE)

   begin
      FSM_CRC_FILLED_CLR   <= '0';
      FSM_SHIFTER_CE       <= '0';
      FSM_DSEL_POS         <= "1000";     -- word full of data
      FSM_MX_DATA_SEL      <= C_XGMII_ENC_IDLE_IDLE;
      FSM_RX_RD            <= '0';

      case (present_state) is

         -- s_wait_for_pream
         when s_wait_for_pream =>
            FSM_CRC_FILLED_CLR <= '1';
            if (RX_SOP='1') then
               if (DIC_MODE = '0') then
                  FSM_MX_DATA_SEL <= C_XGMII_ENC_PREAMD_PREAMU;
               else
                  FSM_MX_DATA_SEL <= C_XGMII_ENC_IDLE_PREAMD;
               end if;
               --FSM_SHIFTER_CE <= '1';
            end if;

         -- s_data
         when s_data =>
            FSM_RX_RD <= '1';
            if (DIC_MODE = '0') then
               FSM_MX_DATA_SEL <= C_XGMII_ENC_DATAD_DATAU;
            else
               if RX_SOP = '1' then
                  FSM_MX_DATA_SEL <= C_XGMII_ENC_PREAMU_DATAD;
               else
                  FSM_MX_DATA_SEL <= C_XGMII_ENC_DATAU_DATAD;
               end if;
            end if;
            if (RX_EOP = '1') then
               FSM_SHIFTER_CE <= '1';
               if RX_EOP_POS /= "111" then
                  FSM_DSEL_POS <= '0' & (RX_EOP_POS + 1);
               end if;
            end if;
            if (RX_DV='0') then
               FSM_MX_DATA_SEL <= C_XGMII_ENC_ERR_ERR;
               FSM_RX_RD <= '0';
            end if;

         -- s_end
         when s_end =>
            FSM_RX_RD <= '0';
            FSM_SHIFTER_CE <= '1';
            if (DIC_MODE = '0') then
               FSM_MX_DATA_SEL <= C_XGMII_ENC_DATAD_DATAU;
            else
               FSM_MX_DATA_SEL <= C_XGMII_ENC_DATAU_DATAD;
            end if;
            FSM_DSEL_POS <= "0000";

         -- s_err
         when s_err =>
            FSM_RX_RD <= '1';

         -- s_ifg - interframe gap
         when s_ifg =>
            FSM_RX_RD <= '0';
            FSM_CRC_FILLED_CLR <= '1';

         -- s_ldata_ifg - last 1-4 octets of data and interframe gap
         when s_ldata_ifg =>
            FSM_MX_DATA_SEL <= C_XGMII_ENC_DATAU_IDLE;
            FSM_RX_RD <= '0';
            FSM_CRC_FILLED_CLR <= '1';

      end case;
   end process output_logic;

end architecture xgmii_obuf_xgmii_enc_fsm_arch;
   
