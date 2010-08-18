-- process_fsmrx.vhd: XGMII OBUF's Process FSMRX
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


-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------

entity obuf_xgmii_process_fsmrx is

   port(
      -- Clock
      CLK               : in std_logic;
      -- Synchronous reset
      RESET             : in std_logic;

      -- Inputs
      LAST_PAD_WORD     : in std_logic_vector(2 downto 0);
      RX_SOP            : in std_logic;
      RX_EOP            : in std_logic;
      RX_DV             : in std_logic;
      PIPE_RD           : in std_logic;

      -- Outputs
      FSMRX_DST_RDY     : out std_logic;
      FSMRX_PADDING     : out std_logic;
      FSMRX_EOP         : out std_logic;
      FSMRX_DV          : out std_logic;
      FSMRX_CNT_PAD_CE  : out std_logic;
      FSMRX_CNT_PAD_LD  : out std_logic
   );

end entity obuf_xgmii_process_fsmrx;


-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture obuf_xgmii_process_fsmrx_arch of obuf_xgmii_process_fsmrx is

   -- fsmrx states type
   type state_type is (s_init, s_crc_pause, s_short_packet, s_long_packet, s_padding);

   -- fsmrx states
   signal present_state, next_state : state_type;

   signal transaction_active        : std_logic;

begin

   transaction_active <= RX_DV and PIPE_RD;

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
   next_state_logic : process (present_state, RX_SOP, RX_EOP, PIPE_RD,
                               transaction_active, LAST_PAD_WORD)
   begin
      case (present_state) is

         -- s_init
         when s_init =>
            if (RX_SOP='1' and transaction_active='1') then
               next_state <= s_short_packet;
            else
               next_state <= s_init;
            end if;

         -- s_crc_pause
         when s_crc_pause =>
            next_state <= s_init;

         -- s_short_packet
         when s_short_packet =>
            next_state <= s_short_packet;
            if transaction_active = '1' then
               if (RX_EOP='0' and LAST_PAD_WORD="111") then
                  next_state <= s_long_packet;
               elsif (RX_EOP='1' and LAST_PAD_WORD/="111") then
                  next_state <= s_padding;
               elsif (RX_EOP='1' and LAST_PAD_WORD="111") then
                  next_state <= s_crc_pause;
               end if;
            end if;

         -- s_long_packet
         when s_long_packet =>
            if (RX_EOP='1' and transaction_active='1') then
               next_state <= s_crc_pause;
            else
               next_state <= s_long_packet;
            end if;

         -- s_padding
         when s_padding =>
            if (LAST_PAD_WORD="111" and PIPE_RD='1') then
               next_state <= s_crc_pause;
            else
               next_state<= s_padding;
            end if;

      end case;
   end process next_state_logic;


   -- Output logic ------------------------------------------------------------
   output_logic : process (present_state, RX_SOP, RX_EOP, transaction_active,
                           PIPE_RD, LAST_PAD_WORD)
   begin
      -- Implicit values (should be changed according to the present_state)
      FSMRX_DV <= transaction_active;
      FSMRX_CNT_PAD_CE <= transaction_active;
      FSMRX_CNT_PAD_LD <= '0';
      FSMRX_PADDING <= '0';
      FSMRX_EOP <= '0';
      FSMRX_DST_RDY <= PIPE_RD;

      case (present_state) is

         -- s_init
         when s_init => null;

         -- s_crc_pause
         when s_crc_pause =>
            FSMRX_DV <= '0';
            FSMRX_CNT_PAD_CE <= '0';
            FSMRX_DST_RDY <= '0';

         -- s_short_packet
         when s_short_packet =>
            if (RX_EOP = '1' and transaction_active='1') then
               FSMRX_PADDING <= '1';
               if (LAST_PAD_WORD = "111") then
                  FSMRX_CNT_PAD_LD <= '1';
                  FSMRX_EOP <= '1';
               end if;
            end if;

         -- s_long_packet
         when s_long_packet =>
            if (RX_EOP = '1' and transaction_active='1') then
               FSMRX_CNT_PAD_LD <= '1';
               FSMRX_EOP <= '1';
            end if;

         -- s_padding
         when s_padding =>
            FSMRX_PADDING <= '1';
            FSMRX_CNT_PAD_CE <= PIPE_RD;
            FSMRX_DV <= '1';
            FSMRX_DST_RDY <= '0';
            if (LAST_PAD_WORD = "111" and PIPE_RD='1') then
               FSMRX_CNT_PAD_LD<= '1';
               FSMRX_EOP <= '1';
            end if;

      end case;
   end process output_logic;

end architecture obuf_xgmii_process_fsmrx_arch;
   
