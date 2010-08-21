--
-- obuf_gmii_tx_fsm.vhd: fsm for obuf_gmii transmit part
--
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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
--

library IEEE;
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_gmii_tx_fsm is
   generic (
      -- Should the FCS computation be skipped?
      SKIP_FCS : boolean := false
   );
   port (
      CLK       :  in std_logic;
      RESET     :  in std_logic;

      START     :  in std_logic;
      DV        :  in std_logic;
      IFR_OVF   :  in std_logic;
      PREAM_OVF :  in std_logic;
      FCS_OVF   :  in std_logic;
      SGMII_DV  :  in std_logic;

      DO_DV     : out std_logic;
      IFR       : out std_logic;
      SFD       : out std_logic;
      PREAM     : out std_logic;
      DATA      : out std_logic;
      FCS       : out std_logic
   );

end entity obuf_gmii_tx_fsm;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_gmii_tx_fsm is

   type t_state is (S_IDLE, S_PREAM, S_SFD, S_DATA, S_FCS);
   signal present_state, next_state : t_state;

begin -------------------------------------------------------------------------

   sync_fsm: process(RESET, CLK)
   begin
      if (RESET = '1') then
         present_state <= S_IDLE;
      elsif (CLK'event and CLK = '1') then
         if (SGMII_DV = '1') then
            present_state <= next_state;
         end if;
      end if;
   end process;

   next_state_logic:
   process(present_state, CLK, RESET, START, DV, IFR_OVF, PREAM_OVF, FCS_OVF)
   begin
      case (present_state) is
      -- ------------------------------
      when S_IDLE =>
         next_state <= S_IDLE;
         if (START='1' and IFR_OVF='1') then
	    next_state <= S_PREAM;
         end if;
      -- ------------------------------
      when S_PREAM =>
         next_state <= S_PREAM;
         if (PREAM_OVF='1') then
            next_state <= S_SFD;
         end if;
      -- ------------------------------
      when S_SFD =>
         next_state <= S_DATA;
      -- ------------------------------
      when S_DATA =>
         next_state <= S_DATA;
         if (DV='0') then
            if (SKIP_FCS = false) then -- if the FCS is computed and appended to the packet
               next_state <= S_FCS;
            else                       -- if the FCS computation is skipped
               next_state <= S_IDLE;
            end if;
         end if;
      -- ------------------------------
      when S_FCS =>
         next_state <= S_FCS;
         if (FCS_OVF='1') then
	    next_state <= S_IDLE;
         end if;
      -- ------------------------------
      when others =>
         next_state <= S_IDLE;
      -- -------------------------- ----
      end case;
   end process;

   output_logic:
   process(present_state, CLK, RESET, START, DV, IFR_OVF, PREAM_OVF, FCS_OVF)
   begin
      DO_DV <= '0';
      IFR   <= '0';
      SFD   <= '0';
      PREAM <= '0';
      DATA  <= '0';
      FCS   <= '0';

      case (present_state) is
         -- ------------------------------
         when S_IDLE =>
            IFR <= '1';
	    if (START='1' and IFR_OVF='1') then
               IFR   <= '0';
	       PREAM <= '1';
	       DO_DV <= '1';
            end if;
         -- ------------------------------
         when S_PREAM =>
            PREAM <= '1';
	    DO_DV <= '1';
            if (PREAM_OVF='1') then
               SFD   <= '1';
	       PREAM <= '0';
            end if;
         -- ------------------------------
         when S_SFD =>
	    DO_DV <= '1';
	    DATA  <= '1';
         -- ------------------------------
         when S_DATA =>
            DATA  <= '1';
	    DO_DV <= '1';
            if (DV='0') then
	       DATA <= '0';
               FCS  <= '1';
              if (SKIP_FCS = true) then -- if the FCS computation is skipped
                 DO_DV <= '0';
              end if;
            end if;
         -- ------------------------------
         when S_FCS =>
            FCS   <= '1';
	    DO_DV <= '1';
            if (FCS_OVF='1') then
	       IFR   <= '1';
	       FCS   <= '0';
	       DO_DV <= '0';
            end if;
         -- ------------------------------
         when others =>
            null;
         -- ------------------------------
      end case;
   end process;

end architecture full;
