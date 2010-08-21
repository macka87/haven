 --
-- len_decoder.vhd : PCI-e Length decoder
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kobierský <kobierskyk@liberouter.org>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity PCIE_TX_IN_FSM is
  port (
    -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N          : in  std_logic; 
      TRN_CLK              : in  std_logic; 
    -- Data Input Interface -------------------------------------------------
      IN_SOP_N             : in  std_logic;  -- Start of Packet
      IN_EOP_N             : in  std_logic;  -- End of Packet
      IN_SRC_RDY_N         : in  std_logic;  -- Source Ready
      IN_DST_RDY_N         : out std_logic;  -- Destination Ready
      IN_DW4_VLD           : in  std_logic;  -- DW4 computation ready
   -- Data Input Interface -------------------------------------------------
      REALIGN_SOP_N        : out std_logic;  -- Start of Packet
      REALIGN_EOP_N        : out std_logic;  -- End of Packet
      REALIGN_SRC_RDY_N    : out std_logic;  -- Source Ready
      REALIGN_DST_RDY_N    :  in std_logic;  -- Destination Ready
      REALIGN_RDY          :  in std_logic;  -- Realign circuit ready
      REALIGN_INIT         : out std_logic;  -- Realign circuit Init
    -- Output FSM Interface -------------------------------------------------
      HDR0_RDY             : out std_logic;   
      HDR1_RDY             : out std_logic;
      HDR0_ACK             :  in std_logic;
      HDR1_ACK             :  in std_logic;
    -- Control Interface ----------------------------------------------------
      TYPE_WE              : out std_logic;
      LEN_WE               : out std_logic;
      TAG_WE               : out std_logic;
      FIRST_BE_SRC_ADDR_WE : out std_logic;
      ADDR_WE              : out std_logic;
      LOWER_ADDR_WE        : out std_logic;
      REQUESTER_ID_WE      : out std_logic;
      SECOND_HDR           : out std_logic
   );
end PCIE_TX_IN_FSM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of PCIE_TX_IN_FSM is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
  
   -- Control FSM declaration
   type   t_states is (st_hdr0, st_hdr1, st_sop_data, st_data);
   signal present_state, next_state : t_states;

   signal hdr0_rdy_reg     : std_logic;
   signal hdr0_rdy_reg_set : std_logic;
   signal hdr1_rdy_reg     : std_logic;
   signal hdr1_rdy_reg_set : std_logic;
 
begin

-- register hdr0_rdy_reg ------------------------------------------------------
hdr0_rdy_regp: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
         hdr0_rdy_reg <= '0';
      elsif (hdr0_rdy_reg_set = '1') then
         hdr0_rdy_reg <= '1';
      elsif (HDR0_ACK = '1') then
         hdr0_rdy_reg <= '0';
      end if;
   end if;
end process;

-- register hdr1_rdy_reg ------------------------------------------------------
hdr1_rdy_regp: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
        hdr1_rdy_reg <= '0';
      elsif (hdr1_rdy_reg_set = '1') then
         hdr1_rdy_reg <= '1';
      elsif (HDR1_ACK = '1') then
         hdr1_rdy_reg <= '0';
      end if;
   end if;
end process;

HDR0_RDY <= hdr0_rdy_reg;
HDR1_RDY <= hdr1_rdy_reg;

-- SWITCH INPUT FSM -----------------------------------------------------------
-- next state clk logic
clk_d: process(TRN_CLK, TRN_RESET_N)
  begin
    if (TRN_CLK='1' and TRN_CLK'event) then
      if TRN_RESET_N = '0' then
         present_state <= st_hdr0;
      else
         present_state <= next_state;
      end if;
    end if;
  end process;

-- next state logic
state_trans: process(present_state, IN_SOP_N, IN_EOP_N, IN_SRC_RDY_N, REALIGN_DST_RDY_N,
                     REALIGN_RDY, HDR0_ACK, HDR1_ACK, hdr0_rdy_reg, hdr1_rdy_reg, IN_DW4_VLD)
  begin
    case present_state is
      -- ST_HDR0
      when st_hdr0 =>
        if (IN_DW4_VLD = '1' and IN_SRC_RDY_N ='0' and (hdr0_rdy_reg ='0' or HDR0_ACK='1')) then
          next_state <= st_hdr1;
        else
          next_state <= st_hdr0;
        end if;

      -- ST_HDR1
      when st_hdr1 =>
        if (IN_SRC_RDY_N = '0' and (hdr1_rdy_reg = '0' or HDR1_ACK = '1')) then
          if (IN_EOP_N = '0') then
            next_state <= st_hdr0;
          elsif (IN_EOP_N = '1' and REALIGN_RDY='1') then
            next_state <= st_sop_data;
          else
            next_state <= st_hdr1;
          end if;
        else
          next_state <= st_hdr1;
        end if;

      -- ST_SOP_DATA
      when st_sop_data =>
        if (IN_SRC_RDY_N = '0' and REALIGN_DST_RDY_N='0') then
          if (IN_EOP_N = '0') then
            next_state <= st_hdr0;
          else
            next_state <= st_data;
          end if;
        else
          next_state <= st_sop_data;
        end if;

      -- ST_DATA
      when st_data =>
        if (IN_SRC_RDY_N = '0' and IN_EOP_N = '0' and REALIGN_DST_RDY_N='0') then
          next_state <= st_hdr0;
        else
          next_state <= st_data;
        end if;
    end case;

  end process;

-- output logic
output_logic: process(present_state, IN_SOP_N, IN_EOP_N, IN_SRC_RDY_N, REALIGN_DST_RDY_N,
                      REALIGN_RDY, HDR0_ACK, HDR1_ACK, hdr0_rdy_reg, hdr1_rdy_reg, IN_DW4_VLD)
  begin
      hdr0_rdy_reg_set      <= '0';
      hdr1_rdy_reg_set      <= '0';
      IN_DST_RDY_N          <= '1';
      REALIGN_SOP_N         <= '1';
      REALIGN_EOP_N         <= '1';
      REALIGN_SRC_RDY_N     <= '1';
      REALIGN_INIT          <= '0';
      TYPE_WE               <= '0';
      LEN_WE                <= '0';
      TAG_WE                <= '0';
      FIRST_BE_SRC_ADDR_WE  <= '0';
      ADDR_WE               <= '0';
      LOWER_ADDR_WE         <= '0';
      REQUESTER_ID_WE       <= '0';
      SECOND_HDR            <= '0';

    case present_state is

      -- ST_HDR0 (OKI)
      when st_hdr0 =>
        if (IN_SRC_RDY_N ='1') then
          IN_DST_RDY_N <= '0';
        elsif (IN_DW4_VLD='1' and (hdr0_rdy_reg = '0' or HDR0_ACK='1')) then
           IN_DST_RDY_N          <= '0'; --not (not hdr0_rdy_reg or HDR0_ACK);
        end if;

        if (IN_DW4_VLD='1' and IN_SRC_RDY_N ='0' and (hdr0_rdy_reg ='0' or HDR0_ACK='1')) then
          hdr0_rdy_reg_set      <= '1';
          TYPE_WE               <= '1';
          LEN_WE                <= '1';
          TAG_WE                <= '1';
          FIRST_BE_SRC_ADDR_WE  <= '1';
        end if;

      -- ST_HDR1
      when st_hdr1 =>
        SECOND_HDR <= '1';
--        IN_DST_RDY_N <= not ( (not hdr1_rdy_reg or HDR1_ACK) and (not IN_EOP_N or (IN_EOP_N and REALIGN_RDY)));
        if (hdr1_rdy_reg = '0' or HDR1_ACK = '1') and ((IN_EOP_N = '0') or (IN_EOP_N='1' and REALIGN_RDY='1')) then
          IN_DST_RDY_N <= '0';
        end if;

        if (IN_SRC_RDY_N = '0' and (hdr1_rdy_reg = '0' or HDR1_ACK = '1')) then
          if (IN_EOP_N = '0') then
            hdr1_rdy_reg_set      <= '1';
            ADDR_WE               <= '1';
            LOWER_ADDR_WE         <= '1';
            REQUESTER_ID_WE       <= '1';
          elsif (IN_EOP_N = '1' and REALIGN_RDY='1') then
            hdr1_rdy_reg_set      <= '1';
            ADDR_WE               <= '1';
            LOWER_ADDR_WE         <= '1';
            REQUESTER_ID_WE       <= '1';
            REALIGN_INIT          <= '1';
          end if;
        end if;

      -- ST_SOP_DATA
      when st_sop_data =>
         IN_DST_RDY_N          <= REALIGN_DST_RDY_N;
         REALIGN_SOP_N         <= '0';
         REALIGN_EOP_N         <= IN_EOP_N;
         REALIGN_SRC_RDY_N     <= IN_SRC_RDY_N;

      -- ST_DATA
      when st_data =>
         IN_DST_RDY_N          <= REALIGN_DST_RDY_N;
         REALIGN_SOP_N         <= '1';
         REALIGN_EOP_N         <= IN_EOP_N;
         REALIGN_SRC_RDY_N     <= IN_SRC_RDY_N;

      end case;
  end process;


end architecture FULL;

