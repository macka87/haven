--
-- output_fsm.vhd : PCI-e Length decoder
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
entity PCIE_TX_OUT_FSM is
  port (
    -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N           : in  std_logic; 
      TRN_CLK               : in  std_logic; 
    -- Data Input Interface -------------------------------------------------
      TRN_LNK_UP_N          : in  std_logic;                     -- Transaction Link Up
      TRN_TREM_N            : out std_logic_vector(7 downto 0);  -- Transmit Data Reminder
      TRN_TSOF_N            : out std_logic;                     -- Transmit SOF
      TRN_TEOF_N            : out std_logic;                     -- Transmit EOF
      TRN_TSRC_RDY_N        : out std_logic;                     -- Trnasmit Source Ready
      TRN_TDST_RDY_N        : in  std_logic;                     -- Transmit Destination Ready
      TRN_TBUF_AV           : in  std_logic_vector(3 downto 0);  -- Transmit Buffers Available
                                                                 -- trn_tbuf_av[0] => Non Posted Queue
                                                                 -- trn_tbuf_av[1] => Posted Queue
                                                                 -- trn_tbuf_av[2] => Completion Queue
    
    -- Type Control Interface -----------------------------------------------
      SPLIT_TRANS           : in std_logic;
      WITH_DATA             : in std_logic;                      -- Type
      DW4_REG               : in std_logic;                      -- Type
      TR_TYPE               : in std_logic_vector(1 downto 0);   -- Trans. Type

    -- Realign circuit ------------------------------------------------------
      REALIGN_SOP_N        :  in std_logic;                      -- Start of Packet
      REALIGN_EOP_N        :  in std_logic;                      -- End of Packet
      REALIGN_SRC_RDY_N    :  in std_logic;                      -- Source Ready
      REALIGN_DST_RDY_N    : out std_logic;                      -- Destination Ready
      REALIGN_REM_N        :  in std_logic;                      -- Realign circuit ready

    -- Input FSM Interface --------------------------------------------------
      HDR0_RDY             :  in std_logic;   
      HDR1_RDY             :  in std_logic;
      HDR0_ACK             : out std_logic;
      HDR1_ACK             : out std_logic;

    -- Control Interface ----------------------------------------------------
      NEXT_PART            : out std_logic;                      -- Next part
      TYPE_OUT             : out std_logic_vector(1 downto 0);
      DATA_SEL             : out std_logic_vector(1 downto 0);   -- Data select
      DW4_OUT              : out std_logic                       -- Data select
   );
end PCIE_TX_OUT_FSM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of PCIE_TX_OUT_FSM is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
  
   -- Control FSM declaration
   type   t_states is (st_hdr0, st_hdr1, st_hdr1_data, st_data);
   signal present_state, next_state : t_states;

   signal type_reg : std_logic_vector(1 downto 0);
   signal type_reg_we : std_logic;
   signal dw4_inside_reg : std_logic;
   signal split_trans_reg : std_logic;
   signal split_trans_reg_we : std_logic;
   signal aux_dst_rdy_n_other : std_logic;
   signal aux_dst_rdy_n_first : std_logic;
begin

-- Start sending when link up and buffers are available
aux_dst_rdy_n_first <= '0' when (TRN_TDST_RDY_N ='0' and TRN_LNK_UP_N='0' and TRN_TBUF_AV="1111") else '1';
-- Look only on TRN_TDST_RDY_N during on-going transaction 
aux_dst_rdy_n_other <= TRN_TDST_RDY_N;

-- register type_reg ------------------------------------------------------
type_regp: process(TRN_CLK, TRN_RESET_N)
begin
  if (TRN_CLK'event AND TRN_CLK = '1') then
     if (TRN_RESET_N = '0') then
       type_reg <= (others =>'0');
     elsif (type_reg_we = '1') then
         type_reg <= TR_TYPE;
     end if;
   end if;
end process;

-- register type_reg ------------------------------------------------------
dw4_inside_regp: process(TRN_CLK, TRN_RESET_N)
begin
  if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
         dw4_inside_reg <= '0';
      elsif (type_reg_we = '1') then
         dw4_inside_reg <= DW4_REG;
      end if;
  end if;
end process;

-- register split_trans_reg ------------------------------------------------------
split_trans_regp: process(TRN_CLK, TRN_RESET_N)
begin
  if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
         split_trans_reg <= '0';
      elsif (split_trans_reg_we = '1') then
         split_trans_reg <= SPLIT_TRANS;
      end if;
   end if;
end process;

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
state_trans: process(present_state, aux_dst_rdy_n_other, aux_dst_rdy_n_first, WITH_DATA,
                     DW4_REG, REALIGN_SOP_N, REALIGN_EOP_N, REALIGN_SRC_RDY_N,
                     REALIGN_REM_N, HDR0_RDY, HDR1_RDY, dw4_inside_reg, SPLIT_TRANS)
  begin
    case present_state is

      -- ST_HDR0
      when st_hdr0 =>
        if (HDR0_RDY = '1' and aux_dst_rdy_n_first = '0') then
          if (WITH_DATA = '1') then
            next_state <= st_hdr1_data;
          else
            next_state <= st_hdr1;
          end if;
        else
          next_state <= st_hdr0;
        end if;

      -- ST_HDR1 (data transaction)
      when st_hdr1_data =>
        if (HDR1_RDY = '1' and aux_dst_rdy_n_other = '0') then
          if (dw4_inside_reg = '1') then
            next_state <= st_data;
          elsif (dw4_inside_reg = '0' and REALIGN_SRC_RDY_N = '0') then
            if (REALIGN_EOP_N = '0') then
              next_state <= st_hdr0;
            else
              next_state <= st_data;
            end if;
          else
            next_state <= st_hdr1_data;   
          end if;
        else
          next_state <= st_hdr1_data;
        end if;
              
      -- ST_HDR1 (read)
      when st_hdr1 =>
        if (HDR1_RDY = '1' and aux_dst_rdy_n_other = '0') then
          next_state <= st_hdr0;
        else
          next_state <= st_hdr1;
        end if;

      -- ST_DATA
      when st_data =>
        if (REALIGN_SRC_RDY_N = '0' and REALIGN_EOP_N = '0' and aux_dst_rdy_n_other = '0') then
          next_state <= st_hdr0;
        else
          next_state <= st_data;
        end if;
    end case;

  end process;

-- output logic
output_logic: process(present_state, aux_dst_rdy_n_first, aux_dst_rdy_n_other, WITH_DATA,
                      DW4_REG, REALIGN_SOP_N, REALIGN_EOP_N, REALIGN_SRC_RDY_N, REALIGN_REM_N,
                      HDR0_RDY, HDR1_RDY, TR_TYPE, type_reg, dw4_inside_reg, SPLIT_TRANS,
                      split_trans_reg, TRN_LNK_UP_N, TRN_TBUF_AV)
  begin

    TRN_TREM_N        <= "11111111";
    TRN_TSOF_N        <= '1';
    TRN_TEOF_N        <= '1';
    TRN_TSRC_RDY_N    <= '1';
    REALIGN_DST_RDY_N <= '1';
    HDR0_ACK          <= '0';
    HDR1_ACK          <= '0';
    DATA_SEL          <= "00";
    NEXT_PART         <= '0';
    TYPE_OUT          <= "00";
    type_reg_we       <= '0';
    DW4_OUT           <= '0';
    split_trans_reg_we <= '0';

    case present_state is

      -- ST_HDR0
      when st_hdr0 =>
        TYPE_OUT          <= TR_TYPE;
        DW4_OUT           <= DW4_REG;
        type_reg_we       <= '1';
        TRN_TREM_N        <= "00000000";
        if (HDR0_RDY = '1' and TRN_LNK_UP_N='0' and TRN_TBUF_AV="1111") then
          TRN_TSRC_RDY_N  <= '0';
          TRN_TSOF_N      <= '0';
        end if;
        DATA_SEL          <= "00";
        split_trans_reg_we <= '1';
        
        if (HDR0_RDY = '1' and aux_dst_rdy_n_first = '0') then
            HDR0_ACK      <= not SPLIT_TRANS;
        end if;
        

      -- ST_HDR1 (data transaction)
      when st_hdr1_data =>
        TYPE_OUT          <= type_reg;
        DW4_OUT           <= dw4_inside_reg;
        TRN_TREM_N        <= "00000000";
        TRN_TEOF_N        <= not (not dw4_inside_reg and not REALIGN_EOP_N);
        TRN_TSRC_RDY_N    <= not ( (HDR1_RDY and dw4_inside_reg) or (HDR1_RDY and not dw4_inside_reg and not REALIGN_SRC_RDY_N));
        REALIGN_DST_RDY_N <= not (HDR1_RDY and not aux_dst_rdy_n_other and not dw4_inside_reg);
        DATA_SEL          <= "01";

        if (HDR1_RDY = '1' and aux_dst_rdy_n_other = '0') then
          if (dw4_inside_reg = '1') then
            HDR1_ACK      <= not split_trans_reg;
          elsif (dw4_inside_reg = '0' and REALIGN_SRC_RDY_N = '0') then
            HDR1_ACK      <= not split_trans_reg;
          end if;
        end if;

        if (HDR1_RDY = '1' and aux_dst_rdy_n_other = '0' and dw4_inside_reg = '0' and REALIGN_SRC_RDY_N = '0' and REALIGN_EOP_N='0') then
           NEXT_PART     <= split_trans_reg;
        end if;


      -- ST_HDR1 (read)
      when st_hdr1 =>
        TYPE_OUT          <= type_reg;
        DW4_OUT           <= dw4_inside_reg;
        TRN_TREM_N        <= "0000" & not dw4_inside_reg & not dw4_inside_reg & not dw4_inside_reg & not dw4_inside_reg;
        TRN_TEOF_N        <= not HDR1_RDY;
        TRN_TSRC_RDY_N    <= not HDR1_RDY;
        DATA_SEL          <= "01";
        HDR1_ACK          <= HDR1_RDY and not aux_dst_rdy_n_other;
       
        if (HDR1_RDY='1' and aux_dst_rdy_n_other='0') then
          HDR1_ACK          <= not split_trans_reg;
        end if;

        if (HDR1_RDY = '1' and aux_dst_rdy_n_other = '0') then
           NEXT_PART <= split_trans_reg;
        end if;

      -- ST_DATA
      when st_data =>
        TYPE_OUT          <= type_reg;
        DW4_OUT           <= dw4_inside_reg;
        TRN_TREM_N        <= "0000" &  REALIGN_REM_N &  REALIGN_REM_N &  REALIGN_REM_N & REALIGN_REM_N;
        TRN_TSRC_RDY_N    <= REALIGN_SRC_RDY_N;
        TRN_TEOF_N        <= not (not REALIGN_SRC_RDY_N and not REALIGN_EOP_N);
        DATA_SEL          <= "10";
        REALIGN_DST_RDY_N <= aux_dst_rdy_n_other;

        if (REALIGN_SRC_RDY_N = '0' and REALIGN_EOP_N = '0' and aux_dst_rdy_n_other = '0') then
          NEXT_PART <= split_trans_reg;
        end if;

      end case;
  end process;


end architecture FULL;

