-- parser_pac.vhd - Framelink generator for packet TX BUFFER.
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Vozenilek <xvozen00@stud.fit.vutbr.cz>
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
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TXBUF_PARSER_PAC is
  generic (
    DATA_WIDTH : integer := 16;
    FLOWS      : integer := 4
  );
  port (
    CLK          : in  std_logic;
    RESET        : in  std_logic;

    -- Input mem2nfifo interface
    TXBUF_DATA   : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    TXBUF_VALID  : in  std_logic;
    TXBUF_READ   : out std_logic;

    -- Input sh_fifo interface
    NEWLEN_FIFO  : in  std_logic_vector(15 downto 0);
    NEWLEN_VLD   : in  std_logic;
    NEWLEN_READ  : out std_logic;

    -- Output FrameLink interface
    FL_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
    FL_SOF_N     : out std_logic;
    FL_SOP_N     : out std_logic;
    FL_EOP_N     : out std_logic;
    FL_EOF_N     : out std_logic;
    FL_REM       : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
    FL_SRC_RDY_N : out std_logic;
    FL_DST_RDY_N : in  std_logic
  );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of TXBUF_PARSER_PAC is

  -- DATA_WIDTH in Bytes
  constant DATA_WIDTH_BYTES : integer := DATA_WIDTH/8;
  -- number of bits to truncate for converting from bits to Bytes
  constant DATA_BYTES : integer := log2(DATA_WIDTH/8);

  type fsm_states is (s_idle, s_data, s_alignment, s_wait);

  subtype ITEMS_RANGE is natural range 15 downto DATA_BYTES;
  subtype BYTES_RANGE is natural range DATA_BYTES-1 downto 0;

  signal pres_state    : fsm_states;
  signal next_state    : fsm_states;

  signal txbuf_rd      : std_logic;

  signal items_cnt     : std_logic_vector(abs(log2(FLOWS)-1) downto 0);
  signal items_end     : std_logic;

  signal counter_rst   : std_logic;
  signal counter_ce    : std_logic;
  signal cnt_counter   : std_logic_vector(15 downto 0);

  signal data_transfer : std_logic;
  signal frame_end     : std_logic;
  signal frame_end_ce  : std_logic;
  signal next_frame    : std_logic;

-- ----------------------------------------------------------------------------
begin

assert ((DATA_WIDTH = 16) or (DATA_WIDTH = 32) or (DATA_WIDTH = 64))
report "TXBUF_PARSER_PAC: Supports only 16, 32 or 64 DATA_WIDTH."
severity failure;

data_transfer <= TXBUF_VALID and (not FL_DST_RDY_N);
next_frame    <= data_transfer and frame_end;

-- frame end register
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (RESET = '1') then
      frame_end <= '0';
    else
      if (frame_end_ce = '1') then
        if (cnt_counter >= NEWLEN_FIFO) then
          frame_end <= NEWLEN_VLD;
        else
          frame_end <= '0';
        end if;
      end if;
    end if;
  end if;
end process;

-- FSM register
process(CLK)
begin
  if ((CLK'event ) and (CLK = '1')) then
    if (RESET = '1') then
      pres_state <= s_idle;
    else
      pres_state <= next_state;
    end if;
  end if;
end process;

-- FSM next state logic
process(pres_state, data_transfer, next_frame, items_end)
begin
  next_state <= pres_state;
  case (pres_state) is
    -- ------------------------------
    when s_idle =>
      if (data_transfer = '1') then
        next_state <= s_data;
      end if;
    -- ------------------------------
    when s_data =>
      if (next_frame = '1') then
        if (items_end = '1') then
          next_state <= s_wait;
        else
          next_state <= s_alignment;
        end if;
      end if;
    -- ------------------------------
    when s_alignment =>
      if (items_end = '1') then
        next_state <= s_idle;
      end if;
    -- ------------------------------
    when s_wait =>
      next_state <= s_idle;
    -- ------------------------------
    when others =>
      null;
    -- ------------------------------
  end case;
end process;

-- FSM output logic
process(pres_state, data_transfer, next_frame, TXBUF_VALID, frame_end)
begin
  txbuf_rd     <= '0';
  frame_end_ce <= '0';
  NEWLEN_READ  <= '0';
  FL_SOF_N     <= '1';
  FL_SOP_N     <= '1';
  FL_EOP_N     <= '1';
  FL_EOF_N     <= '1';
  FL_SRC_RDY_N <= '1';
  counter_rst  <= '0';
  counter_ce   <= '0';
  case (pres_state) is
    -- ------------------------------
    when s_idle =>
      txbuf_rd     <= data_transfer;
      frame_end_ce <= data_transfer;
      NEWLEN_READ  <= next_frame;
      FL_SOF_N     <= not TXBUF_VALID;
      FL_SOP_N     <= not TXBUF_VALID;
      FL_EOP_N     <= not frame_end;
      FL_EOF_N     <= not frame_end;
      FL_SRC_RDY_N <= not TXBUF_VALID;
      counter_rst  <= next_frame;
      counter_ce   <= data_transfer;
    -- ------------------------------
    when s_data =>
      txbuf_rd     <= data_transfer;
      frame_end_ce <= data_transfer;
      NEWLEN_READ  <= next_frame;
      FL_EOP_N     <= not frame_end;
      FL_EOF_N     <= not frame_end;
      FL_SRC_RDY_N <= not TXBUF_VALID;
      counter_rst  <= next_frame;
      counter_ce   <= data_transfer;
    -- ------------------------------
    when s_alignment =>
      txbuf_rd     <= TXBUF_VALID;
      frame_end_ce <= TXBUF_VALID;
    -- ------------------------------
    when s_wait =>
      frame_end_ce <= '1';
    -- ------------------------------
    when others =>
      null;
    -- ------------------------------
  end case;
end process;

-- data counter
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if ((RESET = '1') or (counter_rst = '1')) then
      cnt_counter <= conv_std_logic_vector(2*DATA_WIDTH_BYTES, cnt_counter'length);
    else
      if (counter_ce = '1') then
        cnt_counter <= cnt_counter + DATA_WIDTH_BYTES;
      end if;
    end if;
  end if;
end process;

GEN_MORE_FLOWS : if (FLOWS > 1) generate

  -- items counter
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        items_cnt <= conv_std_logic_vector(0, items_cnt'length);
      else
        if (txbuf_rd = '1') then
          items_cnt <= items_cnt + 1;
        end if;
      end if;
    end if;
  end process;

  -- items end signal
  process(items_cnt)
  begin
    if (items_cnt = conv_std_logic_vector(FLOWS-1, items_cnt'length)) then
      items_end <= '1';
    else
      items_end <= '0';
    end if;
  end process;

end generate;

GEN_ONE_FLOW : if (FLOWS = 1) generate
  items_end <= '1';
end generate;

-- ----------------------------------------------------------------------------
-- interface mapping
TXBUF_READ <= txbuf_rd;
FL_DATA    <= TXBUF_DATA;
FL_REM     <= NEWLEN_FIFO(BYTES_RANGE)-1;

end architecture;
-- ----------------------------------------------------------------------------
