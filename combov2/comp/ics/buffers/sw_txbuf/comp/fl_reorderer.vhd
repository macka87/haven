--
-- fl_reorderer.vhd - reorders data; used to remove size of frame and head
--                    at 64-bit FrameLink flow (when size'width is 16)
-- Author(s): Vozenilek Jan <xvozen00@stud.fit.vutbr.cz>
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
entity FL_REORDERER is
  generic(
    DATA_WIDTH : integer := 64
  );
  port(
    CLK          : in  std_logic;
    RESET        : in  std_logic;

    -- Input interface
    RX_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    RX_SOF_N     : in  std_logic;
    RX_EOF_N     : in  std_logic;
    RX_SOP_N     : in  std_logic;
    RX_EOP_N     : in  std_logic;
    RX_SRC_RDY_N : in  std_logic;
    RX_DST_RDY_N : out std_logic;
    RX_REM       : in  std_logic_vector(abs(log2(DATA_WIDTH/8)-1) downto 0);

    -- Output interface
    TX_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
    TX_SOF_N     : out std_logic;
    TX_EOF_N     : out std_logic;
    TX_SOP_N     : out std_logic;
    TX_EOP_N     : out std_logic;
    TX_SRC_RDY_N : out std_logic;
    TX_DST_RDY_N : in  std_logic;
    TX_REM       : out std_logic_vector(abs(log2(DATA_WIDTH/8)-1) downto 0)
  );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of FL_REORDERER is

  type fsm_states is (s_empty, s_half1, s_full1, s_half2, s_full2);

  signal pres_state : fsm_states;
  signal next_state : fsm_states;
  signal data_reg   : std_logic_vector(2*DATA_WIDTH-1 downto 0);
  signal sof_reg1   : std_logic;
  signal eof_reg1   : std_logic;
  signal sop_reg1   : std_logic;
  signal eop_reg1   : std_logic;
  signal rem_reg1   : std_logic_vector(abs(log2(DATA_WIDTH/8)-1) downto 0);
  signal sof_reg2   : std_logic;
  signal eof_reg2   : std_logic;
  signal sop_reg2   : std_logic;
  signal eop_reg2   : std_logic;
  signal rem_reg2   : std_logic_vector(abs(log2(DATA_WIDTH/8)-1) downto 0);
  signal load_half1 : std_logic;
  signal load_full1 : std_logic;
  signal load_full2 : std_logic;

-- ----------------------------------------------------------------------------
begin

-- fsm
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (RESET = '1') then
      pres_state <= s_empty;
    else
      pres_state <= next_state;
    end if;
  end if;
end process;

-- next state logic
process(RX_SRC_RDY_N, RX_EOP_N, TX_DST_RDY_N)
begin
  case (pres_state) is
    -- ------------------------------
    when s_empty =>
      if (RX_SRC_RDY_N = '0') then
        next_state <= s_half1;
      else
        next_state <= s_empty;
      end if;
    -- ------------------------------
    when s_half1 =>
      if (RX_SRC_RDY_N = '0') then
        if (RX_EOP_N = '0') then
          next_state <= s_empty;
        else
          next_state <= s_full1;
        end if;
      else
        next_state <= s_half1;
      end if;
    -- ------------------------------
    when s_full1 =>
      if (TX_DST_RDY_N = '0') then
        next_state <= s_half2;
      else
        next_state <= s_full1;
      end if;      
    -- ------------------------------
    when s_half2 =>
      if (RX_SRC_RDY_N = '0') then
        if (RX_EOP_N = '0') then
          next_state <= s_empty;
        else
          next_state <= s_full2;
        end if;
      else
        next_state <= s_half2;
      end if;      
    -- ------------------------------
    when s_full2 =>
      if (TX_DST_RDY_N = '0') then
        next_state <= s_half1;
      else
        next_state <= s_full2;
      end if;      
    -- ------------------------------
  end case;
end process;

-- output logic
process(RX_SRC_RDY_N, TX_DST_RDY_N, data_reg,
        sof_reg1, eof_reg1, sop_reg1, eop_reg1, rem_reg1,
        sof_reg2, eof_reg2, sop_reg2, eop_reg2, rem_reg2)
begin
  case (pres_state) is
    -- ------------------------------
    when s_empty =>
      load_half1   <= not RX_SRC_RDY_N;
      load_full1   <= '0';
      load_full2   <= '0';
      RX_DST_RDY_N <= '0';
      TX_SRC_RDY_N <= '1';
      TX_DATA      <= (others => '0');
      TX_REM       <= (others => '0');
      TX_SOF_N     <= '1';
      TX_EOF_N     <= '1';
      TX_SOP_N     <= '1';
      TX_EOP_N     <= '1';
    -- ------------------------------
    when s_half1 =>
      load_half1   <= '0';
      load_full1   <= not RX_SRC_RDY_N;
      load_full2   <= '0';
      RX_DST_RDY_N <= '0';
      TX_SRC_RDY_N <= not eop_reg1;
      TX_DATA      <= data_reg(DATA_WIDTH-1 downto 0);
      TX_REM       <= rem_reg1 - DATA_WIDTH/16;
      TX_SOF_N     <= sof_reg1;
      TX_EOF_N     <= eof_reg1;
      TX_SOP_N     <= sop_reg1;
      TX_EOP_N     <= eop_reg1;
    -- ------------------------------
    when s_full1 =>
      load_half1   <= '0';
      load_full1   <= '0';
      load_full2   <= '0';
      RX_DST_RDY_N <= '1';
      TX_SRC_RDY_N <= '0';
      TX_DATA      <= data_reg(DATA_WIDTH-1 downto 0);
      TX_REM       <= rem_reg1 - DATA_WIDTH/16;
      TX_SOF_N     <= sof_reg1;
      TX_EOF_N     <= eof_reg1;
      TX_SOP_N     <= sop_reg1;
      TX_EOP_N     <= eop_reg1;
    -- ------------------------------
    when s_half2 =>
      load_half1   <= '0';
      load_full1   <= '0';
      load_full2   <= not RX_SRC_RDY_N;
      RX_DST_RDY_N <= '0';
      TX_SRC_RDY_N <= not eop_reg2;
      TX_DATA      <= data_reg(2*DATA_WIDTH-1 downto DATA_WIDTH);
      TX_REM       <= rem_reg2 - DATA_WIDTH/16;
      TX_SOF_N     <= sof_reg2;
      TX_EOF_N     <= eof_reg2;
      TX_SOP_N     <= sop_reg2;
      TX_EOP_N     <= eop_reg2;
    -- ------------------------------
    when s_full2 =>
      load_half1   <= '0';
      load_full1   <= '0';
      load_full2   <= '0';
      RX_DST_RDY_N <= '1';
      TX_SRC_RDY_N <= '0';
      TX_DATA      <= data_reg(2*DATA_WIDTH-1 downto DATA_WIDTH);
      TX_REM       <= rem_reg2 - DATA_WIDTH/16;
      TX_SOF_N     <= sof_reg2;
      TX_EOF_N     <= eof_reg2;
      TX_SOP_N     <= sop_reg2;
      TX_EOP_N     <= eop_reg2;
    -- ------------------------------
  end case;
end process;

-- data register
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if ((load_half1 = '1') or (load_full2 = '1')) then
      data_reg(DATA_WIDTH/2-1 downto 0)
        <= RX_DATA(DATA_WIDTH-1 downto DATA_WIDTH/2);
    end if;
    if (load_full1 = '1') then
      data_reg(DATA_WIDTH+DATA_WIDTH/2-1 downto DATA_WIDTH/2) <= RX_DATA;
    end if;
    if (load_full2 = '1') then
      data_reg(2*DATA_WIDTH-1 downto DATA_WIDTH+DATA_WIDTH/2)
        <= RX_DATA(DATA_WIDTH/2-1 downto 0);
    end if;
  end if;
end process;

-- registers
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if ((load_half1 = '1') or (load_full2 = '1')) then
      sof_reg1 <= RX_SOF_N;
      eof_reg1 <= RX_EOF_N;
      sop_reg1 <= RX_SOP_N;
      eop_reg1 <= RX_EOP_N;
      rem_reg1 <= RX_REM;
    end if;
  end if;
end process;

process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (load_full1 = '1') then
      sof_reg2 <= RX_SOF_N;
      eof_reg2 <= RX_EOF_N;
      sop_reg2 <= RX_SOP_N;
      eop_reg2 <= RX_EOP_N;
      rem_reg2 <= RX_REM;
    end if;
  end if;
end process;

end architecture;
