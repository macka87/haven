-- swr_filler.vhd - aligns data to wanted bytes
-- Copyright (C) 2007 CESNET
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
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------
entity SWR_FILLER is
  generic(
    DATA_WIDTH     : integer := 32;
    BYTES_TO_ALIGN : integer := 8
  );
  port(
    CLK             : in  std_logic;
    RESET           : in  std_logic;

    -- Write interface
    NONALIGNED_DATA : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    NONALIGNED_END  : in  std_logic;
    SRC_RDY_N       : in  std_logic;
    DST_RDY_N       : out std_logic;

    -- Read interface
    WRITE           : out std_logic;
    ALIGNED_DATA    : out std_logic_vector(DATA_WIDTH-1 downto 0);
    BUFFER_FULL     : in  std_logic;
    ALIGNED_END     : out std_logic
  );
end entity;

-- ----------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------
architecture behavioral of SWR_FILLER is

  constant CNT_FILL_WIDTH : integer := log2((8*BYTES_TO_ALIGN) / DATA_WIDTH);

  type t_state is (S_WDATA, S_WPADDING);

  signal present_state  : t_state;
  signal next_state     : t_state;
  signal fill_cnt       : std_logic_vector(CNT_FILL_WIDTH - 1 downto 0);
  signal vcc_vec        : std_logic_vector(CNT_FILL_WIDTH - 1 downto 0);
  signal wr_transaction : std_logic;
  signal dst_rdy_n_int : std_logic;
   signal fill_cnt_ce : std_logic;
-- ----------------------------------------------------------------------------
begin

   vcc_vec <= (others => '1');

-- counts from CYCLES_FOR_N_BYTES to 0
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (RESET = '1') then
      fill_cnt <= (others => '0');
    else
      if (fill_cnt_ce = '1') then
        fill_cnt <= fill_cnt + 1;
      end if;
    end if;
  end if;
end process;


-- Write transaction -- used only during data transmission
wr_transaction <= not (dst_rdy_n_int or SRC_RDY_N);

-- sync FSM state ----------------------------------------------------------
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (RESET = '1') then
      present_state <= S_WDATA;
    else
      present_state <= next_state;
    end if;
  end if;
end process;



-- next_state logic
-- when nonaligned data ends and N bytes are not yet written, generates signal that indicates inserting
process(present_state, fill_cnt, NONALIGNED_END, wr_transaction, BUFFER_FULL)
begin
  case present_state is
    -- ------------------------------
    when S_WDATA =>
      if ((fill_cnt /= vcc_vec) and (NONALIGNED_END = '1') and wr_transaction = '1') then
         next_state <= S_WPADDING;
      else
         next_state <= S_WDATA;
      end if;

    -- ------------------------------
    when S_WPADDING =>
      if (fill_cnt = vcc_vec and BUFFER_FULL = '0') then
         next_state <= S_WDATA;
      else
         next_state <= S_WPADDING;
      end if;

    -- ------------------------------
    when others =>
      next_state <= S_WDATA;
  end case;
end process;


-- FSM output logic
process(present_state, SRC_RDY_N, BUFFER_FULL, NONALIGNED_DATA, NONALIGNED_END,
   wr_transaction, fill_cnt)
begin


    dst_rdy_n_int <= '1';
    ALIGNED_DATA  <= (others => 'X'); -- dead
    ALIGNED_END   <= '0';
    WRITE         <= '0';
    fill_cnt_ce   <= '0';

  case present_state is

    -- ------------------------------
    -- writing input to buffer
    when S_WDATA =>
      dst_rdy_n_int  <= BUFFER_FULL;
      ALIGNED_DATA   <= NONALIGNED_DATA;
      WRITE          <= not SRC_RDY_N;
      fill_cnt_ce    <= wr_transaction;
      if (fill_cnt = vcc_vec) then
         ALIGNED_END <= NONALIGNED_END;
      end if;

    -- ------------------------------
    -- writing zeros (filling) up to N bytes
    when S_WPADDING =>
      dst_rdy_n_int  <= '1';
      ALIGNED_DATA   <= (others => '0');
      WRITE          <= '1';
      fill_cnt_ce    <= not BUFFER_FULL;
      if (fill_cnt = vcc_vec) then
         ALIGNED_END <= '1';
      end if;

    -- ------------------------------
    when others =>
      null;

  end case;
end process;


DST_RDY_N <= dst_rdy_n_int;

end architecture;
-- ----------------------------------------------------------------------------
