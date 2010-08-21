--
-- fifo_sync_block.vhd: Synchronous Block FIFO
-- Copyright (C) 2007 CESNET
-- Author(s): Vozenilek Jan  <xvozen00@stud.fit.vutbr.cz>
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
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- FIFO package
use work.fifo_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of FIFO_SYNC_BLOCK is

  constant ADDR_WIDTH : integer := log2(ITEMS)-1;

  subtype ADDR_RANGE is natural range ADDR_WIDTH downto 0;

  signal write_allow          : std_logic;
  signal read_allow           : std_logic;
  signal mem_pipe_en          : std_logic;
  signal mem_read_allow       : std_logic;
  signal sig_empty            : std_logic;
  signal sig_full             : std_logic;
  signal reg_empty            : std_logic;
  signal reg_full             : std_logic;
  signal reg_ready            : std_logic;
  signal sig_finish           : std_logic;
  signal reg_finish           : std_logic_vector(LATENCY-1 downto 0);

  signal sig_rd               : std_logic;
  signal rd_discard_allow     : std_logic;
  signal wr_discard_allow     : std_logic;
  signal sig_discarding       : std_logic;
  signal reg_discarding       : std_logic;
  signal sig_dv               : std_logic;

  signal cnt_write_addr       : std_logic_vector(log2(ITEMS) downto 0);
  signal cnt_write_addr_next  : std_logic_vector(log2(ITEMS) downto 0);
  signal cnt_read_addr        : std_logic_vector(log2(ITEMS) downto 0);
  signal cnt_read_addr_next   : std_logic_vector(log2(ITEMS) downto 0);
  signal reg_write_addr       : std_logic_vector(log2(ITEMS) downto 0);
  signal reg_read_addr        : std_logic_vector(log2(ITEMS) downto 0);

  signal mux_cnt_write_addr   : std_logic_vector(log2(ITEMS) downto 0);
  signal mux_reg_write_addr   : std_logic_vector(log2(ITEMS) downto 0);
  signal mux_read_addr_sel    : std_logic_vector(1 downto 0);
  signal mux_cnt_read_addr    : std_logic_vector(log2(ITEMS) downto 0);
  signal mux_reg_read_addr    : std_logic_vector(log2(ITEMS) downto 0);

  signal cnt_blk_finish       : std_logic_vector(log2(BLOCK_SIZE)-1 downto 0);
  signal cnt_blk_end          : std_logic_vector(log2(BLOCK_SIZE)-1 downto 0);
  signal blk_end_int          : std_logic;

  signal prev_write_addr      : std_logic_vector(log2(ITEMS) downto 0);
  signal prev_write_addr_next : std_logic_vector(log2(ITEMS) downto 0);

  signal addr_store           : std_logic;
  signal addr_load            : std_logic;
  signal new_read_addr        : std_logic_vector(log2(ITEMS) downto 0);
  signal new_read_addr_next   : std_logic_vector(log2(ITEMS) downto 0);
  signal addr_valid           : std_logic;
  signal fifo_full            : std_logic;
  signal fifo_status          : std_logic_vector(log2(MAX_BLOCKS) downto 0);

-- ----------------------------------------------------------------------------
begin

memory : entity work.FIFO_MEM 
  generic map (
    MEM_TYPE   => MAIN_MEM,
    LATENCY    => LATENCY,
    ITEMS      => ITEMS,
    ITEM_WIDTH => ITEM_WIDTH
  )
  port map (
    CLKW       => CLK,
    WRITE_EN   => write_allow,
    WRITE_ADDR => reg_write_addr(ADDR_RANGE),
    DI         => DI,

    CLKR       => CLK,
    PIPE_EN    => mem_pipe_en,
    READ_EN    => mem_read_allow,
    RE_ADDR    => reg_read_addr(ADDR_RANGE),
    DO         => DO,
    DO_DV      => sig_dv,
    ADDR_OUT   => open,

    RESET      => RESET
  );

PREFETCH_MODE: if (PREFETCH = true) generate

  -- prefetch logic
  process(RD, sig_dv)
  begin
    mem_pipe_en <= RD;
    sig_rd      <= RD;
    if (sig_dv = '0') then
      mem_pipe_en <= '1';
      sig_rd      <= '1';
    end if;
  end process;

  WR_DISCARD_PREFETCH: if ((discard = WriteDiscard) or
                           (discard = WriteReadDiscard)) generate
    mem_read_allow <= (not reg_empty) and addr_valid;
  end generate;

  NO_WR_DISCARD_PREFETCH: if ((discard = NoDiscard) or
                              (discard = ReadDiscard)) generate
    mem_read_allow <= not reg_empty;
  end generate;

end generate;


NONPREFETCH_MODE: if (PREFETCH = false) generate

  sig_rd         <= RD;
  mem_pipe_en    <= '1';
  mem_read_allow <= read_allow;

end generate;


-- control and allow logic
write_allow <= WR and (not reg_full) and (not fifo_full) and (not reg_discarding);

NO_DISCARD: if (discard = NoDiscard) generate

  wr_discard_allow <= '0';
  rd_discard_allow <= '0';

  read_allow <= sig_rd and (not reg_empty);

end generate;

WRITE_DISCARD: if (discard = WriteDiscard) generate

  wr_discard_allow <= WR_DISCARD;
  rd_discard_allow <= '0';

  read_allow <= sig_rd and (not reg_empty) and addr_valid;

end generate;

READ_DISCARD: if (discard = ReadDiscard) generate

  wr_discard_allow <= '0';
  rd_discard_allow <= RD_DISCARD and (not reg_empty);

  read_allow <= sig_rd and (not reg_empty);

end generate;

BOTH_DISCARDS: if (discard = WriteReadDiscard) generate

  wr_discard_allow <= WR_DISCARD;
  rd_discard_allow <= RD_DISCARD and (not reg_empty) and addr_valid;

  read_allow <= sig_rd and addr_valid and (not reg_empty);

end generate;


FIXED_BLK_SIZE: if (BLOCK_TYPE = fixed_size) generate

  -- addr FIFO logic
  fifo_full  <= '0';
  new_read_addr <= reg_read_addr + (BLOCK_SIZE - cnt_blk_finish);

  -- cnt_blk_end counter
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        cnt_blk_end <= conv_std_logic_vector(1, cnt_blk_end'length);
      else
        if ((write_allow = '1') or (reg_discarding = '1')) then
          cnt_blk_end <= cnt_blk_end + 1;
          if (cnt_blk_end = conv_std_logic_vector(BLOCK_SIZE-1, log2(BLOCK_SIZE))) then
            cnt_blk_end <= (others => '0');
          end if;
        end if;
      end if;
    end if;
  end process;

  -- blk_end_int signal
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (cnt_blk_end = conv_std_logic_vector(BLOCK_SIZE-1, log2(BLOCK_SIZE))) then
        blk_end_int <= '1';
      else
        blk_end_int <= '0';
      end if;
    end if;
  end process;

  -- fifo_status counter (simulates addr_fifo)
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        fifo_status <= (others => '0');
      else
        if ((blk_end_int = '1') and (reg_finish(LATENCY-1) = '0')) then
          fifo_status <= fifo_status + 1;
        end if;
        if ((blk_end_int = '0') and (reg_finish(LATENCY-1) = '1')) then
          fifo_status <= fifo_status - 1;
        end if;
      end if;
    end if;
  end process;

  -- addr_valid
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        addr_valid <= '0';
      else
        if ((blk_end_int = '1') and (reg_finish(LATENCY-1) = '0')) then
            addr_valid <= '1';
        elsif ((blk_end_int = '0') and (reg_finish(LATENCY-1) = '1') and
               (fifo_status = conv_std_logic_vector(1, log2(BLOCK_SIZE)))) then
          addr_valid <= '0';
        end if;
      end if;
    end if;
  end process;

  -- cnt_blk_finish counter
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        cnt_blk_finish <= (others => '0');
      else
        if (read_allow = '1') then
          cnt_blk_finish <= cnt_blk_finish + 1;
        end if;
        if ((cnt_blk_finish = conv_std_logic_vector(BLOCK_SIZE-1, log2(BLOCK_SIZE))) or
            (rd_discard_allow = '1')) then
          cnt_blk_finish <= (others => '0');
        end if;
      end if;
    end if;
  end process;

  -- sig_finish
  process(read_allow, cnt_blk_finish, rd_discard_allow)
  begin
    if ((read_allow = '1') and
       ((cnt_blk_finish = conv_std_logic_vector(BLOCK_SIZE-1, log2(BLOCK_SIZE))) or
        (rd_discard_allow = '1'))) then
      sig_finish <= '1';
    else
      sig_finish <= '0';
    end if;
  end process;

end generate;


VARIABLE_BLK_SIZE: if (BLOCK_TYPE = variable_size) generate

  addr_fifo: entity work.FIFO_SYNC_ORD
    generic map (
      MEM_TYPE   => ADDR_MEM,
      LATENCY    => 1,
      ITEMS      => MAX_BLOCKS,
      ITEM_WIDTH => log2(ITEMS)+1,
      PREFETCH   => true
    )
    port map (   
      CLK    => CLK, 
      RESET  => RESET,

      WR     => addr_store,
      DI     => cnt_write_addr,
      
      RD     => addr_load,
      DO     => new_read_addr,
      DO_DV  => addr_valid,

      FULL   => fifo_full,
      EMPTY  => open,
      STATUS => fifo_status
    );

  -- addr store
  process(write_allow, blk_end_int, sig_discarding)
  begin
    if ((write_allow = '1') and (blk_end_int = '1') and
        (sig_discarding = '0')) then
      addr_store <= '1';
    else
      addr_store <= '0';
    end if;
  end process;

  -- addr load
  addr_load <= sig_finish or rd_discard_allow;

  -- blk_end_int signal
  blk_end_int <= BLK_END;

  -- sig_finish
  process(read_allow, new_read_addr, cnt_read_addr, rd_discard_allow)
  begin
    if ((read_allow = '1') and
        (new_read_addr = cnt_read_addr) and (rd_discard_allow = '0')) then
      sig_finish <= '1';
    else
      sig_finish <= '0';
    end if;
  end process;

end generate;

-- reg_ready
process(CLK)
begin
 if ((CLK'event) and (CLK = '1')) then
   if (RESET = '1') then
     reg_ready <= '0';
   else
     if ((blk_end_int = '1') and (write_allow = '1')) then
       reg_ready <= '1';
     elsif ((mem_pipe_en = '1') and
            ((fifo_status = conv_std_logic_vector(0, log2(MAX_BLOCKS)+1)) or
            ((fifo_status = conv_std_logic_vector(1, log2(MAX_BLOCKS)+1))
              and (addr_valid = '0')))) then
       reg_ready <= '0';
     end if;
   end if;
 end if;
end process;

-- new_read_addr next value
process(new_read_addr)
begin
  if (new_read_addr(ADDR_RANGE) = conv_std_logic_vector(ITEMS-1, ADDR_WIDTH+1)) then
    new_read_addr_next(ADDR_RANGE) <= (others => '0');
    new_read_addr_next((ADDR_WIDTH+1)) <= not new_read_addr(ADDR_WIDTH+1);
  else
    new_read_addr_next <= new_read_addr + 1;
  end if;
end process;

-- reg_finish (to latency pipeline)
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (RESET = '1') then
      reg_finish(0) <= '0';
    else
      if (mem_pipe_en = '1') then
        reg_finish(0) <= sig_finish;
      end if;
    end if;
  end if;
end process;

gen_latency_higher_than_1: if (LATENCY > 1) generate
  gen_latency_pipeline: for j in 1 to LATENCY generate
    process(CLK)
    begin
      if ((CLK'event) and (CLK = '1')) then
        if (mem_pipe_en = '1') then
          reg_finish(j) <= reg_finish(j-1);
        end if;
      end if;
    end process;
  end generate;
end generate;

-- reg_discarding process
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (RESET = '1') then
      reg_discarding <= '0';
    else
      if (wr_discard_allow = '1') then
        reg_discarding <= '1';
      end if;
      if ((blk_end_int = '1') and (WR = '1')) then
        reg_discarding <= '0';
      end if;
    end if;
  end if;
end process;

sig_discarding <= wr_discard_allow or reg_discarding;

-- prev_write_addr register
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (RESET = '1') then
      prev_write_addr <= (others => '0');
    else
      if ((write_allow = '1') and (blk_end_int = '1') and
          (sig_discarding = '0')) then
        prev_write_addr <= cnt_write_addr;
      end if;
    end if;
  end if;
end process;

-- next prev_write_addr
process(prev_write_addr)
begin
  if (prev_write_addr(ADDR_RANGE) = conv_std_logic_vector(ITEMS-1, ADDR_WIDTH+1)) then
    prev_write_addr_next(ADDR_RANGE)   <= (others => '0');
    prev_write_addr_next(ADDR_WIDTH+1) <= not prev_write_addr(ADDR_WIDTH+1);
  else
    prev_write_addr_next <= prev_write_addr + 1;
  end if;
end process;

-- multiplexor mux_cnt_write_addr
process(wr_discard_allow, prev_write_addr_next, cnt_write_addr_next)
begin
  if (wr_discard_allow = '1') then
    mux_cnt_write_addr <= prev_write_addr_next;
  else
    mux_cnt_write_addr <= cnt_write_addr_next;
  end if;
end process;

-- cnt_write_addr register
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (RESET = '1') then
      cnt_write_addr <= conv_std_logic_vector(1, cnt_write_addr'length);
    else
      if ((write_allow = '1') or (wr_discard_allow = '1')) then
        cnt_write_addr <= mux_cnt_write_addr;
      end if;
    end if;
  end if;
end process;

-- next cnt_write_addr
process(cnt_write_addr)
begin
  if (cnt_write_addr(ADDR_RANGE) = conv_std_logic_vector(ITEMS-1, ADDR_WIDTH+1)) then
    cnt_write_addr_next(ADDR_RANGE)   <= (others => '0');
    cnt_write_addr_next(ADDR_WIDTH+1) <= not cnt_write_addr(ADDR_WIDTH+1);
  else
    cnt_write_addr_next <= cnt_write_addr + 1;
  end if;
end process;


-- multiplexor mux_reg_write_addr
process(wr_discard_allow, prev_write_addr, cnt_write_addr)
begin
  if (wr_discard_allow = '1') then
    mux_reg_write_addr <= prev_write_addr;
  else
    mux_reg_write_addr <= cnt_write_addr;
  end if;
end process;

-- reg_write_addr register
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (RESET = '1') then
      reg_write_addr <= (others => '0');
    else
      if ((write_allow = '1') or (wr_discard_allow = '1')) then
        reg_write_addr <= mux_reg_write_addr;
      end if;
    end if;
  end if;
end process;


-- multiplexor mux_cnt_read_addr
mux_read_addr_sel <= addr_valid & rd_discard_allow;

process(mux_read_addr_sel, prev_write_addr_next, new_read_addr_next, cnt_read_addr_next)
begin
  case mux_read_addr_sel is
    when "01" => mux_cnt_read_addr <= prev_write_addr_next;
    when "11" => mux_cnt_read_addr <= new_read_addr_next;
    when others => mux_cnt_read_addr <= cnt_read_addr_next;
end case;
end process;

-- cnt_read_addr register
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (RESET = '1') then
      cnt_read_addr <= conv_std_logic_vector(1, cnt_read_addr'length);
    else
      if ((read_allow = '1') or (rd_discard_allow = '1')) then
        cnt_read_addr <= mux_cnt_read_addr;
      end if;
    end if;
  end if;
end process;

-- next cnt_read_addr
process(cnt_read_addr)
begin
  if (cnt_read_addr(ADDR_RANGE) = conv_std_logic_vector(ITEMS-1, ADDR_WIDTH+1)) then
    cnt_read_addr_next(ADDR_RANGE)   <= (others => '0');
    cnt_read_addr_next(ADDR_WIDTH+1) <= not cnt_read_addr(ADDR_WIDTH+1);
  else
    cnt_read_addr_next <= cnt_read_addr + 1;
  end if;
end process;

-- multiplexor mux_reg_read_addr
process(mux_read_addr_sel, prev_write_addr, new_read_addr, cnt_read_addr)
begin
  case mux_read_addr_sel is
    when "01" => mux_reg_read_addr <= prev_write_addr;
    when "11" => mux_reg_read_addr <= new_read_addr;
    when others => mux_reg_read_addr <= cnt_read_addr;
  end case;
end process;

-- reg_read_addr register
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (RESET = '1') then
      reg_read_addr <= (others => '0');
    else
      if ((read_allow = '1') or (rd_discard_allow = '1')) then
        reg_read_addr <= mux_reg_read_addr;
      end if;
    end if;
  end if;
end process;

-- empty, full logic
process(write_allow, read_allow, cnt_read_addr, reg_write_addr)
begin
  if ((write_allow = '0') and (read_allow = '1') and
      (cnt_read_addr = reg_write_addr)) then
    sig_empty <= '1';
  else
    sig_empty <= '0';
  end if;
end process;

process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (RESET = '1') then
      reg_empty <= '1';
    else
      if ((write_allow = '1') or (read_allow = '1') or
          (wr_discard_allow = '1') or (rd_discard_allow = '1')) then
        reg_empty <= sig_empty;
      end if;
    end if;
  end if;
end process;

process(write_allow, wr_discard_allow, read_allow, reg_read_addr, mux_reg_write_addr)
begin
  if (((write_allow = '1') or (wr_discard_allow = '1')) and (read_allow = '0') and
      (reg_read_addr(ADDR_RANGE) = mux_reg_write_addr(ADDR_RANGE)) and
      (reg_read_addr(ADDR_WIDTH+1) /= mux_reg_write_addr(ADDR_WIDTH+1))) then
    sig_full <= '1';
  else
    sig_full <= '0';
  end if;
end process;

process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (RESET = '1') then
      reg_full <= '0';
    else
      if ((write_allow = '1') or (read_allow = '1') or
          (wr_discard_allow = '1') or (rd_discard_allow = '1')) then
        reg_full <= sig_full;
      end if;
    end if;
  end if;
end process;

STATUS_POW2WIDTH : if (2**log2(ITEMS) = ITEMS) generate
  STATUS <= reg_write_addr - reg_read_addr;
end generate;

STATUS_NOTPOW2WIDTH : if (2**log2(ITEMS) /= ITEMS) generate
  process(reg_write_addr, reg_read_addr)
  begin
    if (reg_read_addr(ADDR_WIDTH+1) = reg_write_addr(ADDR_WIDTH+1)) then
      STATUS <= '0' & (reg_write_addr(ADDR_RANGE) - reg_read_addr(ADDR_RANGE));
    else 
      STATUS <= '0' & (ITEMS - (reg_read_addr(ADDR_RANGE) - reg_write_addr(ADDR_RANGE)));
    end if;
  end process;
end generate;

-- ----------------------------------------------------------------------------
-- interface mapping
FULL       <= reg_full;
EMPTY      <= reg_empty;
BLK_FINISH <= reg_finish(LATENCY-1);
BLK_READY  <= reg_ready;
DO_DV      <= sig_dv;

end architecture;
-- ----------------------------------------------------------------------------
