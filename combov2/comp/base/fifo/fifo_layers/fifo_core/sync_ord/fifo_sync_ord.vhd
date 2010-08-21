--
-- fifo_sync_ord.vhd: Synchronous Ordinary Core FIFO
-- Copyright (C) 2009 CESNET
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
architecture behavioral of FIFO_SYNC_ORD is

  constant ADDR_WIDTH : integer := log2(ITEMS)-1;
  constant ADDR_MSB   : integer := log2(ITEMS);

  subtype ADDR_RANGE is natural range ADDR_WIDTH downto 0;

  signal sig_rd              : std_logic;
  signal sig_dv              : std_logic;
  signal mem_pipe_en         : std_logic;
  signal mem_read_allow      : std_logic;

  signal write_allow         : std_logic;
  signal read_allow          : std_logic;
  signal cnt_write_addr_rst  : std_logic;
  signal cnt_write_addr_low  : std_logic_vector(log2(ITEMS)-1 downto 0);
  signal cnt_write_addr_high : std_logic;
  signal cnt_write_addr      : std_logic_vector(log2(ITEMS) downto 0);
  signal reg_write_addr      : std_logic_vector(log2(ITEMS) downto 0);
  signal cnt_read_addr_rst   : std_logic;
  signal cnt_read_addr_low   : std_logic_vector(log2(ITEMS)-1 downto 0);
  signal cnt_read_addr_high  : std_logic;
  signal cnt_read_addr       : std_logic_vector(log2(ITEMS) downto 0);
  signal reg_read_addr       : std_logic_vector(log2(ITEMS) downto 0);

  signal sig_empty           : std_logic;
  signal reg_empty           : std_logic;
  signal sig_full            : std_logic;
  signal reg_full            : std_logic;
  signal sig_status          : std_logic_vector(log2(ITEMS) downto 0);

  signal sig_reset           : std_logic;
  signal reg_reset           : std_logic;

-- ----------------------------------------------------------------------------
begin

   sig_reset <= RESET;

   -- register for reset
   reg_reset_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         reg_reset <= sig_reset;
      end if;
   end process;


   memory : entity work.FIFO_MEM 
   generic map (
     MEM_TYPE   => MEM_TYPE,
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
 
     RESET      => reg_reset   -- BEWARE: I used latched reset so that the
                               -- memory would clear in the same time as
                               -- control registers
   );

-- prefetch logic
GEN_NON_PREFETCH : if (PREFETCH = FALSE) generate
  sig_rd         <= RD;
  mem_pipe_en    <= '1';
  mem_read_allow <= read_allow;
end generate;

GEN_PREFETCH : if (PREFETCH = TRUE) generate
  process(RD, sig_dv)
  begin
    mem_pipe_en <= RD;
    sig_rd      <= RD;
    if (sig_dv = '0') then
      mem_pipe_en <= '1';
      sig_rd      <= '1';
    end if;
  end process;

  mem_read_allow <= not reg_empty;
end generate;

-- allow logic
write_allow <= WR     and (not reg_full);
read_allow  <= sig_rd and (not reg_empty);

-- address counters and registers ---------------------------------------------
-- write address counter
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (reg_reset = '1') then
      cnt_write_addr_low <= conv_std_logic_vector(1, cnt_write_addr_low'length);
    else
      if (write_allow = '1') then
        if (cnt_write_addr_rst = '1') then
          cnt_write_addr_low <= (others => '0');
        else
          cnt_write_addr_low <= cnt_write_addr_low + 1;
        end if;
      end if;
    end if;
  end if;
end process;

process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (reg_reset = '1') then
      cnt_write_addr_high <= '0';
    else
      if (write_allow = '1') then
        if (cnt_write_addr_rst = '1') then
          cnt_write_addr_high <= not cnt_write_addr_high;
        end if;
      end if;
    end if;
  end if;
end process;

process(cnt_write_addr_low)
begin
  if (cnt_write_addr_low = conv_std_logic_vector(ITEMS-1, cnt_write_addr_low'length)) then
    cnt_write_addr_rst <= '1';
  else
    cnt_write_addr_rst <= '0';
  end if;
end process;

cnt_write_addr <= cnt_write_addr_high & cnt_write_addr_low;

-- write address register
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (reg_reset = '1') then
      reg_write_addr <= (others => '0');
    else
      if (write_allow = '1') then
        reg_write_addr <= cnt_write_addr;
      end if;
    end if;
  end if;
end process;

-- read address counter
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (reg_reset = '1') then
      cnt_read_addr_low <= conv_std_logic_vector(1, cnt_read_addr_low'length);
    else
      if (read_allow = '1') then
        if (cnt_read_addr_rst = '1') then
          cnt_read_addr_low <= (others => '0');
        else
          cnt_read_addr_low <= cnt_read_addr_low + 1;
        end if;
      end if;
    end if;
  end if;
end process;

process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (reg_reset = '1') then
      cnt_read_addr_high <= '0';
    else
      if (read_allow = '1') then
        if (cnt_read_addr_rst = '1') then
          cnt_read_addr_high <= not cnt_read_addr_high;
        end if;
      end if;
    end if;
  end if;
end process;

process(cnt_read_addr_low)
begin
  if (cnt_read_addr_low = conv_std_logic_vector(ITEMS-1, cnt_read_addr_low'length)) then
    cnt_read_addr_rst <= '1';
  else
    cnt_read_addr_rst <= '0';
  end if;
end process;

cnt_read_addr <= cnt_read_addr_high & cnt_read_addr_low;

-- read address register
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (reg_reset = '1') then
      reg_read_addr <= (others => '0');
    else
      if (read_allow = '1') then
        reg_read_addr <= cnt_read_addr;
      end if;
    end if;
  end if;
end process;

-- status logic ---------------------------------------------------------------
-- empty
process(write_allow, read_allow, reg_write_addr, cnt_read_addr)
begin
  if ((write_allow = '0') and (read_allow = '1') and
      (reg_write_addr = cnt_read_addr)) then
    sig_empty <= '1';
  else
    sig_empty <= '0';
  end if;
end process;

process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (reg_reset = '1') then
      reg_empty <= '1';
    else
      if ((write_allow = '1') or (read_allow = '1')) then
        reg_empty <= sig_empty;
      end if;
    end if;
  end if;
end process;

-- full
process(write_allow, read_allow, cnt_write_addr, reg_read_addr)
begin
  if ((write_allow = '1') and (read_allow = '0') and
      (cnt_write_addr(ADDR_RANGE) = reg_read_addr(ADDR_RANGE)) and
      (cnt_write_addr(ADDR_MSB) /= reg_read_addr(ADDR_MSB))) then
    sig_full <= '1';
  else
    sig_full <= '0';
  end if;
end process;

process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    if (reg_reset = '1') then
      reg_full <= '0';
    else
      if ((write_allow = '1') or (read_allow = '1')) then
        reg_full <= sig_full;
      end if;
    end if;
  end if;
end process;

-- status
STATUS_POW2 : if (2**log2(ITEMS) = ITEMS) generate
  sig_status <= reg_write_addr - reg_read_addr;
end generate;

STATUS_NOT_POW2 : if (2**log2(ITEMS) /= ITEMS) generate
  process(reg_write_addr, reg_read_addr)
  begin
    if (reg_read_addr(ADDR_MSB) = reg_write_addr(ADDR_MSB)) then
      sig_status <= '0' & (reg_write_addr(ADDR_RANGE) - reg_read_addr(ADDR_RANGE));
    else 
      sig_status <= '0' & (ITEMS - (reg_read_addr(ADDR_RANGE) - reg_write_addr(ADDR_RANGE)));
    end if;
  end process;
end generate;

-- interface mapping ----------------------------------------------------------
DO_DV  <= sig_dv;
EMPTY  <= reg_empty OR (RESET OR reg_reset);
FULL   <= reg_full  OR (RESET OR reg_reset);
STATUS <= sig_status;

end architecture;
-- ----------------------------------------------------------------------------
