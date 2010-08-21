--
-- swt_fifo_ctrl.vhd: FIFO control logic for SW_TXBUF
--                - synchronous write, asynchronous read
-- Copyright (C) 2003 CESNET
-- Author(s):  Pecenka Tomas pecenka@liberouter.org
--             Pus Viktor    pus@liberouter.org
--             Kosek Martin  kosek@liberouter.org
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;

-- auxilary functions and constant needed to evaluate generic address etc.
use WORK.distmem_func.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity SWT_FIFO_CTRL is
   generic (
      -- Distributed RAM type, only 16, 32, 64 bits
      DISTMEM_TYPE   : integer := 16;
      -- Set number of items in FIFO here
      ITEMS          : integer;
      STATUS_WIDTH   : integer
   );
   port(
      RESET    : in std_logic;  -- Global reset signal
      CLK      : in std_logic;  -- Global clock signal

      -- Write interface
      WADDR    : out std_logic_vector(LOG2(ITEMS)-1 downto 0);
      WRITE_REQ: in std_logic;
      FULL     : out std_logic;
      STATUS   : out std_logic_vector(STATUS_WIDTH-1 downto 0);

      -- Read interface
      RADDR    : out std_logic_vector(LOG2(ITEMS)-1 downto 0);
      READ_REQ : in std_logic;
      EMPTY    : out std_logic
   );
end entity SWT_FIFO_CTRL;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of SWT_FIFO_CTRL is

   -- Number of address bits
   constant FADDR       : integer := LOG2(ITEMS)-1;

   signal write_allow         : std_logic;
   signal read_allow          : std_logic;
   signal empty_int           : std_logic;
   signal full_int            : std_logic;

   signal sig_dv              : std_logic;
   
   signal reg_empty           : std_logic;
   signal reg_full            : std_logic;

   signal cnt_write_addr      : std_logic_vector((FADDR+1) downto 0);
   signal cnt_read_addr       : std_logic_vector((FADDR+1) downto 0);
   signal reg_read_addr       : std_logic_vector((FADDR+1) downto 0);
   signal reg_write_addr      : std_logic_vector((FADDR+1) downto 0);
	
	signal cnt_write_addr_low  : std_logic_vector(FADDR downto 0);
	signal cnt_write_addr_high : std_logic;
	signal cnt_write_addr_high_next:std_logic;
	signal cnt_write_addr_load_enable:std_logic;

	signal cnt_read_addr_low   : std_logic_vector(FADDR downto 0);
	signal cnt_read_addr_high  : std_logic;
	signal cnt_read_addr_high_next:std_logic;
	signal cnt_read_addr_load_enable:std_logic;

   signal cnt_diff            : std_logic_vector((FADDR+1) downto 0);
   signal cnt_diff_ce         : std_logic;
   signal cnt_diff_dir        : std_logic;

-- ----------------------------------------------------------------------------
begin

-- ----------------------------------------------------------------------------
--                   Address counters and registers
-- ----------------------------------------------------------------------------
-- cnt_write_addr_low counter
process(RESET, CLK)
begin
   if (RESET = '1') then
      cnt_write_addr_low <= conv_std_logic_vector(1, cnt_write_addr_low'length);
   elsif (CLK'event AND CLK = '1') then
      if (write_allow = '1') then
			if cnt_write_addr_load_enable = '1' then
				cnt_write_addr_low <= (others => '0');
			else
				cnt_write_addr_low <= cnt_write_addr_low + 1;
			end if;
      end if;
   end if;
end process;
										
process(cnt_write_addr_low)
begin
	if cnt_write_addr_low = conv_std_logic_vector(ITEMS-1, cnt_write_addr_low'length) then
		cnt_write_addr_load_enable <= '1';
	else
		cnt_write_addr_load_enable <= '0';
	end if;
end process;
										
process(cnt_write_addr_high, cnt_write_addr_load_enable)
begin
	if cnt_write_addr_load_enable = '1' then
		cnt_write_addr_high_next <= not cnt_write_addr_high; 
	else
		cnt_write_addr_high_next <= cnt_write_addr_high;
	end if;
end process;
	
-- cnt_write_addr_high counter	
process(RESET, CLK)
begin
   if RESET = '1' then
      cnt_write_addr_high <= '0';
   elsif CLK'event and CLK = '1' then
		if write_allow = '1' then
			cnt_write_addr_high <= cnt_write_addr_high_next;
		end if;
   end if;
end process;

cnt_write_addr <= cnt_write_addr_high & cnt_write_addr_low;


-- cnt_read_addr_low counter
process(RESET, CLK)
begin
   if (RESET = '1') then
      cnt_read_addr_low <= conv_std_logic_vector(1, cnt_read_addr_low'length);
   elsif (CLK'event AND CLK = '1') then
      if (read_allow = '1') then
			if cnt_read_addr_load_enable = '1' then
				cnt_read_addr_low <= (others => '0');
			else
				cnt_read_addr_low <= cnt_read_addr_low + 1;
			end if;
      end if;
   end if;
end process;

process(cnt_read_addr_low)
begin
	if cnt_read_addr_low = conv_std_logic_vector(ITEMS-1, cnt_read_addr_low'length) then
		cnt_read_addr_load_enable <= '1';
	else
		cnt_read_addr_load_enable <= '0';
	end if;
end process;							

process(cnt_read_addr_high, cnt_read_addr_load_enable)
begin
	if cnt_read_addr_load_enable = '1' then
		cnt_read_addr_high_next <= not cnt_read_addr_high; 
	else
		cnt_read_addr_high_next <= cnt_read_addr_high;
	end if;
end process;
									 
process(RESET, CLK)
begin
   if RESET = '1' then
      cnt_read_addr_high <= '0';
   elsif CLK'event and CLK = '1' then
		if read_allow = '1' then
			cnt_read_addr_high <= cnt_read_addr_high_next;
		end if;
   end if;
end process;

cnt_read_addr <= cnt_read_addr_high & cnt_read_addr_low;


-- reg_write_addr register
process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_write_addr <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (write_allow = '1') then
         reg_write_addr <= cnt_write_addr;
      end if;
   end if;
end process;

-- reg_read_addr register
process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_read_addr <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (read_allow = '1') then
         reg_read_addr <= cnt_read_addr;
      end if;
   end if;
end process;

-- ----------------------------------------------------------------------------
--                            Control Logic
-- ----------------------------------------------------------------------------
-- allow logic
read_allow <= READ_REQ and (not reg_empty);
write_allow <= WRITE_REQ and (not reg_full);

-- empty, full logic
process(cnt_read_addr, reg_write_addr, read_allow, write_allow)
begin
	if ((cnt_read_addr = reg_write_addr) and (read_allow = '1') and (write_allow = '0')) then
		empty_int <= '1';
	else
		empty_int <= '0';
	end if;
end process;

process(reg_read_addr, cnt_write_addr, write_allow, read_allow)
begin
	if ((reg_read_addr(FADDR downto 0) = cnt_write_addr(FADDR downto 0))
        and (reg_read_addr(FADDR+1) /= cnt_write_addr(FADDR+1))
        and (write_allow = '1') and (read_allow = '0')) then
		full_int <= '1';
	else
		full_int <= '0';
	end if;
end process;

-- reg_empty register
process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_empty <= '1';
   elsif (CLK'event AND CLK = '1') then
      if ((read_allow = '1') or (write_allow = '1')) then
         reg_empty <= empty_int;
      end if;
   end if;
end process;

-- reg_full register
process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_full <= '0';
   elsif (CLK'event AND CLK = '1') then
      if ((write_allow = '1') or (read_allow = '1')) then
         reg_full <= full_int;
      end if;
   end if;
end process;

-- cnt_diff counter
cnt_diff_ce <= read_allow xor write_allow;
cnt_diff_dir <= read_allow;

process(RESET, CLK)
begin
   if (RESET = '1') then
      cnt_diff <= conv_std_logic_vector(ITEMS, cnt_diff'length);
   elsif (CLK'event AND CLK = '1') then
      if (cnt_diff_ce = '1') then
         if (cnt_diff_dir = '1') then
            cnt_diff <= cnt_diff + 1;
         else
            cnt_diff <= cnt_diff - 1;
         end if;
      end if;
   end if;
end process;

-- ----------------------------------------------------------------------------

-- interface mapping
FULL     <= reg_full;
EMPTY    <= reg_empty;
WADDR    <= reg_write_addr(log2(ITEMS)-1 downto 0);
RADDR    <= reg_read_addr(log2(ITEMS)-1 downto 0);

GEN_STATUS1: if(STATUS_WIDTH > FADDR+2) generate
   STATUS(FADDR+1 downto 0) <= cnt_diff;
   STATUS(STATUS_WIDTH-1 downto FADDR+2) <= (others => '0');
end generate;

GEN_STATUS2: if(STATUS_WIDTH <= FADDR+2) generate
   STATUS   <= cnt_diff((FADDR+1) downto (FADDR+1)-STATUS_WIDTH+1);
end generate;

end architecture behavioral;
-- ----------------------------------------------------------------------------

