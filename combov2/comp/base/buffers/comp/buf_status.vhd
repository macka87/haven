--
-- buf_status.vhd - giving empty, full and status signals (all registered) from address counters
-- Copyright (C) 2008 CESNET
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

-- ----------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------
entity BUF_STATUS is
  generic(
    -- number of items that can be addressed
    ITEMS       : integer := 4;
    -- indicates that more than one item can be written in one cycle
    MULTI_WRITE : boolean := false;
    -- indicates that more than one item can be read in one cycle
    MULTI_READ  : boolean := false
  );

  port(
    CLK      : in  std_logic;
    RESET    : in  std_logic;

    -- Input
    WRITE_EN    : in  std_logic;
    READ_EN     : in  std_logic;
    WR_CNT      : in  std_logic_vector(log2(ITEMS) downto 0);
    WR_REG      : in  std_logic_vector(log2(ITEMS) downto 0);
    RD_CNT      : in  std_logic_vector(log2(ITEMS) downto 0);
    RD_REG      : in  std_logic_vector(log2(ITEMS) downto 0);

    -- Output
    EMPTY       : out std_logic;
    FULL        : out std_logic;
    STATUS      : out std_logic_vector(log2(ITEMS+1)-1 downto 0)
  );
end entity;

-- ----------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------
architecture behavioral of BUF_STATUS is

  subtype ADDR_RANGE is natural range log2(ITEMS)-1 downto 0;

  signal empty_int     : std_logic;
  signal full_int      : std_logic;

-- ----------------------------------------------------------------------------
begin

  -- empty signal
  process(WRITE_EN, READ_EN, WR_REG, RD_CNT)
  begin
    if ((WRITE_EN = '0') and (READ_EN = '1') and (WR_REG = RD_CNT)) then
      empty_int <= '1';
    else
      empty_int <= '0';
    end if;
  end process;

  -- empty register
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        EMPTY <= '1';
      else
        if ((WRITE_EN = '1') or (READ_EN = '1')) then
          EMPTY <= empty_int;
        end if;
      end if;
    end if;
  end process;

  -- full signal
  process(WRITE_EN, READ_EN, WR_CNT, RD_REG)
  begin
    if ((WRITE_EN = '1') and (READ_EN = '0') and
        (WR_CNT(log2(ITEMS)) /= RD_REG(log2(ITEMS))) and
        (WR_CNT(ADDR_RANGE) = RD_REG(ADDR_RANGE))) then
      full_int <= '1';
    else
      full_int <= '0';
    end if;
  end process;

  -- full register
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        FULL <= '0';
      else
        if ((WRITE_EN = '1') or (READ_EN = '1')) then
          FULL <= full_int;
        end if;
      end if;
    end if;
  end process;

  -- status signals

  status_is2pow: if (2**log2(ITEMS) = ITEMS) generate

    normal: if ((not MULTI_WRITE) and (not MULTI_READ)) generate
      process(CLK)
      begin
        if ((CLK'event) and (CLK = '1')) then
          if (RESET = '1') then
            STATUS <= (others => '0');
          else
            if ((WRITE_EN = '1') and (READ_EN = '0')) then
              STATUS <= WR_CNT - RD_REG;
            end if;
            if ((WRITE_EN = '0') and (READ_EN = '1')) then
              STATUS <= WR_REG - RD_CNT;
            end if;
          end if;
        end if;
      end process;
    end generate;

    multiple_write: if (MULTI_WRITE and (not MULTI_READ)) generate
      process(CLK)
      begin
        if ((CLK'event) and (CLK = '1')) then
          if (RESET = '1') then
            STATUS <= (others => '0');
          else
            if (READ_EN = '1') then
              STATUS <= WR_REG - RD_CNT;
            elsif (WRITE_EN = '1') then
              STATUS <= WR_CNT - RD_REG;
            end if;
          end if;
        end if;
      end process;
    end generate;

    multiple_read: if ((not MULTI_WRITE) and MULTI_READ) generate
      process(CLK)
      begin
        if ((CLK'event) and (CLK = '1')) then
          if (RESET = '1') then
            STATUS <= (others => '0');
          else
            if (WRITE_EN = '1') then
              STATUS <= WR_CNT - RD_REG;
            elsif (READ_EN = '1') then
              STATUS <= WR_REG - RD_CNT;
            end if;
          end if;
        end if;
      end process;
    end generate;

    multiple_both: if (MULTI_WRITE and MULTI_READ) generate
      process(CLK)
      begin
        if ((CLK'event) and (CLK = '1')) then
          if (RESET = '1') then
            STATUS <= (others => '0');
          else
            if ((WRITE_EN = '1') and (READ_EN = '0')) then
              STATUS <= WR_CNT - RD_REG;
            end if;
            if ((WRITE_EN = '0') and (READ_EN = '1')) then
              STATUS <= WR_REG - RD_CNT;
            end if;
            if ((WRITE_EN = '1') and (READ_EN = '1')) then
              STATUS <= WR_CNT - RD_CNT;
            end if;
          end if;
        end if;
      end process;
    end generate;

  end generate;

  status_not2pow: if (2**log2(ITEMS) /= ITEMS) generate

    normal: if ((not MULTI_WRITE) and (not MULTI_READ)) generate
      process(CLK)
      begin
        if ((CLK'event) and (CLK = '1')) then
          if (RESET = '1') then
            STATUS <= (others => '0');
          else
            if ((WRITE_EN = '1') and (READ_EN = '0')) then
              if (WR_CNT(log2(ITEMS)) /= RD_REG(log2(ITEMS))) then
                STATUS <= ITEMS - (RD_REG(ADDR_RANGE) - WR_CNT(ADDR_RANGE));
              else
                STATUS <= WR_CNT(ADDR_RANGE) - RD_REG(ADDR_RANGE);
              end if;
            end if;
            if ((WRITE_EN = '0') and (READ_EN = '1')) then
              if (WR_REG(log2(ITEMS)) /= RD_CNT(log2(ITEMS))) then
                STATUS <= ITEMS - (RD_CNT(ADDR_RANGE) - WR_REG(ADDR_RANGE));
              else
                STATUS <= WR_REG(ADDR_RANGE) - RD_CNT(ADDR_RANGE);
              end if;
            end if;
          end if;
        end if;
      end process;
    end generate;

    multiple_write: if (MULTI_WRITE and (not MULTI_READ)) generate
      process(CLK)
      begin
        if ((CLK'event) and (CLK = '1')) then
          if (RESET = '1') then
            STATUS <= (others => '0');
          else
            if (READ_EN = '1') then
              if (WR_REG(log2(ITEMS)) /= RD_CNT(log2(ITEMS))) then
                STATUS <= ITEMS - (RD_CNT(ADDR_RANGE) - WR_REG(ADDR_RANGE));
              else
                STATUS <= WR_REG(ADDR_RANGE) - RD_CNT(ADDR_RANGE);
              end if;
            elsif (WRITE_EN = '1') then
              if (WR_CNT(log2(ITEMS)) /= RD_REG(log2(ITEMS))) then
                STATUS <= ITEMS - (RD_REG(ADDR_RANGE) - WR_CNT(ADDR_RANGE));
              else
                STATUS <= WR_CNT(ADDR_RANGE) - RD_REG(ADDR_RANGE);
              end if;
            end if;
          end if;
        end if;
      end process;
    end generate;

    multiple_read: if ((not MULTI_WRITE) and MULTI_READ) generate
      process(CLK)
      begin
        if ((CLK'event) and (CLK = '1')) then
          if (RESET = '1') then
            STATUS <= (others => '0');
          else
            if (WRITE_EN = '1') then
              if (WR_CNT(log2(ITEMS)) /= RD_REG(log2(ITEMS))) then
                STATUS <= ITEMS - (RD_REG(ADDR_RANGE) - WR_CNT(ADDR_RANGE));
              else
                STATUS <= WR_CNT(ADDR_RANGE) - RD_REG(ADDR_RANGE);
              end if;
            elsif (READ_EN = '1') then
              if (WR_REG(log2(ITEMS)) /= RD_CNT(log2(ITEMS))) then
                STATUS <= ITEMS - (RD_CNT(ADDR_RANGE) - WR_REG(ADDR_RANGE));
              else
                STATUS <= WR_REG(ADDR_RANGE) - RD_CNT(ADDR_RANGE);
              end if;
            end if;
          end if;
        end if;
      end process;
    end generate;

    multiple_both: if (MULTI_WRITE and MULTI_READ) generate
      process(CLK)
      begin
        if ((CLK'event) and (CLK = '1')) then
          if (RESET = '1') then
            STATUS <= (others => '0');
          else
            if ((WRITE_EN = '1') and (READ_EN = '0')) then
              if (WR_CNT(log2(ITEMS)) /= RD_REG(log2(ITEMS))) then
                STATUS <= ITEMS - (RD_REG(ADDR_RANGE) - WR_CNT(ADDR_RANGE));
              else
                STATUS <= WR_CNT(ADDR_RANGE) - RD_REG(ADDR_RANGE);
              end if;
            end if;
            if ((WRITE_EN = '0') and (READ_EN = '1')) then
              if (WR_REG(log2(ITEMS)) /= RD_CNT(log2(ITEMS))) then
                STATUS <= ITEMS - (RD_CNT(ADDR_RANGE) - WR_REG(ADDR_RANGE));
              else
                STATUS <= WR_REG(ADDR_RANGE) - RD_CNT(ADDR_RANGE);
              end if;
            end if;
            if ((WRITE_EN = '1') and (READ_EN = '1')) then
              if (WR_CNT(log2(ITEMS)) /= RD_CNT(log2(ITEMS))) then
                STATUS <= ITEMS - (RD_CNT(ADDR_RANGE) - WR_CNT(ADDR_RANGE));
              else
                STATUS <= WR_CNT(ADDR_RANGE) - RD_CNT(ADDR_RANGE);
              end if;
            end if;
          end if;
        end if;
      end process;
    end generate;

  end generate;

end architecture;
-- ----------------------------------------------------------------------------
