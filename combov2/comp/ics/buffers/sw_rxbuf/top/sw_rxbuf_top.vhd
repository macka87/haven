-- sw_rxbuf_top.vhd - generic entity of sw_rxbuf
-- Copyright (C) 2008 CESNET
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
entity SW_RXBUF_TOP is
  generic(
    DATA_WIDTH       : integer := 64;
    -- should be a power of 2
    -- Evailable data size for one interface (number of words DATA_WIDTH wide)
    BLOCK_SIZE       : integer := 512;
    FLOWS            : integer := 2;
    -- Total size (bytes) for one flow (interface)
    TOTAL_FLOW_SIZE  : integer := 16384
  );
  port(
    CLK           : in  std_logic;
    RESET         : in  std_logic;

    -- Write interface (FrameLinks)
    RX_DATA       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    RX_SOP_N      : in  std_logic_vector(FLOWS-1 downto 0);
    RX_EOP_N      : in  std_logic_vector(FLOWS-1 downto 0);
    RX_SOF_N      : in  std_logic_vector(FLOWS-1 downto 0);
    RX_EOF_N      : in  std_logic_vector(FLOWS-1 downto 0);
    RX_REM        : in  std_logic_vector((log2((DATA_WIDTH/FLOWS)/8)*FLOWS)-1 downto 0);
    RX_SRC_RDY_N  : in  std_logic_vector(FLOWS-1 downto 0);
    RX_DST_RDY_N  : out std_logic_vector(FLOWS-1 downto 0);

    RX_NEWLEN     : out std_logic_vector((FLOWS*16)-1 downto 0);
    RX_NEWLEN_DV  : out std_logic_vector(FLOWS-1 downto 0);
    RX_NEWLEN_RDY : in  std_logic_vector(FLOWS-1 downto 0);  -- always set to '1'
    RX_RELLEN     : in  std_logic_vector((FLOWS*16)-1 downto 0);
    RX_RELLEN_DV  : in  std_logic_vector(FLOWS-1 downto 0);

    -- Read interface (InternalBus)
    RD_ADDR       : in  std_logic_vector(31 downto 0);
    RD_BE         : in  std_logic_vector(7 downto 0);
    RD_REQ        : in  std_logic;
    RD_ARDY       : out std_logic;

    RD_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
    RD_SRC_RDY    : out std_logic;
    RD_DST_RDY    : in  std_logic
  );
end entity;

-- ----------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------
architecture behavioral of SW_RXBUF_TOP is

  constant FLOW_WIDTH : integer := DATA_WIDTH / FLOWS;
  constant RELLEN_W   : integer := log2(BLOCK_SIZE+1);
  constant DATA_BYTES : integer := log2(DATA_WIDTH/8);
  constant FLOW_BYTES : integer := FLOW_WIDTH/8;
  constant FL_BYTES_W : integer := log2(FLOW_WIDTH/8);
  constant FLOW_LSB   : integer := log2(TOTAL_FLOW_SIZE); -- where flow (interface) address starts

  subtype MEM_RANGE is natural range log2(BLOCK_SIZE)+DATA_BYTES-1 downto DATA_BYTES;
  subtype BLK_RANGE is natural range abs(log2(FLOWS)-1)+FLOW_LSB downto FLOW_LSB;

  type t_cnt is array(FLOWS-1 downto 0) of std_logic_vector(15 downto 0);

  signal data_in       : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal write         : std_logic_vector(FLOWS-1 downto 0);
  signal read_req      : std_logic;
  signal rxbuf_empty   : std_logic_vector(FLOWS-1 downto 0);
  signal rxbuf_full    : std_logic_vector(FLOWS-1 downto 0);
  signal rxbuf_valid   : std_logic;
  signal rellen        : std_logic_vector((RELLEN_W*FLOWS)-1 downto 0);
  signal cnt_counter   : t_cnt;
  signal rx_eof        : std_logic_vector(FLOWS-1 downto 0);
  signal data_end      : std_logic_vector(FLOWS-1 downto 0);
  signal newlen_dv     : std_logic_vector(FLOWS-1 downto 0);
  signal newlen        : t_cnt;

  signal buf_wr_transaction : std_logic_vector(FLOWS - 1 downto 0);
-- ----------------------------------------------------------------------------
begin

assert (DATA_WIDTH mod FLOWS = 0)
report "DATA_WIDTH / FLOWS is not an integer."
severity ERROR;

-- Check if total size is the same or more than block_size
assert (BLOCK_SIZE * (DATA_WIDTH/8) <= TOTAL_FLOW_SIZE)
report "TOTAL_FLOW_SIZE must be >= than BLOCK_SIZE * (DATA_WIDTH/8)."
severity ERROR;

rxbuf_i : entity work.NFIFO2MEM
  generic map (
    DATA_WIDTH => DATA_WIDTH,
    FLOWS      => FLOWS,
    BLOCK_SIZE => BLOCK_SIZE,
    LUT_MEMORY => false,
    GLOB_STATE => true
  ) 
  port map (
    CLK        => CLK,
    RESET      => RESET,

    DATA_IN    => data_in,
    WRITE      => write,

    DATA_OUT   => RD_DATA,
    DATA_VLD   => rxbuf_valid,
    BLOCK_ADDR => RD_ADDR(BLK_RANGE),
    RD_ADDR    => RD_ADDR(MEM_RANGE),
    REL_LEN    => rellen,
    REL_LEN_DV => RX_RELLEN_DV,
    READ       => RD_REQ,
    PIPE_EN    => RD_DST_RDY,
 
    EMPTY      => rxbuf_empty,
    FULL       => rxbuf_full,
    STATUS     => open
  );

-- -- read request
-- process(RD_ADDR, RD_REQ, RD_DST_RDY)
-- begin
--   if (RD_ADDR(31 downto log2(FLOWS)+FLOW_LSB) = conv_std_logic_vector(0, 32-(log2(FLOWS)+FLOW_LSB))) then
--     read_req <= RD_REQ and RD_DST_RDY;
--   else
--     read_req <= '0';
--   end if;
-- end process;

-- EOF for filler
rx_eof <= (not RX_EOF_N) and (not RX_SRC_RDY_N);

-- align data to 8 bytes
alignment: for j in 0 to FLOWS-1 generate

  MORE_FLOWS : if (FLOWS > 1) generate

    filler : entity work.SWR_FILLER
      generic map (
        DATA_WIDTH     => FLOW_WIDTH,
        BYTES_TO_ALIGN => DATA_WIDTH/8
      )
      port map (
        CLK             => CLK,
        RESET           => RESET,

        -- Write interface
        NONALIGNED_DATA => RX_DATA((FLOW_WIDTH*j)+FLOW_WIDTH-1 downto FLOW_WIDTH*j),
        NONALIGNED_END  => rx_eof(j),
        SRC_RDY_N       => RX_SRC_RDY_N(j),
        DST_RDY_N       => RX_DST_RDY_N(j),

        -- Read interface
        WRITE           => write(j),
        ALIGNED_DATA    => data_in((FLOW_WIDTH*j)+FLOW_WIDTH-1 downto FLOW_WIDTH*j),
        BUFFER_FULL     => rxbuf_full(j),
        ALIGNED_END     => data_end(j)
      );

  end generate;

  -- release length
  rellen(j*RELLEN_W+RELLEN_W-1 downto j*RELLEN_W)
    <= RX_RELLEN(j*16+RELLEN_W+DATA_BYTES-1 downto j*16+DATA_BYTES);


  buf_wr_transaction(j) <= write(j) and not rxbuf_full(j);

  -- counters and counter registers
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        cnt_counter(j) <= conv_std_logic_vector(FLOW_BYTES, cnt_counter(j)'length);
      else
        if (buf_wr_transaction(j) = '1') then
          cnt_counter(j) <= cnt_counter(j) + FLOW_BYTES;
          if (data_end(j) = '1') then
            cnt_counter(j) <= conv_std_logic_vector(FLOW_BYTES, cnt_counter(j)'length);
          end if;
        end if;
      end if;
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        newlen(j) <= (others => '0');
      else
--         if (data_end(j) = '1') then
          newlen(j) <= cnt_counter(j);
--         end if;
      end if;
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        newlen_dv(j) <= '0';
      else
        newlen_dv(j) <= data_end(j) and buf_wr_transaction(j);
      end if;
    end if;
  end process;

  sh_reg_newlen_dv: entity work.SH_REG
    generic map(
      NUM_BITS => FLOWS
    )
    port map(
      CLK  => CLK,
      DIN  => newlen_dv(j),
      CE   => '1',
      DOUT => RX_NEWLEN_DV(j)
    );

  sh_reg_newlen: entity work.SH_REG_BUS
    generic map(
      NUM_BITS   => FLOWS,
      DATA_WIDTH => newlen(j)'length
    )
    port map(
      CLK  => CLK,
      DIN  => newlen(j),
      CE   => '1',
      DOUT => RX_NEWLEN((j*16)+15 downto j*16)
    );

end generate;

ONE_FLOW : if (FLOWS = 1) generate
  RD_ARDY         <= RD_DST_RDY and RD_REQ;
  data_in         <= RX_DATA;
  write(0)        <= not RX_SRC_RDY_N(0);
  data_end(0)     <= rx_eof(0);
  RX_DST_RDY_N(0) <= rxbuf_full(0);
end generate;

MORE_FLOWS : if (FLOWS > 1) generate
  RD_ARDY <= RD_DST_RDY and RD_REQ;
end generate;

-- ----------------------------------------------------------------------------
-- interface mapping
RD_SRC_RDY    <= rxbuf_valid;

end architecture;
-- ----------------------------------------------------------------------------
