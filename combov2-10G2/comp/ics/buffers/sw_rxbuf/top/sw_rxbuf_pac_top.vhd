-- sw_rxbuf_pac_top.vhd - generic entity of sw_rxbuf for packet DMA
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
entity SW_RXBUF_PAC_TOP is
  generic(
    -- Internal Bus data width
    DATA_WIDTH      : integer := 64;
    -- Should be a power of 2
    -- Available data size for one interface (number of words DATA_WIDTH wide)
    BLOCK_SIZE      : integer := 512;
    -- Number of input interfaces
    FLOWS           : integer := 2;
    -- Total size (bytes) for one flow (interface)
    TOTAL_FLOW_SIZE : integer := 16384
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

    -- DMA controller interface
    RX_NEWLEN     : out std_logic_vector((FLOWS*16)-1 downto 0);
    RX_NEWLEN_DV  : out std_logic_vector(FLOWS-1 downto 0);
    RX_NEWLEN_RDY : in  std_logic_vector(FLOWS-1 downto 0);
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
architecture behavioral of SW_RXBUF_PAC_TOP is

  -- length of shortest packet in Bytes
  constant SHORTEST_PAC_LEN : integer := 64;
  -- depth of newlen shift fifo (to store all shortest packets)
  constant FIFO_DEPTH : integer := (BLOCK_SIZE*DATA_WIDTH)/(SHORTEST_PAC_LEN*8);
  -- data width (bits) of one input flow
  constant FLOW_WIDTH : integer := DATA_WIDTH / FLOWS;
  -- width of single release length signal
  constant RELLEN_W   : integer := log2(BLOCK_SIZE+1);
  -- number of bits to truncate for converting from bits to Bytes
  constant DATA_BYTES : integer := log2(DATA_WIDTH/8);
  -- data width (Bytes) of one input flow
  constant FLOW_BYTES : integer := FLOW_WIDTH/8;
  -- where flow (interface) address starts
  constant FLOW_LSB   : integer := log2(TOTAL_FLOW_SIZE);

  -- width of REM signal of one flow
  function REM_WIDTH
    return integer is
  begin
    if (FLOW_BYTES = 1) then return 1;
    else return log2(FLOW_BYTES);
    end if;
  end function;

  subtype MEM_RANGE   is natural range log2(BLOCK_SIZE)+DATA_BYTES-1 downto DATA_BYTES;
  subtype BLK_RANGE   is natural range abs(log2(FLOWS)-1)+FLOW_LSB downto FLOW_LSB;
  subtype BYTES_RANGE is natural range DATA_BYTES-1 downto 0;
  subtype ITEMS_RANGE is natural range RELLEN_W+DATA_BYTES-1 downto DATA_BYTES;

  type t_cnt    is array(FLOWS-1 downto 0) of std_logic_vector(15 downto 0);
  type t_rem    is array(FLOWS-1 downto 0) of std_logic_vector(REM_WIDTH-1 downto 0);
  type t_rellen is array(FLOWS-1 downto 0) of std_logic_vector(RELLEN_W-1 downto 0);

  signal data_in           : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal write             : std_logic_vector(FLOWS-1 downto 0);
  signal read_req          : std_logic;
  signal rxbuf_full        : std_logic_vector(FLOWS-1 downto 0);
  signal rxbuf_valid       : std_logic;
  signal rellen_bytes      : t_cnt;
  signal rellen_items      : t_rellen;
  signal rellen            : std_logic_vector((RELLEN_W*FLOWS)-1 downto 0);
  signal rellen_dv         : std_logic_vector(FLOWS-1 downto 0);
  signal cnt_counter       : t_cnt;
  signal drem              : t_rem;
  signal rx_eof            : std_logic_vector(FLOWS-1 downto 0);
  signal dst_rdy_n         : std_logic_vector(FLOWS-1 downto 0);
  signal newlen_reg_dv     : std_logic_vector(FLOWS-1 downto 0);
  signal newlen_reg        : t_cnt;
  signal newlen_fifo_dv    : std_logic_vector(FLOWS-1 downto 0);
  signal newlen_fifo       : t_cnt;
  signal newlen_fifo_empty : std_logic_vector(FLOWS-1 downto 0);

-- ----------------------------------------------------------------------------
begin

assert (DATA_WIDTH mod FLOWS = 0)
report "DATA_WIDTH / FLOWS is not an integer."
severity ERROR;

assert (FLOW_BYTES >= 1)
report "Width of one flow must be >= 1 Byte."
severity ERROR;

-- Check if total size is the same or more than block_size
assert (BLOCK_SIZE * (DATA_WIDTH/8) <= TOTAL_FLOW_SIZE)
report "TOTAL_FLOW_SIZE must be >= than BLOCK_SIZE * (DATA_WIDTH/8)."
severity ERROR;

nfifo2mem_i : entity work.NFIFO2MEM
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
    REL_LEN_DV => rellen_dv,
    READ       => RD_REQ,
    PIPE_EN    => RD_DST_RDY,
 
    EMPTY      => open,
    FULL       => rxbuf_full,
    STATUS     => open
  );

-- rellen_dv register
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    rellen_dv <= RX_RELLEN_DV;
  end if;
end process;

-- EOF for filler
rx_eof <= (not RX_EOF_N) and (not RX_SRC_RDY_N);

-- align data to width of Internal Bus
alignment: for j in 0 to FLOWS-1 generate

  MORE_FLOWS : if (FLOWS > 1) generate

    swr_filler_i : entity work.SWR_FILLER
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
        DST_RDY_N       => dst_rdy_n(j),

        -- Read interface
        WRITE           => write(j),
        ALIGNED_DATA    => data_in((FLOW_WIDTH*j)+FLOW_WIDTH-1 downto FLOW_WIDTH*j),
        BUFFER_FULL     => rxbuf_full(j),
        ALIGNED_END     => open
      );

  end generate;

  -- REM signal
  GEN_REM_1B : if (FLOW_BYTES = 1) generate
    drem(j) <= (others => '0');
  end generate;

  GEN_REM_XB : if (FLOW_BYTES > 1) generate
    drem(j) <= RX_REM((j+1)*REM_WIDTH-1 downto j*REM_WIDTH);
  end generate;

  -- release length
  rellen_bytes(j) <= RX_RELLEN((j+1)*16-1 downto j*16);
  rellen((j+1)*RELLEN_W-1 downto j*RELLEN_W) <= rellen_items(j);

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (rellen_bytes(j)(BYTES_RANGE) = conv_std_logic_vector(0, DATA_BYTES)) then
        rellen_items(j) <= rellen_bytes(j)(ITEMS_RANGE);
      else
        rellen_items(j) <= rellen_bytes(j)(ITEMS_RANGE) + 1;
      end if;
    end if;
  end process;

  -- counters and counter registers
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RX_SOF_N(j) = '0') then
        cnt_counter(j) <= conv_std_logic_vector(FLOW_BYTES, cnt_counter(j)'length);
      else
        if ((RX_SRC_RDY_N(j) = '0') and (dst_rdy_n(j) = '0')) then
          cnt_counter(j) <= cnt_counter(j) + FLOW_BYTES;
        end if;
      end if;
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      newlen_reg(j) <= cnt_counter(j) + 1 + drem(j);
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      newlen_reg_dv(j) <= (not RX_EOF_N(j)) and (not RX_SRC_RDY_N(j)) and (not dst_rdy_n(j));
    end if;
  end process;

  sh_reg_i: entity work.SH_REG
    generic map(
      NUM_BITS => 2*FLOWS-1
    )
    port map(
      CLK  => CLK,
      DIN  => newlen_reg_dv(j),
      CE   => '1',
      DOUT => newlen_fifo_dv(j)
    );

  sh_reg_bus_i: entity work.SH_REG_BUS
    generic map(
      NUM_BITS   => 2*FLOWS-1,
      DATA_WIDTH => 16
    )
    port map(
      CLK  => CLK,
      DIN  => newlen_reg(j),
      CE   => '1',
      DOUT => newlen_fifo(j)
    );

    sh_fifo_i: entity work.SH_FIFO
      generic map(
        FIFO_WIDTH => 16,
        FIFO_DEPTH => FIFO_DEPTH
      )
      port map(
        CLK    => CLK,
        RESET  => RESET,
        -- write interface
        DIN    => newlen_fifo(j),
        WE     => newlen_fifo_dv(j),
        FULL   => open,
        -- read interface
        DOUT   => RX_NEWLEN((j*16)+15 downto j*16),
        RE     => RX_NEWLEN_RDY(j),
        EMPTY  => newlen_fifo_empty(j),
        STATUS => open
      );

end generate;

ONE_FLOW : if (FLOWS = 1) generate
  data_in      <= RX_DATA;
  write(0)     <= not RX_SRC_RDY_N(0);
  dst_rdy_n(0) <= rxbuf_full(0);
end generate;

-- ----------------------------------------------------------------------------
-- interface mapping
RD_SRC_RDY   <= rxbuf_valid;
RD_ARDY      <= RD_DST_RDY and RD_REQ;
RX_DST_RDY_N <= dst_rdy_n;
RX_NEWLEN_DV <= not newlen_fifo_empty;

end architecture;
-- ----------------------------------------------------------------------------
