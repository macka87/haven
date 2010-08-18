-- sw_txbuf_pac_top.vhd - generic entity of sw_txbuf for packet DMA
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
entity SW_TXBUF_PAC_TOP is
  generic(
    DATA_WIDTH  : integer := 64;
    -- should be a power of 2
    BLOCK_SIZE  : integer := 512;
    -- Evailable data size for one flow (interface) (number of words DATA_WIDTH wide)
    FLOWS       : integer := 4;
    -- Total size (bytes) for one flow (interface)
    TOTAL_FLOW_SIZE : integer := 16384
  );
  port(
    CLK           : in  std_logic;
    RESET         : in  std_logic;

    -- Write interface (InternalBus)
    WR_ADDR       : in  std_logic_vector(31 downto 0);
    WR_BE         : in  std_logic_vector(7 downto 0);
    WR_REQ        : in  std_logic;
    WR_RDY        : out std_logic;
    WR_DATA       : in  std_logic_vector(DATA_WIDTH-1 downto 0);

    TX_NEWLEN     : in  std_logic_vector((FLOWS*16)-1 downto 0);
    TX_NEWLEN_DV  : in  std_logic_vector(FLOWS-1 downto 0);
    TX_NEWLEN_RDY : out std_logic_vector(FLOWS-1 downto 0);
    TX_RELLEN     : out std_logic_vector((FLOWS*16)-1 downto 0);
    TX_RELLEN_DV  : out std_logic_vector(FLOWS-1 downto 0);

    -- Read interface (FrameLinks)
    TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
    TX_SOF_N      : out std_logic_vector(FLOWS-1 downto 0);
    TX_SOP_N      : out std_logic_vector(FLOWS-1 downto 0);
    TX_EOP_N      : out std_logic_vector(FLOWS-1 downto 0);
    TX_EOF_N      : out std_logic_vector(FLOWS-1 downto 0);
    TX_REM        : out std_logic_vector(abs((log2((DATA_WIDTH/FLOWS)/8)*FLOWS)-1) downto 0);
    TX_SRC_RDY_N  : out std_logic_vector(FLOWS-1 downto 0);
    TX_DST_RDY_N  : in  std_logic_vector(FLOWS-1 downto 0)
  );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of SW_TXBUF_PAC_TOP is

  -- length of shortest packet in Bytes
  constant SHORTEST_PAC_LEN : integer := 64;
  -- depth of newlen shift fifo (to store all shortest packets)
  constant FIFO_DEPTH  : integer := (BLOCK_SIZE*DATA_WIDTH)/(SHORTEST_PAC_LEN*8);
  -- data width (bits) of one input flow
  constant FLOW_WIDTH  : integer := DATA_WIDTH / FLOWS;
  -- width of single new length signal
  constant NEWLEN_W    : integer := log2(BLOCK_SIZE+1);
  -- number of bits to truncate for converting from bits to Bytes
  constant DATA_BYTES  : integer := log2(DATA_WIDTH/8);
  -- data width (Bytes) of one input flow
  constant FLOW_BYTES  : integer := FLOW_WIDTH/8;
  -- where flow (interface) address starts
  constant FLOW_LSB    : integer := log2(TOTAL_FLOW_SIZE);

  subtype MEM_RANGE   is natural range log2(BLOCK_SIZE)+DATA_BYTES-1 downto DATA_BYTES;
  subtype BLK_RANGE   is natural range abs(log2(FLOWS)-1)+FLOW_LSB downto FLOW_LSB;
  subtype BYTES_RANGE is natural range DATA_BYTES-1 downto 0;

  subtype ITEMS_RANGE is natural range NEWLEN_W+DATA_BYTES-1 downto DATA_BYTES;

  type t_data_reg is array(FLOWS-1 downto 0) of std_logic_vector(DATA_WIDTH-1 downto 0);

  type t_cnt    is array(FLOWS-1 downto 0) of std_logic_vector(15 downto 0);
  type t_newlen is array(FLOWS-1 downto 0) of std_logic_vector(NEWLEN_W-1 downto 0);

  signal reg_wr_data       : t_data_reg;
  signal write_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal write_req         : std_logic;
  signal write_addr        : std_logic_vector(31 downto 0);
  signal write_rdy         : std_logic;

  signal txbuf_full        : std_logic_vector(FLOWS-1 downto 0);
  signal txbuf_out         : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal txbuf_valid       : std_logic_vector(FLOWS-1 downto 0);

  signal read_req          : std_logic_vector(FLOWS-1 downto 0);

  signal newlen_bytes      : t_cnt;
  signal newlen_items      : t_newlen;
  signal newlen            : std_logic_vector((NEWLEN_W*FLOWS)-1 downto 0);
  signal newlen_dv         : std_logic_vector(FLOWS-1 downto 0);
  signal newlen_fifo       : t_cnt;
  signal newlen_fifo_full  : std_logic_vector(FLOWS-1 downto 0);
  signal newlen_fifo_empty : std_logic_vector(FLOWS-1 downto 0);
  signal newlen_fifo_vld   : std_logic_vector(FLOWS-1 downto 0);
  signal newlen_fifo_rd    : std_logic_vector(FLOWS-1 downto 0);

-- ----------------------------------------------------------------------------
begin

assert (DATA_WIDTH mod FLOWS = 0)
report "DATA_WIDTH / FLOWS is not an integer."
severity ERROR;

tx_buffer : entity work.MEM2NFIFO
  generic map(
    DATA_WIDTH => DATA_WIDTH,
    FLOWS      => FLOWS,
    BLOCK_SIZE => BLOCK_SIZE,
    LUT_MEMORY => false,
    GLOB_STATE => true
  ) 
  port map(
    CLK        => CLK,
    RESET      => RESET,

    DATA_IN    => write_data,
    WRITE      => write_req,
    BLOCK_ADDR => write_addr(BLK_RANGE),
    WR_ADDR    => write_addr(MEM_RANGE),
    NEW_LEN    => newlen,
    NEW_LEN_DV => newlen_dv,

    DATA_OUT   => txbuf_out,
    DATA_VLD   => txbuf_valid,
    READ       => read_req,
 
    EMPTY      => open,
    FULL       => txbuf_full,
    STATUS     => open
  );

-- newlen_dv register
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    newlen_dv <= TX_NEWLEN_DV;
  end if;
end process;

-- write address and write request register
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    write_addr <= WR_ADDR;
    write_req  <= WR_REQ;
  end if;
end process;

-- diffs between one and more flows (wires or multiplexers)
ONE_FLOW : if (FLOWS = 1) generate
  -- write data and write ready
  write_data <= reg_wr_data(0);
  write_rdy  <= not txbuf_full(0);
end generate;

MORE_FLOWS : if (FLOWS > 1) generate
  -- write data and write ready
  write_data <= reg_wr_data(conv_integer(write_addr(BLK_RANGE)));
  write_rdy  <= not txbuf_full(conv_integer(WR_ADDR(BLK_RANGE)));
end generate;

-- valid signal of newlen fifo
newlen_fifo_vld <= not newlen_fifo_empty;

gen_output : for j in 0 to FLOWS-1 generate

  -- BE handling
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (WR_ADDR(BLK_RANGE) = j) then
        if (WR_REQ = '1') then
          for i in 0 to 7 loop
            if (WR_BE(i) = '1') then
              reg_wr_data(j)((i+1)*8-1 downto i*8) <= WR_DATA((i+1)*8-1 downto i*8);
            end if;
          end loop;
        end if;
      end if;
    end if;
  end process;

  -- new length
  newlen_bytes(j) <= TX_NEWLEN((j+1)*16-1 downto j*16);
  newlen((j+1)*NEWLEN_W-1 downto j*NEWLEN_W) <= newlen_items(j);

  -- aligning to IB (item) width
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (newlen_bytes(j)(BYTES_RANGE) = conv_std_logic_vector(0, DATA_BYTES)) then
        newlen_items(j) <= newlen_bytes(j)(ITEMS_RANGE);
      else
        newlen_items(j) <= newlen_bytes(j)(ITEMS_RANGE) + 1;
      end if;
    end if;
  end process;

  parser_pac_i: entity work.TXBUF_PARSER_PAC
    generic map(
      DATA_WIDTH => FLOW_WIDTH,
      FLOWS      => FLOWS
    )
    port map(
      CLK          => CLK,
      RESET        => RESET,

      -- Input mem2nfifo interface
      TXBUF_DATA   => txbuf_out((j+1)*FLOW_WIDTH-1 downto j*FLOW_WIDTH),
      TXBUF_VALID  => txbuf_valid(j),
      TXBUF_READ   => read_req(j),

      -- Input sh_fifo interface
      NEWLEN_FIFO  => newlen_fifo(j),
      NEWLEN_VLD   => newlen_fifo_vld(j),
      NEWLEN_READ  => newlen_fifo_rd(j),

      -- Output FrameLink interface
      FL_DATA      => TX_DATA((j+1)*FLOW_WIDTH-1 downto j*FLOW_WIDTH),
      FL_SOF_N     => TX_SOF_N(j),
      FL_SOP_N     => TX_SOP_N(j),
      FL_EOP_N     => TX_EOP_N(j),
      FL_EOF_N     => TX_EOF_N(j),
      FL_REM       => TX_REM((j+1)*log2(FLOW_BYTES)-1 downto j*log2(FLOW_BYTES)),
      FL_SRC_RDY_N => TX_SRC_RDY_N(j),
      FL_DST_RDY_N => TX_DST_RDY_N(j)
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
      DIN    => TX_NEWLEN((j*16)+15 downto j*16),
      WE     => TX_NEWLEN_DV(j),
      FULL   => newlen_fifo_full(j),
      -- read interface
      DOUT   => newlen_fifo(j),
      RE     => newlen_fifo_rd(j),
      EMPTY  => newlen_fifo_empty(j),
      STATUS => open
    );

    TX_RELLEN((j*16)+15 downto j*16) <= newlen_fifo(j);
    TX_RELLEN_DV(j) <= newlen_fifo_rd(j);

end generate;

-- ----------------------------------------------------------------------------
-- interface mapping
WR_RDY        <= write_rdy;
TX_NEWLEN_RDY <= not newlen_fifo_full;

end architecture;
-- ----------------------------------------------------------------------------
