--
-- SW TX buffer - top entity of sw_txbuf
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
entity SW_TXBUF_TOP is
  generic(
    DATA_WIDTH  : integer := 64;
    -- should be a power of 2
    BLOCK_SIZE  : integer := 512;
    -- Evailable data size for one flow (interface) (number of words DATA_WIDTH wide)
    FLOWS       : integer := 4;
    -- Total size (bytes) for one flow (interface)
    TOTAL_FLOW_SIZE  : integer := 16384;
    -- length of one size (head or data) in used protocol (16 bits for FrameLink)
    SIZE_LENGTH : integer := 16;
    -- can turn on/off usage of component that inserts register to output flows (to reduce critical path)
    USE_FL_PIPE : boolean := false
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
    TX_NEWLEN_RDY : out std_logic_vector(FLOWS-1 downto 0);  -- always set to '1'
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
architecture behavioral of SW_TXBUF_TOP is

  constant FLOW_WIDTH      : integer := DATA_WIDTH / FLOWS;
  constant FLOW_DREM_WIDTH : integer := log2(DATA_WIDTH / FLOWS / 8);
  constant NEWLEN_W        : integer := log2(BLOCK_SIZE+1);
  constant DATA_BYTES      : integer := log2(DATA_WIDTH/8);
  constant FLOW_BYTES      : integer := FLOW_WIDTH/8;
  constant FL_BYTES_W      : integer := log2(FLOW_BYTES);
  constant FLOW_LSB        : integer := log2(TOTAL_FLOW_SIZE); -- where flow (interface) address starts

  subtype MEM_RANGE is natural range log2(BLOCK_SIZE)+DATA_BYTES-1 downto DATA_BYTES;
  subtype BLK_RANGE is natural range abs(log2(FLOWS)-1)+FLOW_LSB downto FLOW_LSB;

  type t_cnt   is array(FLOWS-1 downto 0) of std_logic_vector(15 downto 0);
  type t_state is array(FLOWS-1 downto 0) of std_logic_vector(3 downto 0);
  type t_drem  is array(FLOWS-1 downto 0) of std_logic_vector(abs(FL_BYTES_W-1) downto 0);

  signal txbuf_full    : std_logic_vector(FLOWS-1 downto 0);
  signal txbuf_out     : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal txbuf_valid   : std_logic_vector(FLOWS-1 downto 0);

  signal write_req     : std_logic;
  signal read_req      : std_logic_vector(FLOWS-1 downto 0);

  signal newlen        : std_logic_vector((NEWLEN_W*FLOWS)-1 downto 0);
  signal cnt_counter   : t_cnt;

--  signal sof_n         : std_logic_vector(FLOWS-1 downto 0);
--  signal sop_n         : std_logic_vector(FLOWS-1 downto 0);
--  signal eof_n         : std_logic_vector(FLOWS-1 downto 0);
--  signal eop_n         : std_logic_vector(FLOWS-1 downto 0);
--  signal src_rdy_n     : std_logic_vector(FLOWS-1 downto 0);
--  signal dst_rdy_n     : std_logic_vector(FLOWS-1 downto 0);
--  signal drem          : t_drem;
--  signal data_out      : std_logic_vector(DATA_WIDTH-1 downto 0);

  signal parser_sending_word      : std_logic_vector(FLOWS-1 downto 0);
  signal parser_sending_last_word : std_logic_vector(FLOWS-1 downto 0);
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

    DATA_IN    => WR_DATA,
    WRITE      => write_req,
    BLOCK_ADDR => WR_ADDR(BLK_RANGE),
    WR_ADDR    => WR_ADDR(MEM_RANGE),
    NEW_LEN    => newlen,
    NEW_LEN_DV => TX_NEWLEN_DV,

    DATA_OUT   => txbuf_out,
    DATA_VLD   => txbuf_valid,
    READ       => read_req,
 
    EMPTY      => open,
    FULL       => txbuf_full,
    STATUS     => open
  );

-- write request
process(WR_ADDR, WR_REQ)
begin
  if (WR_ADDR(31 downto log2(FLOWS)+FLOW_LSB) = 0) then
    write_req <= WR_REQ;
  else
    write_req <= '0';
  end if;
end process;

-- ready signal to IB
ONE_FLOW : if (FLOWS = 1) generate
  WR_RDY <= not txbuf_full(0);
end generate;

MORE_FLOWS : if (FLOWS > 1) generate
  WR_RDY <= not txbuf_full(conv_integer(WR_ADDR(BLK_RANGE)));
end generate;


gen_parser : for j in 0 to FLOWS-1 generate

   PARSER_I : entity work.TXBUF_PARSER
      generic map (
         DATA_WIDTH        => FLOW_WIDTH
      )
      port map (
         CLK               => CLK,
         RESET             => RESET,
   
         -- MEM2NFIFO interface
         FIFO_DATA_OUT     => txbuf_out((j+1)*FLOW_WIDTH - 1 downto j*FLOW_WIDTH),
         FIFO_DATA_VLD     => txbuf_valid(j),
         FIFO_RD           => read_req(j),

         -- Control interface -- TODO
         SENDING_WORD      => parser_sending_word(j),
         SENDING_LAST_WORD => parser_sending_last_word(j),

         -- Output framelink interface
         FL_DATA           => TX_DATA((j+1)*FLOW_WIDTH - 1 downto j*FLOW_WIDTH),
         FL_SOF_N          => TX_SOF_N(j),
         FL_SOP_N          => TX_SOP_N(j),
         FL_EOP_N          => TX_EOP_N(j),
         FL_EOF_N          => TX_EOF_N(j),
         FL_REM            => TX_REM((j+1)*FLOW_DREM_WIDTH - 1 downto j*FLOW_DREM_WIDTH),
         FL_SRC_RDY_N      => TX_SRC_RDY_N(j),
         FL_DST_RDY_N      => TX_DST_RDY_N(j)
      );


-- 
--   USE_PIPE : if (USE_FL_PIPE) generate
--     fl_pipe : entity work.FL_PIPE
--       generic map(
--         DATA_WIDTH   => FLOW_WIDTH
--       )
--       port map(
--         -- Common interface 
--         CLK          => CLK,
--         RESET        => RESET,
--         
--         -- Input interface
--         RX_SOF_N     => sof_n(j),
--         RX_SOP_N     => sop_n(j),
--         RX_EOP_N     => eop_n(j),
--         RX_EOF_N     => eof_n(j),
--         RX_SRC_RDY_N => src_rdy_n(j),
--         RX_DST_RDY_N => dst_rdy_n(j),
--         RX_DATA      => data_out((j*FLOW_WIDTH)+FLOW_WIDTH-1 downto j*FLOW_WIDTH),
--         RX_REM       => drem(j),
--    
--         -- Output interface
--         TX_SOF_N     => TX_SOF_N(j),
--         TX_EOP_N     => TX_EOP_N(j),
--         TX_SOP_N     => TX_SOP_N(j),
--         TX_EOF_N     => TX_EOF_N(j),
--         TX_SRC_RDY_N => TX_SRC_RDY_N(j),
--         TX_DST_RDY_N => TX_DST_RDY_N(j),
--         TX_DATA      => TX_DATA((j*FLOW_WIDTH)+FLOW_WIDTH-1 downto j*FLOW_WIDTH),
--         TX_REM       => TX_REM(abs((FL_BYTES_W*j)+FL_BYTES_W-1) downto FL_BYTES_W*j)
--       );
--   end generate;

  -- release length
  newlen(j*NEWLEN_W+NEWLEN_W-1 downto j*NEWLEN_W)
    <= TX_NEWLEN(j*16+NEWLEN_W+DATA_BYTES-1 downto j*16+DATA_BYTES);

  -- counters and counter registers
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        cnt_counter(j) <= conv_std_logic_vector(FLOW_BYTES, cnt_counter(j)'length);
      else
        if (parser_sending_word(j) = '1') then
          cnt_counter(j) <= cnt_counter(j) + FLOW_BYTES;
          if (parser_sending_last_word(j) = '1') then
            cnt_counter(j) <=
               conv_std_logic_vector(FLOW_BYTES, cnt_counter(j)'length);
          end if;
        end if;
      end if;
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        TX_RELLEN((j*16)+15 downto j*16) <= (others => '0');
      else
        if (parser_sending_last_word(j) = '1') then
          TX_RELLEN((j*16)+15 downto j*16) <= cnt_counter(j);
        end if;
      end if;
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      TX_RELLEN_DV(j) <= parser_sending_last_word(j);
    end if;
  end process;

end generate;

-- ----------------------------------------------------------------------------
-- interface mapping

TX_NEWLEN_RDY <= (others => '1');

-- DONT_USE_PIPE : if (not USE_FL_PIPE) generate
--   TX_SOF_N     <= sof_n;
--   TX_SOP_N     <= sop_n;
--   TX_EOP_N     <= eop_n;
--   TX_EOF_N     <= eof_n;
--   TX_SRC_RDY_N <= src_rdy_n;
--   dst_rdy_n    <= TX_DST_RDY_N;
--   TX_DATA      <= data_out;

end architecture;
-- ----------------------------------------------------------------------------
