-- sw_rxbuf_gen_ver.vhd - generic envelope above SW_RXBUF_GEN for easy verification
-- -- it contains only connection between SW_RXBUF_GEN and FrameLink Multiplexer
-- Copyright (C) 2010 CESNET
-- Author(s): Karel Koranda <xkoran01@stud.fit.vutbr.cz>
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
entity SW_RXBUF_GEN_VER is
  generic(
    DATA_WIDTH      : integer := 64;
    BLOCK_SIZE      : integer := 512;
    FLOWS           : integer := 4
  );
  port(
    CLK             : in  std_logic;
    RESET           : in  std_logic;

    -- Write interface (FrameLink)
    RX_SOF_N        : in  std_logic_vector(FLOWS-1 downto 0);
    RX_SOP_N        : in  std_logic_vector(FLOWS-1 downto 0);
    RX_EOP_N        : in  std_logic_vector(FLOWS-1 downto 0);
    RX_EOF_N        : in  std_logic_vector(FLOWS-1 downto 0);
    RX_SRC_RDY_N    : in  std_logic_vector(FLOWS-1 downto 0);
    RX_DST_RDY_N    : out std_logic_vector(FLOWS-1 downto 0);
    RX_DATA         : in  std_logic_vector(DATA_WIDTH*FLOWS-1 downto 0);
    RX_DREM         : in  std_logic_vector(FLOWS*log2(DATA_WIDTH/8)-1 downto 0);
    
    -- RELLEN and NEWLEN interface
    BUF_NEWLEN      : out std_logic_vector(15 downto 0);
    BUF_NEWLEN_DV   : out std_logic;
    BUF_NEWLEN_IFC  : out std_logic_vector(abs(log2(FLOWS)-1) downto 0);
    BUF_RELLEN      : in  std_logic_vector(15 downto 0);
    BUF_RELLEN_DV   : in  std_logic;
    BUF_RELLEN_IFC  : in  std_logic_vector(abs(log2(FLOWS)-1) downto 0);

    -- Read interface (InternalBus)
    RD_ADDR         : in  std_logic_vector(31 downto 0);
    RD_BE           : in  std_logic_vector((DATA_WIDTH/8)-1 downto 0);
    RD_REQ          : in  std_logic;
    RD_ARDY         : out std_logic;

    RD_DATA         : out std_logic_vector(DATA_WIDTH-1 downto 0);
    RD_SRC_RDY      : out std_logic;
    RD_DST_RDY      : in  std_logic
  );
end entity;

-- ----------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------
architecture behavioral of SW_RXBUF_GEN_VER is

  constant RX_DATA_WIDTH  : integer := DATA_WIDTH/FLOWS;

  signal tx2rx_addr       : std_logic_vector(abs(log2(FLOWS)-1) downto 0);
  signal tx2rx_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal tx2rx_sop_n      : std_logic;
  signal tx2rx_sof_n      : std_logic;
  signal tx2rx_eop_n      : std_logic;
  signal tx2rx_eof_n      : std_logic;
  signal tx2rx_rem        : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
  signal tx2rx_src_rdy_n  : std_logic;
  signal tx2rx_dst_rdy_n  : std_logic_vector(FLOWS-1 downto 0);

-- ----------------------------------------------------------------------------
begin

GEN_MORE_FLOWS: if FLOWS > 1 generate
-- --------------------------------------------------
-- -- FL_MULTIPLEXER mapping
-- --------------------------------------------------

fl_multiplexer_i : entity work.FL_MULTIPLEXER
  generic map (
    DATA_WIDTH    => DATA_WIDTH,
    CHANNELS      => FLOWS
  ) 
  port map (
    CLK           => CLK,
    RESET         => RESET,

    RX_SOF_N      => RX_SOF_N,
    RX_SOP_N      => RX_SOP_N,
    RX_EOP_N      => RX_EOP_N,
    RX_EOF_N      => RX_EOF_N,
    RX_SRC_RDY_N  => RX_SRC_RDY_N,
    RX_DST_RDY_N  => RX_DST_RDY_N,
    RX_DATA       => RX_DATA,
    RX_DREM       => RX_DREM,
    
    TX_SOF_N      => tx2rx_sof_n,
    TX_EOP_N      => tx2rx_eop_n,
    TX_SOP_N      => tx2rx_sop_n,
    TX_EOF_N      => tx2rx_eof_n,
    TX_SRC_RDY_N  => tx2rx_src_rdy_n,
    TX_DATA       => tx2rx_data,
    TX_DREM       => tx2rx_rem,
    TX_DST_RDY_N  => tx2rx_dst_rdy_n,
    
    TX_CHANNEL    => tx2rx_addr
  );

-- ---------------------------------------------------
-- -- SW_RXBUF_GEN mapping
-- ---------------------------------------------------

sw_rxbuf_gen_i : entity work.SW_RXBUF_GEN
  generic map (
    DATA_WIDTH      => DATA_WIDTH,
    BLOCK_SIZE      => BLOCK_SIZE,
    FLOWS           => FLOWS 
  )
  port map (
    CLK             => CLK,
    RESET           => RESET,
    INIT            => (others => '0'),
    
    RX_ADDR         => tx2rx_addr,
    
    RX_DATA         => tx2rx_data,
    RX_SOP_N        => tx2rx_sop_n,
    RX_SOF_N        => tx2rx_sof_n,
    RX_EOF_N        => tx2rx_eof_n,
    RX_EOP_N        => tx2rx_eop_n,
    RX_REM          => tx2rx_rem,
    RX_SRC_RDY_N    => tx2rx_src_rdy_n,
    RX_DST_RDY_N    => tx2rx_dst_rdy_n,
    
    BUF_NEWLEN      => BUF_NEWLEN,
    BUF_NEWLEN_DV   => BUF_NEWLEN_DV,
    BUF_NEWLEN_IFC  => BUF_NEWLEN_IFC,
    BUF_RELLEN      => BUF_RELLEN,
    BUF_RELLEN_DV   => BUF_RELLEN_DV,
    BUF_RELLEN_IFC  => BUF_RELLEN_IFC,
    
    RD_ADDR         => RD_ADDR,
    RD_BE           => RD_BE,
    RD_REQ          => RD_REQ,
    RD_ARDY         => RD_ARDY,
    
    RD_DATA         => RD_DATA,
    RD_SRC_RDY      => RD_SRC_RDY,
    RD_DST_RDY      => RD_DST_RDY
  );

-- --------------------------------------------------
-- -- 
-- --------------------------------------------------
end generate;

GEN_ONE_FLOW: if FLOWS = 1 generate

sw_rxbuf_gen_i : entity work.SW_RXBUF_GEN
  generic map (
    DATA_WIDTH	=> DATA_WIDTH,
    BLOCK_SIZE	=> BLOCK_SIZE,
    FLOWS	=> FLOWS
  )
  port map (
    CLK		=> CLK,
    RESET 	=> RESET,
    INIT	=> (others => '0'),

    RX_ADDR	=> (others => '0'),

    RX_DATA	=> RX_DATA,
    RX_SOP_N	=> RX_SOP_N(0),
    RX_SOF_N	=> RX_SOF_N(0),
    RX_EOF_N	=> RX_EOF_N(0),
    RX_EOP_N	=> RX_EOP_N(0),
    RX_REM	=> RX_DREM,
    RX_SRC_RDY_N => RX_SRC_RDY_N(0),
    RX_DST_RDY_N => RX_DST_RDY_N,
    
    BUF_NEWLEN	=> BUF_NEWLEN,
    BUF_NEWLEN_DV => BUF_NEWLEN_DV,
    BUF_NEWLEN_IFC => BUF_NEWLEN_IFC,
    BUF_RELLEN	=> BUF_RELLEN,
    BUF_RELLEN_DV => BUF_RELLEN_DV,
    BUF_RELLEN_IFC => BUF_RELLEN_IFC,

    RD_ADDR	=> RD_ADDR,
    RD_BE	=> RD_BE,
    RD_REQ	=> RD_REQ,
    RD_ARDY	=> RD_ARDY,

    RD_DATA	=> RD_DATA,
    RD_SRC_RDY	=> RD_SRC_RDY,
    RD_DST_RDY	=> RD_DST_RDY
  );

end generate;

end architecture;
-- ----------------------------------------------------------------------------
