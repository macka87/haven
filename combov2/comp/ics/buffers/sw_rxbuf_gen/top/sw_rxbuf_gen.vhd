-- sw_rxbuf_gen.vhd - generic entity of sw_rxbuf
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
entity SW_RXBUF_GEN is
  generic(
    DATA_WIDTH       : integer := 64;
    BLOCK_SIZE       : integer := 512;
    FLOWS            : integer := 1
  );
  port(
    CLK             : in  std_logic;
    RESET           : in  std_logic;
    INIT            : in  std_logic_vector(FLOWS-1 downto 0);
    
    STATUS          : out std_logic_vector(log2(BLOCK_SIZE+1)*FLOWS-1 downto 0);
    FULL            : out std_logic_vector(FLOWS-1 downto 0);
    EMPTY           : out std_logic_vector(FLOWS-1 downto 0);

    -- Write interface (FrameLink)
    RX_ADDR         : in std_logic_vector(abs(log2(FLOWS)-1) downto 0);
    
    RX_DATA         : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    RX_SOP_N        : in  std_logic;
    RX_EOP_N        : in  std_logic;
    RX_SOF_N        : in  std_logic;
    RX_EOF_N        : in  std_logic;
    RX_REM          : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
    RX_SRC_RDY_N    : in  std_logic;
    RX_DST_RDY_N    : out std_logic_vector(FLOWS-1 downto 0);

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
architecture behavioral of SW_RXBUF_GEN is

  constant FLOW_WIDTH     : integer := DATA_WIDTH / FLOWS;
  constant DATA_BYTES     : integer := log2(DATA_WIDTH/8);
  constant BLOCK_BYTES    : integer := log2(BLOCK_SIZE);
  constant BLK_ADDR_L     : integer := DATA_BYTES+BLOCK_BYTES+1;
  constant DEMUX_DATA     : integer := log2(BLOCK_SIZE+1);
  constant FLOW_BYTES     : integer := DATA_WIDTH/8;
  constant MUX_DATA_WIDTH : integer := 1;

  constant NEWLEN_WIDTH   : integer := 16-log2(DATA_WIDTH/8);

  constant RELLEN_W : integer := log2(BLOCK_SIZE+1);
  
  subtype MEM_RANGE is natural range log2(BLOCK_SIZE)+DATA_BYTES-1 downto DATA_BYTES;
  subtype BLK_RANGE is natural range abs(log2(FLOWS)-1)+BLK_ADDR_L downto BLK_ADDR_L;
  subtype REL_RANGE is natural range RELLEN_W+DATA_BYTES-1 downto DATA_BYTES;

  type t_newlen_cnt is array(FLOWS-1 downto 0) of std_logic_vector(NEWLEN_WIDTH-1 downto 0);

  signal data_in          : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal write_in         : std_logic;
  
  signal rellen_dv        : std_logic_vector(FLOWS-1 downto 0);
  signal rellen           : std_logic_vector(log2(BLOCK_SIZE+1)*FLOWS-1 downto 0);
  signal rellen_flow      : std_logic_vector(log2(BLOCK_SIZE+1)-1 downto 0);
  
  signal data_end         : std_logic;
  signal newlen_cnt_reset : std_logic_vector(FLOWS-1 downto 0);
  signal buffer_full      : std_logic_vector(0 downto 0);
  signal rx_eof           : std_logic;
  
  signal newlen_ifc_reg   : std_logic_vector(abs(log2(FLOWS)-1) downto 0);
  signal newlen_dv_reg    : std_logic;
  signal newlen_cnt_mux   : std_logic_vector(NEWLEN_WIDTH-1 downto 0);
  signal newlen_cnt_vect  : std_logic_vector((NEWLEN_WIDTH*FLOWS)-1 downto 0);
  signal newlen_cnt1      : t_newlen_cnt;
  signal newlen_reg       : std_logic_vector(NEWLEN_WIDTH-1 downto 0);
  
  signal newlen_ce        : std_logic;
  signal newlen_ce_mux    : std_logic_vector(FLOWS-1 downto 0);
  
  signal full_out         : std_logic_vector(FLOWS-1 downto 0);

  signal dst_rdy_n_filler : std_logic;
  
  signal rx_dst_rdy_n_reg : std_logic_vector(FLOWS-1 downto 0);

  signal zeros : std_logic_vector(15 downto 0);

-- ----------------------------------------------------------------------------
begin

assert (DATA_WIDTH mod FLOWS = 0)
report "DATA_WIDTH / FLOWS is not an integer."
severity ERROR;

-- --------------------------------------------------
-- -- MFIFO2MEM mapping
-- --------------------------------------------------

mfifo2mem_i : entity work.MFIFO2MEM
  generic map (
    DATA_WIDTH  => DATA_WIDTH,
    FLOWS       => FLOWS,
    BLOCK_SIZE  => BLOCK_SIZE,
    LUT_MEMORY  => false,
    OUTPUT_REG  => false
  ) 
  port map (
    CLK         => CLK,
    RESET       => RESET,
    INIT        => INIT,

    DATA_IN     => data_in,
    WR_BLK_ADDR => RX_ADDR,
    WRITE       => write_in,

    DATA_OUT    => RD_DATA,
    DATA_VLD    => RD_SRC_RDY,
    RD_BLK_ADDR => RD_ADDR(BLK_RANGE),
    RD_ADDR     => RD_ADDR(MEM_RANGE),
    REL_LEN     => rellen,
    REL_LEN_DV  => rellen_dv,
    READ        => RD_REQ,
    PIPE_EN     => RD_DST_RDY,

    EMPTY       => EMPTY,
    FULL        => full_out,
    STATUS      => STATUS
  );

-- --------------------------------------------------
-- -- writing
-- --------------------------------------------------

  rx_eof <= (not RX_EOF_N) and (not RX_SRC_RDY_N);

  data_in <= RX_DATA;
  data_end <= rx_eof;
  write_in <= not RX_SRC_RDY_N;

-- --------------------------------------------------
-- -- RELLEN SIGNALS
-- --------------------------------------------------

-- rellen cut - block bytes needed
rellen_flow <= BUF_RELLEN(REL_RANGE);

GEN_RELLEN_DEMUX_MORE_FLOWS: if FLOWS > 1 generate

   rellen_dec1fn : entity work.DEC1FN_ENABLE
      generic map (
         ITEMS   => FLOWS
      )
      port map (
         ADDR    => BUF_RELLEN_IFC,
         ENABLE  => BUF_RELLEN_DV,
         DO      => rellen_dv
      );

   rellen_demux : entity work.GEN_DEMUX
      generic map (
         DATA_WIDTH  => DEMUX_DATA,
         DEMUX_WIDTH => FLOWS
      )
      port map (
         DATA_IN     => rellen_flow,
         SEL         => BUF_RELLEN_IFC,
         DATA_OUT    => rellen
      );

end generate;

GEN_RELLEN_DEMUX_ONE_FLOW: if FLOWS = 1 generate

   rellen_dv(0) <= BUF_RELLEN_DV;
   rellen <= rellen_flow;

end generate;

-- ---------------------------------------------------
-- -- NEWLEN SIGNALS
-- ---------------------------------------------------

GEN_NEWLEN_DEMUX_MORE_FLOWS: if FLOWS > 1 generate

   newlen_ce_demux : entity work.DEC1FN_ENABLE
      generic map (
         ITEMS => FLOWS
      )
      port map (
         ADDR => RX_ADDR,
         ENABLE  => newlen_ce,
         DO  => newlen_ce_mux
      );

   data_end_demux : entity work.DEC1FN_ENABLE
      generic map (
         ITEMS => FLOWS
      )
      port map (
         ADDR => RX_ADDR,
         ENABLE  => data_end,
         DO  => newlen_cnt_reset
      );

end generate;

GEN_NEWLEN_DEMUX_ONE_FLOW: if FLOWS = 1 generate

   newlen_ce_mux(0) <= newlen_ce;
   newlen_cnt_reset(0) <= data_end;

end generate;


-- generic counters for newlen
GEN_BLOCKS: for j in 0 to FLOWS-1 generate
    
    process(CLK)
    begin
      if ((CLK'event) and (CLK = '1')) then
        if (RESET = '1') then
          newlen_cnt1(j) <= conv_std_logic_vector(1, newlen_cnt1(j)'length);
        else
          if (newlen_ce_mux(j) = '1') then
            newlen_cnt1(j) <= newlen_cnt1(j) + 1;
            if (newlen_cnt_reset(j) = '1') then
              newlen_cnt1(j) <= conv_std_logic_vector(1, newlen_cnt1(j)'length);
            end if;
          end if;
        end if;
      end if;
    end process;
  
    newlen_cnt_vect((((j+1)*NEWLEN_WIDTH)-1) downto j*NEWLEN_WIDTH) <= newlen_cnt1(j);

end generate;

  -- newlen mux
GEN_NEWLEN_MUX_MORE_FLOWS: if FLOWS > 1 generate
 
   newlen_mux : entity work.GEN_MUX
      generic map (
         DATA_WIDTH => NEWLEN_WIDTH,
         MUX_WIDTH => FLOWS
      )
      port map (
         DATA_IN   => newlen_cnt_vect,
         SEL       => RX_ADDR,
         DATA_OUT  => newlen_cnt_mux
      );
    
end generate;

GEN_NEWLEN_MUX_ONE_FLOW: if FLOWS = 1 generate

   newlen_cnt_mux <= newlen_cnt_vect;

end generate;

  -- NEWLEN registers
  -- BUF_NEWLEN_IFC register
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        newlen_ifc_reg <= (others => '0');
      else
        newlen_ifc_reg <= RX_ADDR;
      end if;
    end if;
  end process;

  -- BUF_NEWLEN_DV register
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        newlen_dv_reg <= '0';
      else
        newlen_dv_reg <= data_end and newlen_ce;
	    end if;
    end if;
 end process;

  -- BUF_NEWLEN register
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        newlen_reg <= (others => '0');
     else
        newlen_reg <= newlen_cnt_mux;
      end if;
    end if;
  end process;

-- multiplexor
GEN_BUFFER_FULL_MUX_MORE_FLOWS: if FLOWS > 1 generate
   
   buffer_full_mux : entity work.GEN_MUX
      generic map (
         DATA_WIDTH  => MUX_DATA_WIDTH,
         MUX_WIDTH   => FLOWS
      )
      port map (
         DATA_IN     => full_out,
         SEL         => RX_ADDR,
         DATA_OUT    => buffer_full
      );
      
end generate;

GEN_BUFFER_FULL_MUX_ONE_FLOW: if FLOWS = 1 generate

   buffer_full(0) <= full_out(0);

end generate;

  newlen_ce <= write_in and not buffer_full(0);

  zeros <= (others => '0');
  
  -- NEWLEN interface mapping
  BUF_NEWLEN_DV <= newlen_dv_reg;
  BUF_NEWLEN <= newlen_reg 
                & zeros(log2(DATA_WIDTH/8)-1 downto 0);
  BUF_NEWLEN_IFC <= newlen_ifc_reg;

-- --------------------------------------------------
-- -- OTHERS
-- --------------------------------------------------

  RD_ARDY <= RD_DST_RDY and RD_REQ;

  -- interface mapping
  FULL <= full_out;
  RX_DST_RDY_N <= full_out;
  
end architecture;
-- ----------------------------------------------------------------------------
