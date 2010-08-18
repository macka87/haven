--
-- parser.vhd - Framelink generator for TX BUFFER. Parses raw data
--                  from software -- Generic version.
-- Author(s): Lukas Solanka <solanka@liberouter.org>
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
-- README:
--    only 16b version available
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
entity TXBUF_PARSER is
   generic (
      DATA_WIDTH : integer := 16
   );
   port (
      CLK               : in  std_logic;
      RESET             : in  std_logic;
      
      -- MEM2NFIFO interface
      FIFO_DATA_OUT     : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
      FIFO_DATA_VLD     : in  std_logic;
      FIFO_RD           : out std_logic;
      
      -- Control interface -- TODO
      SENDING_WORD      : out std_logic;
      SENDING_LAST_WORD : out std_logic;
      
      -- Output framelink interface
      FL_DATA           : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      FL_SOF_N          : out std_logic;
      FL_SOP_N          : out std_logic;
      FL_EOP_N          : out std_logic;
      FL_EOF_N          : out std_logic;
      FL_REM            : out std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      FL_SRC_RDY_N      : out std_logic;
      FL_DST_RDY_N      : in  std_logic
   );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of TXBUF_PARSER is

-- ==========================================================================
--                                  SIGNALS
-- ==========================================================================
   
   -- the "frame has no header" signal (output of the parser)
   signal parser_zero_header_size   : std_logic;
   -- the "frame has a header" signal (input of the header rearranger)
   signal rearranger_frame_has_hdr  : std_logic;

   -- parser output FrameLink
   signal parser_out_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal parser_out_sof_n       : std_logic;
   signal parser_out_sop_n       : std_logic;
   signal parser_out_eop_n       : std_logic;
   signal parser_out_eof_n       : std_logic;
   signal parser_out_rem         : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal parser_out_src_rdy_n   : std_logic;
   signal parser_out_dst_rdy_n   : std_logic;

begin

   assert ((DATA_WIDTH = 16) or (DATA_WIDTH = 32) or (DATA_WIDTH = 64))
      report "TXBUF_PARSER: Unsupported data width"
      severity error;

   -- Generate 16b parser
   gen16b: if (DATA_WIDTH = 16) generate
   
      PARSER_I: entity work.TXBUF_PARSER_16b
      port map (
         CLK               => CLK,
         RESET             => RESET,
         
         -- MEM2NFIFO interface
         FIFO_DATA_OUT     => FIFO_DATA_OUT,
         FIFO_DATA_VLD     => FIFO_DATA_VLD,
         FIFO_RD           => FIFO_RD,
         
         -- Control interface -- TODO
         SENDING_WORD      => SENDING_WORD,
         SENDING_LAST_WORD => SENDING_LAST_WORD,
         
         -- Output framelink interface
         FL_DATA           => FL_DATA,
         FL_SOF_N          => FL_SOF_N,
         FL_SOP_N          => FL_SOP_N,
         FL_EOP_N          => FL_EOP_N,
         FL_EOF_N          => FL_EOF_N,
         FL_REM            => FL_REM,
         FL_SRC_RDY_N      => FL_SRC_RDY_N,
         FL_DST_RDY_N      => FL_DST_RDY_N
      );

   end generate;

   -- Generate 32b parser
   gen32b: if (DATA_WIDTH = 32) generate
   
      PARSER_I: entity work.TXBUF_PARSER_32b
      port map (
         CLK               => CLK,
         RESET             => RESET,
         
         -- MEM2NFIFO interface
         FIFO_DATA_OUT     => FIFO_DATA_OUT,
         FIFO_DATA_VLD     => FIFO_DATA_VLD,
         FIFO_RD           => FIFO_RD,
         
         -- Control interface -- TODO
         SENDING_WORD      => SENDING_WORD,
         SENDING_LAST_WORD => SENDING_LAST_WORD,
         
         -- Output framelink interface
         FL_DATA           => FL_DATA,
         FL_SOF_N          => FL_SOF_N,
         FL_SOP_N          => FL_SOP_N,
         FL_EOP_N          => FL_EOP_N,
         FL_EOF_N          => FL_EOF_N,
         FL_REM            => FL_REM,
         FL_SRC_RDY_N      => FL_SRC_RDY_N,
         FL_DST_RDY_N      => FL_DST_RDY_N
      );

   end generate;

   -- Generate 64b parser with header rearranger
   gen64b: if (DATA_WIDTH = 64) generate
   
      PARSER_I: entity work.TXBUF_PARSER_64b
      port map (
         CLK               => CLK,
         RESET             => RESET,
         
         -- MEM2NFIFO interface
         FIFO_DATA_OUT     => FIFO_DATA_OUT,
         FIFO_DATA_VLD     => FIFO_DATA_VLD,
         FIFO_RD           => FIFO_RD,
         
         -- Control interface -- TODO
         SENDING_WORD      => SENDING_WORD,
         SENDING_LAST_WORD => SENDING_LAST_WORD,
         ZERO_HEADER_SIZE  => parser_zero_header_size,
         
         -- Output framelink interface
         FL_DATA           => parser_out_data,
         FL_SOF_N          => parser_out_sof_n,
         FL_SOP_N          => parser_out_sop_n,
         FL_EOP_N          => parser_out_eop_n,
         FL_EOF_N          => parser_out_eof_n,
         FL_REM            => parser_out_rem,
         FL_SRC_RDY_N      => parser_out_src_rdy_n,
         FL_DST_RDY_N      => parser_out_dst_rdy_n
      );

      rearranger_frame_has_hdr <= NOT parser_zero_header_size;

      HEADER_REARRANGER_I : entity work.HEADER_REARRANGER
      generic map (
         DATA_WIDTH        => 64
      )
      port map (
         -- common signals
         CLK               => CLK,
         RESET             => RESET,

         -- "frame has header" signal
         FRAME_HAS_HEADER  => rearranger_frame_has_hdr,

         -- input FrameLink
         RX_DATA           => parser_out_data,
         RX_REM            => parser_out_rem,
         RX_SOF_N          => parser_out_sof_n,
         RX_EOF_N          => parser_out_eof_n,
         RX_SOP_N          => parser_out_sop_n,
         RX_EOP_N          => parser_out_eop_n,
         RX_SRC_RDY_N      => parser_out_src_rdy_n,
         RX_DST_RDY_N      => parser_out_dst_rdy_n,
         
         -- output FrameLink
         TX_DATA           => FL_DATA,
         TX_REM            => FL_REM,
         TX_SOF_N          => FL_SOF_N,
         TX_EOF_N          => FL_EOF_N,
         TX_SOP_N          => FL_SOP_N,
         TX_EOP_N          => FL_EOP_N,
         TX_SRC_RDY_N      => FL_SRC_RDY_N,
         TX_DST_RDY_N      => FL_DST_RDY_N
      );

   end generate;

end architecture;
