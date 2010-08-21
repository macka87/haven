-- fifo2nfifo_buffer.vhd: Fifo2nfifo buffer unit
-- Copyright (C) 2009 CESNET
-- Author(s): Jakub Olbert <xolber00@stud.fit.vutbr.cz>
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
--  $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FIFO2NFIFO_BUFFER is
   generic(
      -- Input data width - should be multiple of 8
      -- only 8, 16, 32, 64, 128 supported
      -- Output width is DATA_WIDTH / OUTPUT_COUNT
      DATA_WIDTH     : integer;
      -- number of output interfaces: only 2,4,8,16 supported
      OUTPUT_COUNT   : integer;
      -- number of frame parts
      FRAME_PARTS    : integer;
      -- 
      BLOCK_SIZE     : integer := 128;
      STATUS_WIDTH   : integer := 4;
      -- use BRAMS instead of LUT
      USE_BRAMS      : boolean := true;
      -- use global state
      GLOB_STATE     : boolean := false
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interface (framelink)                    -- connected
      RX_SOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic_vector(OUTPUT_COUNT-1 downto 0);
      RX_DST_RDY_N   : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

      -- status signal for control unit                 -- connected
      STATUS         : out std_logic_vector((OUTPUT_COUNT*STATUS_WIDTH)-1 
                                              downto 0);

      -- output interface (framelink * OUTPUT_COUNT)    -- connected
      TX_SOF_N       : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_SOP_N       : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_EOP_N       : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_EOF_N       : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_SRC_RDY_N   : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_DST_RDY_N   : in  std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out
      std_logic_vector(OUTPUT_COUNT*log2(DATA_WIDTH/OUTPUT_COUNT/8)-1 
                                                                     downto 0)
   );
end entity FIFO2NFIFO_BUFFER;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FIFO2NFIFO_BUFFER is
   -- Function declaration ----------------------------------------------------
   -- return width of JUICE signal
   function get_juice_width(data_width, flows : integer) return integer is
   begin
      return 1;
   end function get_juice_width;

   -- return width of fifo data input
   -- N * (TX_REM_WIDTH + JUICE_WIDTH + DISCARD) + DATA_WIDTH
   function get_fifo_data_width(data_width, flows : integer) return integer is
   begin     
      return flows * (log2(data_width/OUTPUT_COUNT/8)
             + get_juice_width(data_width,flows) + 1) + data_width;
   end function get_fifo_data_width;

   -- Constant declaration ----------------------------------------------------
   constant JUICE_WIDTH : integer := get_juice_width(DATA_WIDTH, OUTPUT_COUNT);
   constant RX_REM_WIDTH : integer := log2(DATA_WIDTH/8);
   constant TX_REM_WIDTH : integer := log2(DATA_WIDTH/OUTPUT_COUNT/8);
   constant FIFO_DATA_WIDTH : integer := get_fifo_data_width(DATA_WIDTH,
                                                                 OUTPUT_COUNT);
   constant OUTPUT_FL_DATA_WIDTH : integer := DATA_WIDTH / OUTPUT_COUNT;
   constant FIFO_IN_FLOW_WIDTH   : integer := OUTPUT_FL_DATA_WIDTH + 1 
                                                  + TX_REM_WIDTH + JUICE_WIDTH;

   -- Signal declaration ------------------------------------------------------
   signal RX_DST_RDY_N_single : std_logic;
   signal RX_SRC_RDY_N_single : std_logic;

   -- fifo interface
   signal block_addr   : std_logic_vector(abs(log2(OUTPUT_COUNT)-1) downto 0);
   signal fifo_status  : std_logic_vector(log2(BLOCK_SIZE+1)*OUTPUT_COUNT-1
                                                                    downto 0);
   signal fifo_data_in : std_logic_vector(FIFO_DATA_WIDTH-1 downto 0);
   signal fifo_data_out: std_logic_vector(FIFO_DATA_WIDTH-1 downto 0);
   signal fifo_write   : std_logic;
   signal fifo_data_vld: std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal fifo_read    : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal fifo_empty   : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal fifo_full    : std_logic_vector(OUTPUT_COUNT-1 downto 0);

   -- compress and decompress units interface
   signal fl_juice_in  : std_logic_vector(JUICE_WIDTH -1 downto 0);
   signal fl_juice_out : std_logic_vector(JUICE_WIDTH*OUTPUT_COUNT-1 downto 0);
   signal frame_part   : std_logic;
   signal discard      : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal disc_part    : std_logic_vector(log2(OUTPUT_COUNT)-1 downto 0);
   signal rx_rem_transformed : std_logic_vector(log2(OUTPUT_FL_DATA_WIDTH/8)-1
                                                       downto 0);
begin

   -- Convert cu_src_rdy_n to block_addr --------------------------------------
   BLOCK_ADDR_CONV: process (RX_SRC_RDY_N)
   begin
      block_addr <= (others => '0');
      for i in 0 to OUTPUT_COUNT-1 loop
         if (RX_SRC_RDY_N(i) = '0') then
            block_addr <= conv_std_logic_vector(i, block_addr'length);
         end if;
      end loop;
   end process;

   -- Convert fifo2nfifo status to CU status ----------------------------------
   assert (STATUS_WIDTH < log2(BLOCK_SIZE+1))
      report "STATUS_WIDTH must be less then FIFO2NFIFO STATUS'length."
      severity failure;

   STATUS_CONV : FOR i IN 0 TO OUTPUT_COUNT-1 GENERATE
      process(fifo_status)
      begin
         -- MSB is set -> memory is full (no free items)
         if (fifo_status((i+1)*log2(BLOCK_SIZE+1)-1) = '1') then
            STATUS((i+1)*STATUS_WIDTH-1 downto i*STATUS_WIDTH) <=
               (others => '0');
         -- convert STATUS_WIDTH bits after MSB from "occupied" to "free"
         else
            STATUS((i+1)*STATUS_WIDTH-1 downto i*STATUS_WIDTH) <=
               not fifo_status((i+1)*log2(BLOCK_SIZE+1)-2 downto
                               (i+1)*log2(BLOCK_SIZE+1)-STATUS_WIDTH-1);
         end if;
      end process;
   END GENERATE STATUS_CONV;

   -- Fifo2nfifo --------------------------------------------------------------
   FIFO2NFIFO : entity work.FIFO2NFIFO
   generic map(
      DATA_WIDTH => FIFO_DATA_WIDTH,
      FLOWS      => OUTPUT_COUNT,
      BLOCK_SIZE => BLOCK_SIZE,
      LUT_MEMORY => not USE_BRAMS,
      GLOB_STATE => GLOB_STATE
   )
   port map(
      -- common interface
      CLK        => CLK,
      RESET      => RESET,

      -- Write interface
      DATA_IN    => fifo_data_in,
      BLOCK_ADDR => block_addr,
      WRITE      => fifo_write,
      FULL       => fifo_full,

      -- Read interface
      DATA_OUT   => fifo_data_out,
      DATA_VLD   => fifo_data_vld,
      READ       => fifo_read,
      EMPTY      => fifo_empty,

      -- status (for Control unit)
      STATUS     => fifo_status
   );

   -- FL_COMPRESS unit --------------------------------------------------------
   COMPRESS : entity work.FL_COMPRESS
   generic map(
      WIRES => JUICE_WIDTH
   )
   port map(
      -- common interface
      CLK => CLK,
      RESET => RESET,

      -- inform about valid data
      RX_SRC_RDY_N => RX_SRC_RDY_N_single,
      RX_DST_RDY_N => RX_DST_RDY_N_single,

      -- Framelink control signals 
      RX_SOF_N => RX_SOF_N,
      RX_EOF_N => RX_EOF_N,
      RX_SOP_N => RX_SOP_N,
      RX_EOP_N => RX_EOP_N,

      -- Compressed Framelink control signals
      FL_JUICE => fl_juice_in,

      -- Each cycle in '0' mean one part (for FL_DECOMPRESS)
      FRAME_PART => frame_part
   );

   -- generate Align units ----------------------------------------------------
   ALIGN_UNITS : FOR n IN 0 TO OUTPUT_COUNT-1 GENERATE
      ALIGN_UNIT : entity work.FL_SPLITTER_ALIGN_UNIT
      generic map(
         INPUT_WIDTH  => FIFO_IN_FLOW_WIDTH,
         OUTPUT_WIDTH => OUTPUT_FL_DATA_WIDTH,
         JUICE_WIDTH  => JUICE_WIDTH,
         REM_WIDTH    => TX_REM_WIDTH
      )
      port map(
         -- common interface
         CLK   => CLK,
         RESET => RESET,

         -- input interface (shared with FIFO2NFIFO)
         FRAME_PART => frame_part,
         DATA_IN    => fifo_data_out((n+1)*FIFO_IN_FLOW_WIDTH-1 
                       downto n*(FIFO_IN_FLOW_WIDTH)),
         READ       => fifo_read(n),
         DATA_VLD   => fifo_data_vld(n),
         EMPTY      => fifo_empty(n),

         -- output interface (OUTPUT_COUNT * Framelink)
         TX_DATA    => TX_DATA((n+1)*(OUTPUT_FL_DATA_WIDTH)-1 downto
                       n*(OUTPUT_FL_DATA_WIDTH)),
         TX_REM     => TX_REM((n+1)*TX_REM_WIDTH-1 downto n*TX_REM_WIDTH),
         TX_SOF_N   => TX_SOF_N(n),
         TX_SOP_N   => TX_SOP_N(n),
         TX_EOP_N   => TX_EOP_N(n),
         TX_EOF_N   => TX_EOF_N(n),
         TX_DST_RDY_N => TX_DST_RDY_N(n),
         TX_SRC_RDY_N => TX_SRC_RDY_N(n)
      );
   END GENERATE ALIGN_UNITS;

   -- directly mapped signals -------------------------------------------------
   -- input interface
   RX_DST_RDY_N <= fifo_full;
   RX_DST_RDY_N_single <= '0' WHEN 
                  fifo_full(conv_integer(unsigned(block_addr))) = '0' ELSE '1';
   RX_SRC_RDY_N_single <= '1' WHEN conv_integer(unsigned(not RX_SRC_RDY_N)) =
                          0 ELSE '0';

   -- connect fifo data input -------------------------------------------------
   FIFO_INPUT : FOR n IN 0 TO OUTPUT_COUNT-1 GENERATE
      fifo_data_in((n+1)*FIFO_IN_FLOW_WIDTH-1 downto n*FIFO_IN_FLOW_WIDTH) <=
         RX_DATA((n+1)*OUTPUT_FL_DATA_WIDTH-1 downto n*OUTPUT_FL_DATA_WIDTH)
         & rx_rem_transformed
         & fl_juice_out(n)
         & discard(n);
   END GENERATE FIFO_INPUT;

   -- transform REM signal ----------------------------------------------------
   rx_rem_transformed <= RX_REM(TX_REM_WIDTH-1 downto 0);

   -- set JUICE and DISCARD signals -------------------------------------------
   disc_part <= RX_REM(RX_REM'left downto RX_REM'left-(log2(OUTPUT_COUNT)-1)) when RX_EOP_N = '0'else
	        (others => '1');

   DISC_2 : IF OUTPUT_COUNT = 2 GENERATE                -- 2 output interfaces
      discard <= "10" when disc_part = "0" else
                 "00" when disc_part = "1" else
                 "11";  -- error state
      fl_juice_out <= '1' & fl_juice_in when disc_part = "0" else
                      fl_juice_in & '1';
   END GENERATE DISC_2;

   DISC_4 : IF OUTPUT_COUNT = 4 GENERATE                -- 4 output interfaces 
      discard <= "1110" when disc_part = "00" else
                 "1100" when disc_part = "01" else
                 "1000" when disc_part = "10" else
                 "0000" when disc_part = "11" else
                 "1111"; -- invalid state

      fl_juice_out <= fl_juice_in & "111" when disc_part = "11" else
                      '1' & fl_juice_in & "11" when disc_part = "10" else
                      "11" & fl_juice_in & '1' when disc_part = "01" else
                      "111" & fl_juice_in;
   END GENERATE DISC_4;

   DISC_8 : IF OUTPUT_COUNT = 8 GENERATE                -- 8 output interfaces
      discard <= 
         "11111110"  when  disc_part = "000"  else
         "11111100"  when  disc_part = "001"  else
         "11111000"  when  disc_part = "010"  else
         "11110000"  when  disc_part = "011"  else
         "11100000"  when  disc_part = "100"  else
         "11000000"  when  disc_part = "101"  else
         "10000000"  when  disc_part = "110"  else
         "00000000"  when  disc_part = "111"  else
         "11111111"; -- invalid state

      fl_juice_out <= 
         fl_juice_in & "1111111"       when  disc_part = "111"  else
         '1' & fl_juice_in & "111111"  when  disc_part = "110"  else
         "11" & fl_juice_in & "11111"  when  disc_part = "101"  else
         "111" & fl_juice_in & "1111"  when  disc_part = "100"  else
         "1111" & fl_juice_in & "111"  when  disc_part = "011"  else
         "11111" & fl_juice_in & "11"  when  disc_part = "010"  else
         "111111" & fl_juice_in & '1'  when  disc_part = "001"  else
         "1111111" & fl_juice_in;
   END GENERATE DISC_8;

   -- write to fifo2nfifo when valid data are available and fifo isn't full
   enable_write_fifo : process(RX_SRC_RDY_N, fifo_full,block_addr)
   begin
      fifo_write <= '0';
      if (RX_SRC_RDY_N(conv_integer(unsigned(block_addr))) = '0') then
         if (fifo_full(conv_integer(unsigned(block_addr))) = '0') then
            fifo_write <= '1';
         end if;
      end if;
   end process enable_write_fifo;

end architecture full;

