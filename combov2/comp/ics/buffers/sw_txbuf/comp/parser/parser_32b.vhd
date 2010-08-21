--
-- parser_32b.vhd - Framelink generator for TX BUFFER. Parses raw data
--                  from software.
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
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TXBUF_PARSER_32b is
   port (
      CLK               : in  std_logic;
      RESET             : in  std_logic;
      
      -- MEM2NFIFO interface
      FIFO_DATA_OUT     : in  std_logic_vector(31 downto 0);
      FIFO_DATA_VLD     : in  std_logic;
      FIFO_RD           : out std_logic;
      
      -- Control interface -- TODO
      SENDING_WORD      : out std_logic;
      SENDING_LAST_WORD : out std_logic;
      
      -- Output framelink interface
      FL_DATA           : out std_logic_vector(31 downto 0);
      FL_SOF_N          : out std_logic;
      FL_SOP_N          : out std_logic;
      FL_EOP_N          : out std_logic;
      FL_EOF_N          : out std_logic;
      FL_REM            : out std_logic_vector(1 downto 0);
      FL_SRC_RDY_N      : out std_logic;
      FL_DST_RDY_N      : in  std_logic
   );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of TXBUF_PARSER_32b is

   -------------------------------------------------------------------
   -- Constants declarations
   -------------------------------------------------------------------
   constant DATA_WIDTH  : integer := 32;
   constant CNT_STEP    : integer := DATA_WIDTH/8;

   -------------------------------------------------------------------
   -- Signals declarations
   -------------------------------------------------------------------
   -- FSM signals
   type fsm_states is (LOAD_SIZES, SEND_HWDATA,
            ALIGN_HWDATA, SEND_PAYLOAD, ALIGN_PAYLOAD);
   signal curr_state, next_state : fsm_states;


   -- HW data and payload and align counters
   signal cnt_hwd_size            : std_logic_vector(15 downto 0);
   signal cnt_hwd_size_ce         : std_logic;
   signal cnt_hwd_size_ld         : std_logic;
   signal cnt_seg_size            : std_logic_vector(15 downto 0);
   signal cnt_seg_size_ce         : std_logic;
   signal cnt_seg_size_ld         : std_logic;
   signal cnt_data_aligned_64b    : std_logic_vector(2 downto 0);
   signal cnt_data_aligned_64b_ce : std_logic;


   signal cmp_data_aligned  : std_logic;
   signal last_hwdata_word  : std_logic;
   signal last_payload_word : std_logic;
   signal reg_sof_set       : std_logic;
   signal reg_sop_set       : std_logic;
   signal zero_hwdata_size  : std_logic;
   signal reg_sop           : std_logic;
   signal reg_sof           : std_logic;
   signal fifo_rd_req       : std_logic;
   signal data_transmission : std_logic;
   signal src_rdy_n         : std_logic;

begin

   -------------------------------------------------------------------
   -- Control and data registers and signals
   -------------------------------------------------------------------
   -- cnt_hwd_size counter
   -- Counts remaining bytes of the HW data (framelink header)
   cnt_hwd_sizep: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_hwd_size <= (others => '0');
         elsif (cnt_hwd_size_ce = '1') then
            if (cnt_hwd_size_ld = '1') then
               cnt_hwd_size <= FIFO_DATA_OUT(31 downto 16);
            else
               cnt_hwd_size <= cnt_hwd_size - CNT_STEP;
            end if;
         end if;
      end if;
   end process;


   -- cnt_seg_size counter
   -- Counts remaining bytes of segment to transfer
   cnt_seg_sizep: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_seg_size <= (others => '0');
         elsif (cnt_seg_size_ce = '1') then
            if (cnt_seg_size_ld = '1') then
               cnt_seg_size <= FIFO_DATA_OUT(15 downto 0) - CNT_STEP;
            else
               cnt_seg_size <= cnt_seg_size - CNT_STEP;
            end if;
         end if;
      end if;
   end process;


   -- cnt_data_aligned_64b counter
   -- This counter counts number of bytes transmitted
   cnt_data_aligned_64bp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_data_aligned_64b <= (others => '0');
         elsif (cnt_data_aligned_64b_ce = '1') then
            cnt_data_aligned_64b <= cnt_data_aligned_64b + CNT_STEP;
         end if;
      end if;
   end process;


   -------------------------------------------------------------------
   -- SOP and SOF registers
   -- These are set by the FSM. Once the register is set, the first
   -- data transmission resets it so SOP/SOF last only one data transmission
   -- cycle
   -------------------------------------------------------------------

   -- register reg_sop ------------------------------------------------------
   reg_sopp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_sop <= '0';
         elsif (reg_sop_set = '1') then
            reg_sop <= '1';
         elsif (reg_sop = '1' and data_transmission = '1') then
            reg_sop <= '0';
         end if;
      end if;
   end process;

   -- register reg_sof ------------------------------------------------------
   reg_sofp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_sof <= '0';
         elsif (reg_sof_set = '1') then
            reg_sof <= '1';
         elsif (reg_sof = '1' and data_transmission = '1') then
            reg_sof <= '0';
         end if;
      end if;
   end process;

   
   -- cmp_data_aligned
   -- Comparator for the last word to be transmitted to align to the
   -- 64b boundary
   cmp_data_aligned <= '1' when cnt_data_aligned_64b(2) = '1'
                       else '0';

   last_hwdata_word  <=
      '1' when cnt_hwd_size(15 downto 3) = X"000" & '0' and
                cnt_hwd_size(2 downto 0) <= "100" 
      else '0';

   last_payload_word <=
      '1' when cnt_seg_size(15 downto 3) = X"000" & '0' and
               cnt_seg_size( 2 downto 0) <= "100"
       else '0';


   data_transmission <= not (src_rdy_n or FL_DST_RDY_N);
   zero_hwdata_size <=
      '1' when FIFO_DATA_OUT(31 downto 16) = conv_std_logic_vector(0, cnt_hwd_size'length)
      else '0';

   -------------------------------------------------------------------
   -- Parsing FSM
   -------------------------------------------------------------------

   -- -------------------------------------------------------
   sync_logic : process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            curr_state <= LOAD_SIZES;
         else
            curr_state <= next_state;
         end if;
      end if;
   end process sync_logic;
   
   -- -------------------------------------------------------
   next_state_logic : process(curr_state, FIFO_DATA_VLD, FIFO_DATA_OUT, 
      data_transmission, last_hwdata_word, last_payload_word, cmp_data_aligned,
      zero_hwdata_size)
   begin
      case (curr_state) is

      -- -------------------------------------------------------
      when LOAD_SIZES =>
         next_state <= LOAD_SIZES;
            
         if (FIFO_DATA_VLD = '1') then
            if (zero_hwdata_size = '1') then
               next_state <= ALIGN_HWDATA;
            else
               next_state <= SEND_HWDATA;
            end if;
         end if;

      -- -------------------------------------------------------
      when SEND_HWDATA =>
         next_state <= SEND_HWDATA;

         if (data_transmission = '1' and last_hwdata_word = '1') then
            if (cmp_data_aligned = '1') then
               next_state <= SEND_PAYLOAD;
            else
               next_state <= ALIGN_HWDATA;
            end if;
         end if;

      -- -------------------------------------------------------
      when ALIGN_HWDATA =>
         next_state <= ALIGN_HWDATA;

         if (FIFO_DATA_VLD = '1' and cmp_data_aligned = '1') then
            next_state <= SEND_PAYLOAD;
         end if;

      -- -------------------------------------------------------
      when SEND_PAYLOAD =>
         next_state <= SEND_PAYLOAD;

         if (data_transmission = '1' and last_payload_word = '1') then
            if (cmp_data_aligned = '1') then
               next_state <= LOAD_SIZES;
            else
               next_state <= ALIGN_PAYLOAD;
            end if;
         end if;

      -- -------------------------------------------------------
      when ALIGN_PAYLOAD =>
         next_state <= ALIGN_PAYLOAD;

         if (FIFO_DATA_VLD = '1' and cmp_data_aligned = '1') then
            next_state <= LOAD_SIZES;
         end if;

      -- -------------------------------------------------------
      when others =>
         null;

      end case;
   end process next_state_logic;
   
   -- -------------------------------------------------------
   output_logic : process(curr_state, FIFO_DATA_VLD, FIFO_DATA_OUT, 
      data_transmission, last_hwdata_word, last_payload_word, cmp_data_aligned,
      zero_hwdata_size, cnt_hwd_size, FL_DST_RDY_N, cnt_seg_size)
   begin
      cnt_seg_size_ce         <= '0';
      cnt_seg_size_ld         <= '0';
      cnt_hwd_size_ce         <= '0';
      cnt_hwd_size_ld         <= '0';
      cnt_data_aligned_64b_ce <= '0';
      reg_sop_set             <= '0';
      reg_sof_set             <= '0';
      fifo_rd_req             <= '0';

      -- Output framelink control signals (active in '0')
      FL_EOP_N        <= '1';
      FL_EOF_N        <= '1';
      -- low bit/s of the size counters determine FL REM signal
      FL_REM          <= cnt_hwd_size(1 downto 0) - "01";
      src_rdy_n       <= '1';

      -- Control output interface
      SENDING_LAST_WORD <= '0';


      case (curr_state) is
      -- -------------------------------------------------------
      when LOAD_SIZES =>
         fifo_rd_req     <= '1';

         if (FIFO_DATA_VLD = '1') then
           reg_sof_set     <= '1';
           reg_sop_set     <= '1';
           cnt_seg_size_ce <= '1';
           cnt_seg_size_ld <= '1';
           cnt_data_aligned_64b_ce <= '1';
           cnt_hwd_size_ce <= '1';
           cnt_hwd_size_ld <= '1';
         end if;

      -- -------------------------------------------------------
      when SEND_HWDATA =>
         cnt_hwd_size_ce         <= data_transmission;
         cnt_seg_size_ce         <= data_transmission;
         cnt_data_aligned_64b_ce <= data_transmission;
         src_rdy_n               <= not FIFO_DATA_VLD;
         fifo_rd_req             <= not FL_DST_RDY_N;

         if (last_hwdata_word = '1') then
            FL_EOP_N    <= '0';
            if (data_transmission = '1') then
               reg_sop_set <= '1';
            end if;
         end if;

      -- -------------------------------------------------------
      when ALIGN_HWDATA =>
         fifo_rd_req             <= '1';
         reg_sop_set             <= '1';

         if (FIFO_DATA_VLD = '1') then
            cnt_seg_size_ce         <= '1';
            cnt_data_aligned_64b_ce <= '1';
         end if;

      -- -------------------------------------------------------
      when SEND_PAYLOAD =>
         cnt_hwd_size_ce         <= data_transmission;
         cnt_seg_size_ce         <= data_transmission;
         cnt_data_aligned_64b_ce <= data_transmission;
         src_rdy_n               <= not FIFO_DATA_VLD;
         fifo_rd_req             <= not FL_DST_RDY_N;
         FL_REM                  <= cnt_seg_size(1 downto 0) - 1;

         if (last_payload_word = '1') then
            FL_EOP_N <= '0';
            FL_EOF_N <= '0';

            if (data_transmission = '1' and cmp_data_aligned = '1') then
               SENDING_LAST_WORD <= '1';
            end if;

         end if;

      -- -------------------------------------------------------
      when ALIGN_PAYLOAD =>
         fifo_rd_req <= '1';
         if (FIFO_DATA_VLD = '1') then
            cnt_seg_size_ce         <= '1';
            cnt_data_aligned_64b_ce <= '1';
            
            if (cmp_data_aligned = '1') then
               SENDING_LAST_WORD <= '1';
            end if;

         end if;

      -- -------------------------------------------------------
      when others =>
         null;

      end case;
   end process output_logic;


   -------------------------------------------------------------------
   -- Interface mapping
   -------------------------------------------------------------------
   FIFO_RD      <= fifo_rd_req;

   FL_DATA      <= FIFO_DATA_OUT;
   FL_SRC_RDY_N <= src_rdy_n;
   FL_SOF_N     <= not reg_sof;
   FL_SOP_N     <= not reg_sop;

   SENDING_WORD <= fifo_rd_req and FIFO_DATA_VLD;

end architecture;
