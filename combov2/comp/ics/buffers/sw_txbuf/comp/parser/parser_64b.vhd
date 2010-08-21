--
-- parser_64b.vhd - Framelink generator for TX BUFFER. Parses raw data
--                  from software - 64b data width version.
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
entity TXBUF_PARSER_64b is
   port (
      CLK               : in  std_logic;
      RESET             : in  std_logic;
      
      -- MEM2NFIFO interface
      FIFO_DATA_OUT     : in  std_logic_vector(63 downto 0);
      FIFO_DATA_VLD     : in  std_logic;
      FIFO_RD           : out std_logic;
      
      -- Control interface
      SENDING_WORD      : out std_logic;
      SENDING_LAST_WORD : out std_logic;
      ZERO_HEADER_SIZE  : out std_logic;  -- Valid together with SOF
      
      -- Output framelink interface
      FL_DATA           : out std_logic_vector(63 downto 0);
      FL_SOF_N          : out std_logic;
      FL_SOP_N          : out std_logic;
      FL_EOP_N          : out std_logic;
      FL_EOF_N          : out std_logic;
      FL_REM            : out std_logic_vector(2 downto 0);
      FL_SRC_RDY_N      : out std_logic;
      FL_DST_RDY_N      : in  std_logic
   );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of TXBUF_PARSER_64b is

   -------------------------------------------------------------------
   -- Constants declarations
   -------------------------------------------------------------------
   constant DATA_WIDTH  : integer := 64;
   constant CNT_STEP    : integer := DATA_WIDTH/8;

   -------------------------------------------------------------------
   -- Signals declarations
   -------------------------------------------------------------------
   -- FSM signals
   type fsm_states is (LOAD_SIZES, SEND_FIRST_HWDATA_WORD, SEND_HWDATA,
      SEND_PAYLOAD);
   signal curr_state, next_state : fsm_states;


   -- HW data and payload and align counters
   signal cnt_hwd_size              : std_logic_vector(15 downto 0);
   signal cnt_hwd_size_ce           : std_logic;
   signal cnt_hwd_size_ld           : std_logic;
   signal cnt_seg_size              : std_logic_vector(15 downto 0);
   signal cnt_seg_size_ce           : std_logic;
   signal cnt_seg_size_ld           : std_logic;

   signal last_hwdata_word          : std_logic;
   signal last_payload_word         : std_logic;
   signal reg_sof_set               : std_logic;
   signal reg_sop_set               : std_logic;
   signal zero_hwdata_size          : std_logic;
   signal reg_sop                   : std_logic;
   signal reg_sof                   : std_logic;
   signal fifo_rd_req               : std_logic;
   signal data_transmission         : std_logic;
   signal src_rdy_n                 : std_logic;
   signal cnt_seg_size_ld_full      : std_logic;
   signal hwdata_drem_generator     : std_logic_vector(2 downto 0);
   signal payload_drem_generator    : std_logic_vector(2 downto 0);
   signal reg_zero_hwdata_size      : std_logic;
   signal reg_zero_hwdata_size_set  : std_logic;
   signal hwdata_first_word         : std_logic;

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
               if (hwdata_first_word = '1') then
                  cnt_hwd_size <= cnt_hwd_size - CNT_STEP/2;
               else
                  cnt_hwd_size <= cnt_hwd_size - CNT_STEP;
               end if;
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
               if (cnt_seg_size_ld_full = '1') then
                  cnt_seg_size <= FIFO_DATA_OUT(15 downto 0);
               else
                  cnt_seg_size <= FIFO_DATA_OUT(15 downto 0) - CNT_STEP;
               end if;
            else
               cnt_seg_size <= cnt_seg_size - CNT_STEP;
            end if;
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


   -- register reg_zero_hwdata_size ------------------------------------------------------
   reg_zero_hwdata_sizep: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_zero_hwdata_size <= '0';
         elsif (reg_zero_hwdata_size_set = '1') then
            reg_zero_hwdata_size <= '1';
         elsif (reg_zero_hwdata_size = '1' and data_transmission = '1') then
            reg_zero_hwdata_size <= '0';
         end if;
      end if;
   end process;

   
   -- When sending the first hwdata word and it's last as well, this signal
   -- is ignored. See SEND_FIRST_HWDATA_WORD for more info
   last_hwdata_word  <=
      '1' when cnt_hwd_size(15 downto 4) = X"000" and
                cnt_hwd_size(3 downto 0) <= "1000" 
      else '0';

   last_payload_word <=
      '1' when cnt_seg_size(15 downto 4) = X"000" and
               cnt_seg_size( 3 downto 0) <= "1000"
       else '0';


   data_transmission <= not (src_rdy_n or FL_DST_RDY_N);

   -- Assume HWDATA_SIZE is 16b: [31:16]
   zero_hwdata_size <=  '1' when FIFO_DATA_OUT(31 downto 16) = X"0000" else '0';

   -- FL_REM generator
   hwdata_drem_generator <= cnt_hwd_size(2 downto 0) - "001";
   payload_drem_generator<= cnt_seg_size(2 downto 0) - "001";

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
      data_transmission, last_hwdata_word, last_payload_word, 
      zero_hwdata_size, cnt_hwd_size)
   begin
      case (curr_state) is

      -- -------------------------------------------------------
      when LOAD_SIZES =>
         next_state <= LOAD_SIZES;

         if (FIFO_DATA_VLD = '1') then
            if (zero_hwdata_size = '1') then
               next_state <= SEND_PAYLOAD;
            else
               next_state <= SEND_FIRST_HWDATA_WORD;
            end if;
         end if;

      -- -------------------------------------------------------
      when SEND_FIRST_HWDATA_WORD =>
         next_state <= SEND_FIRST_HWDATA_WORD;

         if (data_transmission = '1') then
            if (cnt_hwd_size <= conv_std_logic_vector(4, cnt_hwd_size'length))
            then
               next_state <= SEND_PAYLOAD;
            else
               next_state <= SEND_HWDATA;
            end if;
         end if;

      -- -------------------------------------------------------
      when SEND_HWDATA =>
         next_state <= SEND_HWDATA;

         if (data_transmission = '1' and last_hwdata_word = '1') then
            next_state <= SEND_PAYLOAD;
         end if;

      -- -------------------------------------------------------
      when SEND_PAYLOAD =>
         next_state <= SEND_PAYLOAD;

         if (data_transmission = '1' and last_payload_word = '1') then
            next_state <= LOAD_SIZES;
         end if;

      -- -------------------------------------------------------
      when others =>
         null;

      end case;
   end process next_state_logic;
   
   -- -------------------------------------------------------
   output_logic : process(curr_state, FIFO_DATA_VLD, FIFO_DATA_OUT, 
      data_transmission, last_hwdata_word, last_payload_word, 
      zero_hwdata_size, cnt_hwd_size, hwdata_drem_generator,
      payload_drem_generator, FL_DST_RDY_N)
   begin
      cnt_seg_size_ce         <= '0';
      cnt_seg_size_ld         <= '0';
      cnt_seg_size_ld_full    <= '0';
      cnt_hwd_size_ce         <= '0';
      cnt_hwd_size_ld         <= '0';
      reg_sop_set             <= '0';
      reg_sof_set             <= '0';
      reg_zero_hwdata_size_set<= '0';
      fifo_rd_req             <= '0';
      hwdata_first_word       <= '0';

      -- Output framelink control signals (active in '0')
      FL_EOP_N        <= '1';
      FL_EOF_N        <= '1';
      -- low bit/s of the size counters determine FL REM signal
      FL_REM          <= hwdata_drem_generator;
      src_rdy_n       <= '1';

      -- Control output interface
      SENDING_LAST_WORD <= '0';


      case (curr_state) is
      -- -------------------------------------------------------
      when LOAD_SIZES =>

         cnt_seg_size_ce <= '1';
         cnt_seg_size_ld <= '1';
         cnt_hwd_size_ce <= '1';
         cnt_hwd_size_ld <= '1';

         cnt_seg_size_ld_full     <= not zero_hwdata_size;
         fifo_rd_req              <= zero_hwdata_size or not FIFO_DATA_VLD;
         reg_zero_hwdata_size_set <= FIFO_DATA_VLD and zero_hwdata_size;

         reg_sop_set <= '1';
         reg_sof_set <= '1';

      -- -------------------------------------------------------
      when SEND_FIRST_HWDATA_WORD =>

         hwdata_first_word <= '1';
         fifo_rd_req       <= not FL_DST_RDY_N;
         
         -- Add 4 to DREM in case this is the first and last word.
         -- If not, EOF_N will be '1' and FL_REM won't be valid
         FL_REM <= '1' & hwdata_drem_generator(1 downto 0);

         src_rdy_n <= not FIFO_DATA_VLD;

         cnt_seg_size_ce <= data_transmission;
         cnt_hwd_size_ce <= data_transmission;

         if (data_transmission = '1') then
            if (cnt_hwd_size <= conv_std_logic_vector(4, cnt_hwd_size'length))
            then
               FL_EOP_N    <= '0';
               reg_sop_set <= '1';
            end if;
         end if;

      -- -------------------------------------------------------
      when SEND_HWDATA =>

         fifo_rd_req       <= not FL_DST_RDY_N;
         src_rdy_n         <= not FIFO_DATA_VLD;

         FL_REM            <= hwdata_drem_generator;
         FL_EOP_N          <= not last_hwdata_word;
         reg_sop_set       <= last_hwdata_word and data_transmission;

         cnt_seg_size_ce   <= data_transmission;
         cnt_hwd_size_ce   <= data_transmission;

      -- -------------------------------------------------------
      when SEND_PAYLOAD =>
         
         fifo_rd_req       <= not FL_DST_RDY_N;
         src_rdy_n         <= not FIFO_DATA_VLD;
         
         FL_REM            <= payload_drem_generator;
         FL_EOP_N          <= not last_payload_word;
         FL_EOF_N          <= not last_payload_word;
         SENDING_LAST_WORD <= last_payload_word and data_transmission;

         cnt_seg_size_ce   <= data_transmission;
         cnt_hwd_size_ce   <= data_transmission;

      -- -------------------------------------------------------
      when others =>
         null;

      end case;
   end process output_logic;


   -------------------------------------------------------------------
   -- Interface mapping
   -------------------------------------------------------------------
   FIFO_RD           <= fifo_rd_req;

   FL_DATA           <= FIFO_DATA_OUT;
   FL_SRC_RDY_N      <= src_rdy_n;
   FL_SOF_N          <= not reg_sof;
   FL_SOP_N          <= not reg_sop;

   SENDING_WORD      <= fifo_rd_req and FIFO_DATA_VLD;
   ZERO_HEADER_SIZE  <= reg_zero_hwdata_size;

end architecture;
