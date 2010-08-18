-- cu.vhd: SW_TXBUF Control Unit architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- library containing if-else function
use work.swt_func.all;


-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity SWT_CU is
   generic(
      DATA_WIDTH     : integer;
      BMEM_ITEMS     : integer;
      BMEM_LENGTH_WIDTH : integer;
      BMEM_OFFSET_WIDTH : integer;
      CTRL_MEM_ITEMS : integer;
      CONTROL_DATA_LENGTH : integer;
      CONSTANT_HW_HEADER_LENGTH : integer;
      CONSTANT_HW_HEADER_DATA : std_logic_vector(63 downto 0)
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- BlockRAM interface
      BMEM_ADDR      : out std_logic_vector(log2(BMEM_ITEMS)-1 downto 0);
      BMEM_RD        : out std_logic;
      BMEM_PIPE_EN   : out std_logic;
      BMEM_DO        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      BMEM_DV        : in  std_logic;
      
      -- Control Memory interface
      CTRL_OFFSET    : in  std_logic_vector(BMEM_OFFSET_WIDTH-1 downto 0);
      CTRL_LENGTH    : in  std_logic_vector(BMEM_LENGTH_WIDTH-1 downto 0);
      CTRL_EMPTY     : in  std_logic;
      CTRL_RRQ       : out std_logic;

      -- Control Bus interface
      SEND_ACK       : out std_logic;
      SEND_ACK_RDY   : in  std_logic;
      
      -- output FrameLink interface
      SOF_N          : out std_logic;
      SOP_N          : out std_logic;
      EOP_N          : out std_logic;
      EOF_N          : out std_logic;
      SRC_READY      : out std_logic;
      DST_READY      : in  std_logic;
      DATA_OUT       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      REM_OUT        : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0)
   );
end entity SWT_CU;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of SWT_CU is

   -- ------------------ Constants declaration --------------------------------
   constant BMEM_ADDR_WIDTH   : integer := log2(BMEM_ITEMS);
   constant WORD_WIDTH        : integer := log2(DATA_WIDTH/8);

   -- ------------------ Signals declaration ----------------------------------
   
   -- counters
   signal cnt_addr            : std_logic_vector(BMEM_ADDR_WIDTH-1 downto 0);
   signal cnt_addr_ce         : std_logic;
   signal cnt_addr_load       : std_logic;
   signal cnt_length          : std_logic_vector(BMEM_LENGTH_WIDTH-WORD_WIDTH-1
                                                                     downto 0);
   signal cnt_length_ce       : std_logic;
   signal cnt_length_load     : std_logic;
   
   -- registers
   signal reg_drem            : std_logic_vector(WORD_WIDTH-1 downto 0);
   signal reg_drem_we         : std_logic;
   signal reg_packet_sop      : std_logic;
   signal reg_packet_sop_we   : std_logic;

   -- (de)multiplexers
   signal mx_tx_src_rdy       : std_logic;
   signal mx_tx_data          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal mx_tx_rem           : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal mx_tx_sof_n         : std_logic;
   signal mx_tx_sop_n         : std_logic;
   signal mx_tx_eop_n         : std_logic;
   signal mx_tx_eof_n         : std_logic;

   -- fsm signals
   -- input signals
   signal fsm_empty           : std_logic;
   signal fsm_header_last_word : std_logic;
   signal fsm_packet_last_word : std_logic;
   signal fsm_send_ack_rdy    : std_logic;
   -- output signals
   signal fsm_read_ctrl       : std_logic;
   signal fsm_send_ack        : std_logic;
   signal fsm_packet_enable   : std_logic;
   signal fsm_header_enable   : std_logic;

   -- others
   signal cnt_length_min      : std_logic;
   signal hw_header_last_word : std_logic;
   signal hw_header_tx_src_rdy_n : std_logic;
   signal hw_header_tx_dst_rdy_n : std_logic;
   signal hw_header_tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal hw_header_tx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal hw_header_tx_sop_n  : std_logic;
   signal hw_header_tx_eop_n  : std_logic;
   signal packet_output_dv    : std_logic;

begin
   -- directly mapped signals -------------------------------------------------
   hw_header_tx_dst_rdy_n <= not DST_READY;
   packet_output_dv  <= BMEM_DV and DST_READY;

   -- CU output signals
   BMEM_ADDR         <= cnt_addr;
   DATA_OUT          <= mx_tx_data;
   BMEM_RD           <= fsm_packet_enable and DST_READY;
   BMEM_PIPE_EN      <= '1';
   CTRL_RRQ          <= fsm_read_ctrl;
   SRC_READY         <= mx_tx_src_rdy;
   REM_OUT           <= mx_tx_rem;
   SEND_ACK          <= fsm_send_ack;
   SOF_N             <= mx_tx_sof_n;
   SOP_N             <= mx_tx_sop_n;
   EOP_N             <= mx_tx_eop_n;
   EOF_N             <= mx_tx_eof_n;

   -- FSM input signals
   fsm_empty            <= CTRL_EMPTY;
   fsm_header_last_word <= hw_header_last_word;
   fsm_packet_last_word <= cnt_length_min and packet_output_dv;
   fsm_send_ack_rdy     <= SEND_ACK_RDY;
   
   -- counter control signals
   cnt_addr_ce       <= fsm_packet_enable and packet_output_dv;
   cnt_addr_load     <= fsm_read_ctrl;
   cnt_length_ce     <= fsm_packet_enable and packet_output_dv;
   cnt_length_load   <= fsm_read_ctrl;

   -- register control signals
   reg_drem_we       <= fsm_read_ctrl;
   reg_packet_sop_we <= fsm_read_ctrl or (fsm_packet_enable and reg_packet_sop 
                        and packet_output_dv);
   
   -- ------------------ comparator cnt_length_min ----------------------------
   cnt_length_minp: process (cnt_length)
   begin
      if cnt_length = conv_std_logic_vector(0, cnt_length'length) then 
         cnt_length_min  <= '1';
      else
         cnt_length_min  <= '0';
      end if;
   end process;
   
   -- ------------------ counter cnt_length -----------------------------------
   cnt_lengthp: process (CLK) 
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' then 
            cnt_length <= (others => '0');
         elsif cnt_length_load = '1' then
            cnt_length <= CTRL_LENGTH(BMEM_LENGTH_WIDTH-1 downto WORD_WIDTH);
         else
            if cnt_length_ce = '1' then
               cnt_length <= cnt_length - 1;
            end if;
         end if;
      end if;
   end process;

   -- ------------------ counter cnt_addr -------------------------------------
   cnt_addrp: process (CLK) 
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' then 
            cnt_addr <= (others => '0');
         elsif cnt_addr_load = '1' then
            cnt_addr <= CTRL_OFFSET(BMEM_ADDR_WIDTH+WORD_WIDTH-1 downto WORD_WIDTH);
         else
            if cnt_addr_ce = '1' then
               cnt_addr <= cnt_addr + 1;
            end if;
         end if;
      end if;
   end process;

   -- ------------------ register reg_drem ------------------------------------
   reg_dremp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (reg_drem_we = '1') then
            reg_drem <= CTRL_LENGTH(WORD_WIDTH-1 downto 0) - 1;
         end if;
      end if;
   end process;

   -- ------------------ register reg_packet_sop ------------------------------
   reg_packet_sopp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if RESET = '1' then 
            reg_packet_sop <= '0';
         elsif (reg_packet_sop_we = '1') then
            reg_packet_sop <= fsm_read_ctrl and 
                              not (fsm_packet_enable and reg_packet_sop 
                              and packet_output_dv);
         end if;
      end if;
   end process;

   -- multiplexer mx_tx_rem ---------------------------------------------------
   mx_tx_remp: process(fsm_header_enable, reg_drem, hw_header_tx_rem)
   begin
      case fsm_header_enable is
         when '0' => mx_tx_rem <= reg_drem;
         when '1' => mx_tx_rem <= hw_header_tx_rem;
         when others => mx_tx_rem <= (others => 'X');
      end case;
   end process;

   -- multiplexer mx_tx_src_rdy -----------------------------------------------
   mx_tx_src_rdyp: process(fsm_header_enable, fsm_packet_enable, BMEM_DV, 
                           hw_header_tx_src_rdy_n)
   begin
      case fsm_header_enable is
         when '0' => mx_tx_src_rdy <= fsm_packet_enable and BMEM_DV;
         when '1' => mx_tx_src_rdy <= not hw_header_tx_src_rdy_n;
         when others => mx_tx_src_rdy <= '1';
      end case;
   end process;

   -- multiplexer mx_tx_data --------------------------------------------------
   mx_tx_datap: process(fsm_header_enable, BMEM_DO, hw_header_tx_data)
   begin
      case fsm_header_enable is
         when '0' => mx_tx_data <= BMEM_DO;
         when '1' => mx_tx_data <= hw_header_tx_data;
         when others => mx_tx_data <= (others => 'X');
      end case;
   end process;
   
   GEN_SOF_HEADER: if CONSTANT_HW_HEADER_LENGTH > 0 generate
      mx_tx_sof_n <= hw_header_tx_sop_n or (not fsm_header_enable);
   end generate;

   GEN_SOF_NOHEADER: if CONSTANT_HW_HEADER_LENGTH = 0 generate
      mx_tx_sof_n <= not reg_packet_sop;
   end generate;

   -- multiplexer mx_tx_sop_n -------------------------------------------------
   mx_tx_sop_np: process(fsm_header_enable, reg_packet_sop, hw_header_tx_sop_n)
   begin
      case fsm_header_enable is
         when '0' => mx_tx_sop_n <= not reg_packet_sop;
         when '1' => mx_tx_sop_n <= hw_header_tx_sop_n;
         when others => mx_tx_sop_n <= '1';
      end case;
   end process;

   -- multiplexer mx_tx_eop_n -------------------------------------------------
   mx_tx_eop_np: process(fsm_header_enable, cnt_length_min, hw_header_tx_eop_n)
   begin
      case fsm_header_enable is
         when '0' => mx_tx_eop_n <= not cnt_length_min;
         when '1' => mx_tx_eop_n <= hw_header_tx_eop_n;
         when others => mx_tx_eop_n <= '1';
      end case;
   end process;

   mx_tx_eof_n <= not cnt_length_min;
   
   -- mapping Control Unit FSM
   SWT_CU_FSM_I : entity work.SWT_CU_FSM
      generic map(
         HW_HEADER_LENGTH => CONSTANT_HW_HEADER_LENGTH
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- input signals
         EMPTY          => fsm_empty,
         HEADER_LAST_WORD => fsm_header_last_word,
         PACKET_LAST_WORD => fsm_packet_last_word,
         SEND_ACK_RDY   => fsm_send_ack_rdy,
         -- output signals
         READ_CTRL      => fsm_read_ctrl,
         SEND_ACK       => fsm_send_ack,
         PACKET_ENABLE  => fsm_packet_enable,
         HEADER_ENABLE  => fsm_header_enable
      );
   
   -- mapping HW header sender
   HEADER_SENDER_I : entity work.SWT_HW_HEADER_SENDER
      generic map(
         DATA_WIDTH                 => DATA_WIDTH,
         CONSTANT_HW_HEADER_LENGTH  => CONSTANT_HW_HEADER_LENGTH,
         CONSTANT_HW_HEADER_DATA    => CONSTANT_HW_HEADER_DATA
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- control interface
         SENDER_ENABLE  => fsm_header_enable,
         LAST_WORD      => hw_header_last_word,
         -- output interface
         TX_SRC_RDY_N   => hw_header_tx_src_rdy_n,
         TX_DST_RDY_N   => hw_header_tx_dst_rdy_n,
         TX_DATA        => hw_header_tx_data,
         TX_REM         => hw_header_tx_rem,
         TX_SOP_N       => hw_header_tx_sop_n,
         TX_EOP_N       => hw_header_tx_eop_n
      );

end architecture full;
