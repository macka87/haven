-- fls_cu.vhd: FrameLink Splitter Control Unit
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FLS_CU is
   generic(
      DATA_WIDTH     : integer;
      OUTPUT_COUNT   : integer;
      STATUS_WIDTH   : integer
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interface
      SOF_IN_N       : in  std_logic;
      SOP_IN_N       : in  std_logic;
      EOP_IN_N       : in  std_logic;
      EOF_IN_N       : in  std_logic;
      SRC_RDY_IN_N   : in  std_logic;
      DST_RDY_IN_N   : out std_logic;
      DATA_IN        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      REM_IN         : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      
      -- FIFO interface
      SOF_OUT_N      : out std_logic;
      SOP_OUT_N      : out std_logic;
      EOP_OUT_N      : out std_logic;
      EOF_OUT_N      : out std_logic;
      SRC_RDY_OUT_N  : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      DST_RDY_OUT_N  : in  std_logic_vector(OUTPUT_COUNT-1 downto 0);
      DATA_OUT       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      REM_OUT        : out std_logic_vector(log2(DATA_WIDTH/8)-1 
                                                                     downto 0);
      FIFO_STATUS    : in  std_logic_vector((OUTPUT_COUNT*STATUS_WIDTH)-1 
                                                                     downto 0)
   );
end entity FLS_CU;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FLS_CU is
   
   -- ------------------ Component declaration --------------------------------
   component FLS_MAX_SELECT is
      generic(
         DATA_WIDTH     : integer;
         VECTOR_COUNT   : integer
      );
      port(
         -- input vectors
         DI             : in  std_logic_vector((VECTOR_COUNT*DATA_WIDTH)-1 
                                                                  downto 0);
         -- max bus ('1' -> this vector is the greatest)
         MAX            : out std_logic_vector(VECTOR_COUNT-1 downto 0)
      );
   end component FLS_MAX_SELECT;

   component FLS_CU_FSM is
      port(
         CLK            : in std_logic;
         RESET          : in std_logic;
   
         -- input signals
         EOF            : in  std_logic;
         QUEUE_RDY      : in  std_logic;
   
         -- output signals
         SET_VALID      : out std_logic;
         CLR_VALID      : out std_logic;
         CLR_READY      : out std_logic;
         NEXT_QUEUE     : out std_logic
      );
   end component FLS_CU_FSM;
   
   -- ------------------ Signals declaration ----------------------------------
   -- FSM signals
   signal fsm_eof             : std_logic;
   signal fsm_queue_rdy       : std_logic;
   signal fsm_set_valid       : std_logic;
   signal fsm_clr_valid       : std_logic;
   signal fsm_clr_ready       : std_logic;
   signal fsm_next_queue      : std_logic;

   -- (de)multiplexers
   signal mx_dst_rdy_in_n     : std_logic;
   signal mx_max              : std_logic;
   signal dmx_src_rdy_in_n_i  : std_logic;
   signal dmx_src_rdy_in_n    : std_logic_vector(OUTPUT_COUNT-1 downto 0);

   -- registers
   signal reg_addr           : std_logic_vector(log2(OUTPUT_COUNT)-1 downto 0);
   signal reg_addr_we        : std_logic;
   signal reg_next           : std_logic_vector(log2(OUTPUT_COUNT)-1 downto 0);
   signal reg_max_bus        : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal reg_valid          : std_logic;
   signal reg_valid_we       : std_logic;
   signal reg_valid_clr      : std_logic;
   signal reg_ready          : std_logic;
   signal reg_ready_we       : std_logic;
   signal reg_ready_clr      : std_logic;

   -- other
   signal max_bus            : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal dv                 : std_logic;

begin
   -- ------------------ Directly mapped signals ------------------------------
   dmx_src_rdy_in_n_i <= (not reg_valid) or SRC_RDY_IN_N;
   dv                <= (not SRC_RDY_IN_N) and (not mx_dst_rdy_in_n);
   
   -- FSM input signals
   fsm_eof           <= dv and (not EOF_IN_N);
   fsm_queue_rdy     <= reg_ready;
   
   -- interface output signals
   DST_RDY_IN_N      <= (not reg_valid) or mx_dst_rdy_in_n;
   
   SOF_OUT_N         <= SOF_IN_N;
   SOP_OUT_N         <= SOP_IN_N;
   EOP_OUT_N         <= EOP_IN_N;
   EOF_OUT_N         <= EOF_IN_N;
   SRC_RDY_OUT_N     <= dmx_src_rdy_in_n;
   DATA_OUT          <= DATA_IN;
   REM_OUT           <= REM_IN;
   
   -- register control signals
   reg_addr_we       <= fsm_next_queue;
   reg_valid_we      <= fsm_set_valid;
   reg_valid_clr     <= fsm_clr_valid;
   reg_ready_clr     <= fsm_clr_ready;
   reg_ready_we      <= mx_max;

   -- FSM mapping
   FLS_CU_FSM_I : FLS_CU_FSM
      port map(
         CLK            => CLK,
         RESET          => RESET,
   
         -- input signals
         EOF            => fsm_eof,
         QUEUE_RDY      => fsm_queue_rdy,
   
         -- output signals
         SET_VALID      => fsm_set_valid,
         CLR_VALID      => fsm_clr_valid,
         CLR_READY      => fsm_clr_ready,
         NEXT_QUEUE     => fsm_next_queue
      );

   -- MAX_SELECTION mapping
   FLS_MAX_SELECT_I : FLS_MAX_SELECT
      generic map(
         DATA_WIDTH     => STATUS_WIDTH,
         VECTOR_COUNT   => OUTPUT_COUNT
      )
      port map(
         DI             => FIFO_STATUS,
         MAX            => max_bus
      );
   
   -- mx_max and reg_next priority encoder
   mx_maxp: process(reg_max_bus)
   begin
     mx_max   <= reg_max_bus(0);
     reg_next <= (others => '0');
     for i in 0 to OUTPUT_COUNT-1 loop
       if (reg_max_bus(i) = '1') then
         mx_max   <= reg_max_bus(i);
         reg_next <= conv_std_logic_vector(i, reg_next'length);
       end if;
     end loop;
   end process;

   -- mx_dst_rdy_in_n multiplexer
   mx_dst_rdy_in_np: process(reg_addr, DST_RDY_OUT_N)
   begin
      mx_dst_rdy_in_n <= DST_RDY_OUT_N(0);
      for i in 0 to OUTPUT_COUNT-1 loop
         if(conv_std_logic_vector(i, log2(OUTPUT_COUNT)) = reg_addr) then
            mx_dst_rdy_in_n <= DST_RDY_OUT_N(i);
         end if;
      end loop;
   end process;
   
   -- dmx_src_rdy_in_n demultiplexer
   dmx_src_rdy_in_np: process(reg_addr, dmx_src_rdy_in_n_i)
   begin
      dmx_src_rdy_in_n <= (others => '1');
      for i in 0 to OUTPUT_COUNT-1 loop
         if(conv_std_logic_vector(i, log2(OUTPUT_COUNT)) = reg_addr) then
            dmx_src_rdy_in_n(i) <= dmx_src_rdy_in_n_i;
         end if;
      end loop;
   end process;

   -- register reg_addr -------------------------------------------------------
   reg_addrp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (reg_addr_we = '1') then
            reg_addr <= reg_next;
         end if;
      end if;
   end process;

   -- register reg_valid ------------------------------------------------------
   reg_validp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1' or reg_valid_clr = '1') then
            reg_valid <= '0';
         elsif (reg_valid_we = '1') then
            reg_valid <= fsm_set_valid;
         end if;
      end if;
   end process;

   -- register reg_ready ------------------------------------------------------
   reg_readyp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1' or reg_ready_clr = '1') then
            reg_ready <= '0';
         elsif (reg_ready_we = '1') then
            reg_ready <= mx_max;
         end if;
      end if;
   end process;

   -- register reg_max_bus ----------------------------------------------------
   reg_max_busp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg_max_bus <= max_bus;
      end if;
   end process;

end architecture full;
