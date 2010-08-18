--
-- bm_converter.vhd: BM Converter
-- Copyright (C) 2008 CESNET
-- Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--                          ARCHITECTURE DECLARATION                         --
-- ----------------------------------------------------------------------------

architecture bm_converter_arch of BM_CONVERTER is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   constant REGS        : integer := 128/DATA_WIDTH;
   
   type t_data    is array(0 to REGS-1) of std_logic_vector(DATA_WIDTH-1 downto 0);
   type t_data_mx is array(0 to REGS-2) of std_logic_vector(DATA_WIDTH-1 downto 0);
   type fsm_states is (IDLE,BM);
   
   signal data          : std_logic_vector(127 downto 0);
   signal data_reg      : t_data;
   signal data_reg_en   : std_logic;
   signal data_mx       : t_data_mx;
   signal data_mx_sel   : std_logic;
   signal present_state : fsm_states;
   signal next_state    : fsm_states;
   signal cnt           : std_logic_vector(log2(REGS)-1 downto 0);
   signal cnt_en        : std_logic;
   signal cnt_zeros     : std_logic_vector(log2(REGS)-1 downto 0);
   signal cnt_ones      : std_logic_vector(log2(REGS)-1 downto 0);
   signal src_rdy_n     : std_logic;
   
begin

   -- Asserts -----------------------------------------------------------------
   assert DATA_WIDTH =  8 or DATA_WIDTH = 16 or DATA_WIDTH = 32 or
          DATA_WIDTH = 64 or DATA_WIDTH = 128
      report "DATA_WIDTH must be one of {8,16,32,64,128}."
      severity error;
   
   -- -------------------------------------------------------------------------
   --                              BM Converter                              --
   -- -------------------------------------------------------------------------
   
   -- line all data up in correct order
   data <= BM_GLOBAL_ADDR(63 downto 32) &
           BM_LOCAL_ADDR &
           BM_GLOBAL_ADDR(31 downto 0) &
           X"00" & BM_TAG & BM_LENGTH &
           "00" & not BM_TRANS_TYPE(1) & BM_TRANS_TYPE(0);

   -- -------------------------- DATA_WIDTH = 128 -----------------------------   

   DATA_WIDTH_128: if (DATA_WIDTH = 128) generate
   
      IB_DATA      <= data;
      
      IB_SOF_N     <= not BM_REQ;
      IB_EOF_N     <= not BM_REQ;
      IB_SRC_RDY_N <= not BM_REQ;
      
      BM_ACK       <= BM_REQ and not IB_DST_RDY_N;
      
   end generate;
   
   -- -------------------------- DATA_WIDTH < 128 -----------------------------
   
   DATA_WIDTH_NOT_128: if (DATA_WIDTH < 128) generate
      
      -- generate all registers except the last one
      GEN_REGISTERS: for i in 0 to REGS-2 generate
         
         data_mx(i) <= data((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH)
                       when (data_mx_sel = '1') else data_reg(i+1);
         
         process(RESET, CLK)
         begin
            if (CLK'event AND CLK = '1') then
               if (data_reg_en = '1') then
                  data_reg(i) <= data_mx(i);
               end if;
            end if;
         end process;
         
      end generate;
      
      -- last register (without multiplexor)
      process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (data_reg_en = '1') then
               data_reg(REGS-1) <= data(REGS*DATA_WIDTH-1 downto (REGS-1)*DATA_WIDTH);
            end if;
         end if;
      end process;
      
      
      -- ------------------------------- FSM ----------------------------------
      
      -- synchronize logic ----------------------------------------------------
      synchlogp : process(RESET, CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               present_state <= IDLE;
            else
               present_state <= next_state;
            end if;
         end if;
      end process;
      
      -- next state logic -----------------------------------------------------
      nextstatelogicp : process(present_state,cnt,IB_DST_RDY_N,BM_REQ)
      begin
         next_state <= present_state;
         
         case (present_state) is
            
            when IDLE =>
               if (BM_REQ = '1') then
                  next_state <= BM;
               end if;
            
            when BM =>
               if (cnt = cnt_ones) and (IB_DST_RDY_N = '0') then
                  next_state <= IDLE;
               end if;
            
         end case;
      end process;

      -- output logic ---------------------------------------------------------
      outputlogicp : process(present_state,IB_DST_RDY_N,BM_REQ,cnt)
      begin
         
         case (present_state) is
            
            when IDLE =>
               data_mx_sel   <= '1';
               data_reg_en   <= '1';
               cnt_en        <= '0';
               src_rdy_n     <= '1';
               BM_ACK        <= BM_REQ;
            
            when BM =>
               cnt_en        <= not IB_DST_RDY_N;
               src_rdy_n     <= '0';
               data_reg_en   <= not IB_DST_RDY_N;
               data_mx_sel   <= '0';
               BM_ACK        <= '0';
           
         end case;
      end process;
      
      
      -- ----------------------------- Counter --------------------------------
      
      cntp: process (RESET, CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then 
               cnt <= (others => '0');
            elsif (cnt_en = '1') then
               cnt <= cnt + 1;
            end if;
         end if;
      end process;
      
      -- ----------------------------------------------------------------------
      
      cnt_zeros <= (others => '0');
      cnt_ones  <= (others => '1');
      
      IB_SRC_RDY_N  <= src_rdy_n;
      IB_DATA       <= data_reg(0);
      
      BM_OP_TAG     <= IB_TAG;
      BM_OP_DONE    <= IB_TAG_VLD;
      
      sof_eof_muxp: process (cnt, cnt_zeros, cnt_ones, src_rdy_n)
      begin
         IB_SOF_N <= '1';
         IB_EOF_N <= '1';
         if ((cnt=cnt_zeros) and (src_rdy_n='0')) then
            IB_SOF_N <= '0';
         end if;
         if ((cnt=cnt_ones) and (src_rdy_n='0')) then
            IB_EOF_N <= '0';
         end if;
      end process;
      
   end generate;
   
   -- -------------------------------------------------------------------------
   
end bm_converter_arch;



