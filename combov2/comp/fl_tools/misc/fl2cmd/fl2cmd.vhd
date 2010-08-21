-- FL2CMD.vhd: Implementation of FrameLink to Command protocol conversion
-- component.
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
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
-- KNOWN ISSUES:
--    *) Component cannot handle few sequences mentioned in documentation.
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

use work.commands.all;

-- ------------------------------------------------------------------------
--                      Architecture declaration
-- ------------------------------------------------------------------------
architecture full of FL2CMD is

   type fsm_states is (
      s_ready, s_fifo_read, s_term
   );

   constant ALL_BYTES   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0)
      := conv_std_logic_vector(16#ff#, log2(DATA_WIDTH/8));

   signal curr_state, next_state : fsm_states;

   signal sig_dst_rdy_n : std_logic;
   signal sig_dst_rdy   : std_logic;
   signal sig_src_rdy_n : std_logic;
   signal sig_src_rdy   : std_logic;

   signal fifo_di       : std_logic_vector(1+log2(DATA_WIDTH/8)+DATA_WIDTH-1 downto 0);
   signal fifo_wr       : std_logic;
   signal fifo_do       : std_logic_vector(1+log2(DATA_WIDTH/8)+DATA_WIDTH-1 downto 0);
   signal fifo_rd       : std_logic;

   signal idle          : std_logic;
   signal done          : std_logic;
   signal sig_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal sig_term      : std_logic;
   signal sig_block     : std_logic;
   signal far_block     : std_logic;
   signal reg_block     : std_logic;
   signal flag_hdr      : std_logic;
   signal flag_pld      : std_logic;
   signal flag_ftr      : std_logic;
   signal flag_hdr_term : std_logic;
   signal flag_pld_term : std_logic;
   signal flag_ftr_term : std_logic;
   signal flag_eof      : std_logic;

   signal sohdr         : std_logic;
   signal eohdr         : std_logic;
   signal sopld         : std_logic;
   signal eopld         : std_logic;
   signal softr         : std_logic;
   signal eoftr         : std_logic;

begin 

   idle  <= '0'
      when (sohdr = '1') or (sopld = '1') or (softr = '1')
         or (flag_hdr = '1') or (flag_pld = '1') or (flag_ftr = '1')
      else '1';

   sig_term <= fifo_do(1+log2(DATA_WIDTH/8)+DATA_WIDTH-1);
   sig_rem  <= fifo_do(log2(DATA_WIDTH/8)+DATA_WIDTH-1 downto DATA_WIDTH);

   sig_dst_rdy_n  <= not CMD_DST_RDY;
   sig_dst_rdy    <= not sig_dst_rdy_n and not sig_block and not reg_block;
   sig_src_rdy_n  <= FL_SRC_RDY_N;
   sig_src_rdy    <= ((not sig_src_rdy_n) or flag_eof) and not done;

   -- output signals
   FL_DST_RDY_N   <= not sig_dst_rdy;
   CMD_SRC_RDY    <= sig_src_rdy;

   -- FIFO feeding
   fifo_di  <= not FL_EOP_N & FL_REM & FL_DATA;
   fifo_wr  <= '1'
      when (sig_dst_rdy = '1') and (sig_src_rdy_n = '0')
      else '0';

   -- ---------------------------------------------------------------------
   --                   Main logic
   -- ---------------------------------------------------------------------

   -- FSM
   sync_logic : process(RESET, CLK)
   begin
      if (RESET = '1') then
         curr_state <= s_ready;
      elsif (CLK'event AND CLK = '1') then
         curr_state <= next_state;
      end if;
   end process sync_logic;

   next_state_logic : process(curr_state, idle, sig_rem, sig_term,
      sig_dst_rdy_n, sig_src_rdy)
   begin
      next_state <= curr_state;
      case (curr_state) is

         when s_ready =>
            if (idle = '0' and sig_dst_rdy_n = '0' and sig_src_rdy = '1') then
               next_state <= s_fifo_read;
            end if;

         when s_fifo_read =>
            if (sig_term = '1' and sig_dst_rdy_n = '0' and sig_src_rdy = '1') then
               if (sig_rem = ALL_BYTES) then
                  -- all bytes valid
                  next_state <= s_term;
               else
                  -- term inside last frame
                  next_state <= s_ready;
               end if;
            end if;

         when s_term =>
            if (sig_dst_rdy_n = '0' and sig_src_rdy = '1') then
               next_state <= s_ready;
            end if;

         when others => null;
      end case;
   end process next_state_logic;

   GEN_LANE_OUTPUT: for i in (DATA_WIDTH/8)-1 downto 0 generate
   process(curr_state, idle, flag_hdr, flag_pld, flag_ftr, sig_term,
      sig_rem, fifo_do, sohdr, sopld, softr, sig_dst_rdy_n, sig_src_rdy)
   begin
      CMD_DATA(7+8*i downto 0+8*i) <= C_CMD_IDLE;
      CMD_COMMAND(i) <= '1';
      fifo_rd        <= '0';
      flag_hdr_term  <= '0';
      flag_pld_term  <= '0';
      flag_ftr_term  <= '0';
      sig_block      <= '0';
      far_block      <= '0';
      done           <= '0';
      case (curr_state) is

         when s_ready =>
            if ((idle = '0') and (i = 0)) then
               if ((flag_hdr = '1') or (sohdr = '1')) then
                  CMD_DATA(7+8*i downto 0+8*i) <= C_CMD_SOC;
               elsif ((flag_pld = '1') or (sopld = '1')) then
                  CMD_DATA(7+8*i downto 0+8*i) <= C_CMD_SOP;
               elsif ((flag_ftr = '1') or (softr = '1')) then
                  CMD_DATA(7+8*i downto 0+8*i) <= C_CMD_SOC;
               end if;
            end if;
            if (idle = '1') then
               done <= '1';
            end if;

         when s_fifo_read =>
            if (sig_term = '0') then
               -- only data
               CMD_COMMAND(i) <= '0';
               CMD_DATA(7+8*i downto 0+8*i) <= fifo_do(7+8*i downto 0+8*i);
            else
               if (flag_ftr = '1') then
                  flag_ftr_term <= '1';
               elsif (flag_pld = '1') then
                  flag_pld_term <= '1';
               elsif (flag_hdr = '1') then
                  flag_hdr_term <= '1';
               end if;
               if (sig_rem = ALL_BYTES) then
                  -- all bytes valid - term in next frame - data in all alnes
                  CMD_COMMAND(i) <= '0';
                  CMD_DATA(7+8*i downto 0+8*i) <= fifo_do(7+8*i downto 0+8*i);
               else
                  -- term in frame with data
                  far_block <= '1';
                  if (conv_std_logic_vector(i, log2(DATA_WIDTH/8)) = sig_rem+1) then
                     -- term in actual lane
                     CMD_COMMAND(i) <= '1';
                     CMD_DATA(7+8*i downto 0+8*i) <= C_CMD_TERM;
                  elsif (conv_std_logic_vector(i, log2(DATA_WIDTH/8)) < sig_rem+1) then
                     -- data in actual lane
                     CMD_COMMAND(i) <= '0';
                     CMD_DATA(7+8*i downto 0+8*i) <= fifo_do(7+8*i downto 0+8*i);
                  elsif (conv_std_logic_vector(i, log2(DATA_WIDTH/8)) > sig_rem+1) then
                     -- idle in actual lane
                     -- do nothing, idle is a default value
                  end if;
               end if;
            end if;
            if (sig_dst_rdy_n = '0' and sig_src_rdy = '1') then
               fifo_rd <= '1';
            end if;

         when s_term =>
            sig_block <= '1';
            if (i = 0) then
               CMD_DATA(7+8*i downto 0+8*i) <= C_CMD_TERM;
            end if;

         when others => null;
      end case;
   end process;
   end generate;

   -- ---------------------------------------------------------------------
   --                   Registers
   -- ---------------------------------------------------------------------

   flag_hdrp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         flag_hdr <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (sohdr = '1') then
            flag_hdr <= '1';
         elsif (flag_hdr_term = '1') then
            flag_hdr <= '0';
         end if;
      end if;
   end process;

   flag_pldp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         flag_pld <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (sopld = '1') then
            flag_pld <= '1';
         elsif (flag_pld_term = '1') then
            flag_pld <= '0';
         end if;
      end if;
   end process;

   flag_ftrp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         flag_ftr <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (softr = '1') then
            flag_ftr <= '1';
         elsif (flag_ftr_term = '1') then
            flag_ftr <= '0';
         end if;
      end if;
   end process;

   reg_blockp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_block <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_block <= sig_block or far_block;
      end if;
   end process;

   flag_eofp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         flag_eof <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (FL_EOF_N = '0') then
            flag_eof <= '1';
         elsif (FL_SOF_N = '0') then
            flag_eof <= '0';
         end if;
      end if;
   end process;

   -- ---------------------------------------------------------------------
   --                   Components
   -- ---------------------------------------------------------------------

   FL_DEC_U: entity work.FL_DEC
      generic map(
         HEADER      => HEADER,
         FOOTER      => FOOTER
      )
      port map(
         CLK         => CLK,
         RESET       => RESET,
         -- input signals: FrameLink interface
         SOF_N       => FL_SOF_N,
         SOP_N       => FL_SOP_N,
         EOP_N       => FL_EOP_N,
         EOF_N       => FL_EOF_N,
         SRC_RDY_N   => FL_SRC_RDY_N,
         DST_RDY_N   => open,
         -- output signa-- outputls
         SOF         => open,
         SOHDR       => sohdr,
         EOHDR       => eohdr,
         HDR_FRAME   => open,
         SOPLD       => sopld,
         EOPLD       => eopld,
         PLD_FRAME   => open,
         SOFTR       => softr,
         EOFTR       => eoftr,
         FTR_FRAME   => open,
         EOF         => open,
         SRC_RDY     => open,
         DST_RDY     => sig_dst_rdy
      );

   DATA_FIFO_U: entity work.FIFO
      generic map(
         -- term indicator + FL_REM + FL_DATA 
         DATA_WIDTH     => 1+log2(DATA_WIDTH/8)+DATA_WIDTH,
         DISTMEM_TYPE   => 64,
         ITEMS          => 4
      )
      port map(
         RESET     => RESET,
         CLK       => CLK,
         --
         DATA_IN   => fifo_di,
         WRITE_REQ => fifo_wr,
         FULL      => open,
         LSTBLK    => open,
         --
         DATA_OUT  => fifo_do,
         READ_REQ  => fifo_rd,
         EMPTY     => open
      );

end architecture full;
