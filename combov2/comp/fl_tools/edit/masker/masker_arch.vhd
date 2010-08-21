-- masker_arch.vhd: Frame Link component to mask bits
-- Copyright (C) 2006 CESNET
-- Author(s): Radim Janalik <radim.janalik@gmail.com>
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

use work.math_pack.all;

architecture full of FL_MASKER is

   signal reg_mask               : std_logic_vector(NUMBER_OF_WORDS*FL_WIDTH-1 downto 0);
   signal wr_req                 : std_logic;
   signal wr_ack                 : std_logic;
   signal cnt                    : std_logic_vector(log2(NUMBER_OF_WORDS)-1 downto 0);

   signal rxpipe_rx_sof_n        : std_logic;
   signal rxpipe_rx_sop_n        : std_logic;
   signal rxpipe_rx_eop_n        : std_logic;
   signal rxpipe_rx_eof_n        : std_logic;
   signal rxpipe_rx_src_rdy_n    : std_logic;
   signal rxpipe_rx_dst_rdy_n    : std_logic;
   signal rxpipe_rx_data         : std_logic_vector(FL_WIDTH-1 downto 0);
   signal rxpipe_rx_rem          : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);

   signal rxpipe_tx_sof_n        : std_logic;
   signal rxpipe_tx_eop_n        : std_logic;
   signal rxpipe_tx_sop_n        : std_logic;
   signal rxpipe_tx_eof_n        : std_logic;
   signal rxpipe_tx_src_rdy_n    : std_logic;
   signal rxpipe_tx_dst_rdy_n    : std_logic;
   signal rxpipe_tx_data         : std_logic_vector(FL_WIDTH-1 downto 0);
   signal rxpipe_tx_rem          : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);

   signal txpipe_rx_sof_n        : std_logic;
   signal txpipe_rx_sop_n        : std_logic;
   signal txpipe_rx_eop_n        : std_logic;
   signal txpipe_rx_eof_n        : std_logic;
   signal txpipe_rx_src_rdy_n    : std_logic;
   signal txpipe_rx_dst_rdy_n    : std_logic;
   signal txpipe_rx_data         : std_logic_vector(FL_WIDTH-1 downto 0);
   signal txpipe_rx_rem          : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);

   signal txpipe_tx_sof_n        : std_logic;
   signal txpipe_tx_eop_n        : std_logic;
   signal txpipe_tx_sop_n        : std_logic;
   signal txpipe_tx_eof_n        : std_logic;
   signal txpipe_tx_src_rdy_n    : std_logic;
   signal txpipe_tx_dst_rdy_n    : std_logic;
   signal txpipe_tx_data         : std_logic_vector(FL_WIDTH-1 downto 0);
   signal txpipe_tx_rem          : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);

   signal addr                   : std_logic_vector(31 downto 0);
   signal mx_read                : std_logic_vector(31 downto 0);
   signal dwr                    : std_logic_vector(31 downto 0);
   signal wr                     : std_logic;
   signal we_req                 : std_logic;
   signal we_mask                : std_logic_vector((NUMBER_OF_WORDS*FL_WIDTH-1)/32 downto 0);

begin

   -- --------------------------------------------------------------------------
   -- RX PIPE
   -- --------------------------------------------------------------------------

   rxpipe_rx_sof_n      <= RX_SOF_N;
   rxpipe_rx_sop_n      <= RX_SOP_N;
   rxpipe_rx_eop_n      <= RX_EOP_N;
   rxpipe_rx_eof_n      <= RX_EOF_N;
   rxpipe_rx_src_rdy_n  <= RX_SRC_RDY_N;
   RX_DST_RDY_N         <= rxpipe_rx_dst_rdy_n;
   rxpipe_rx_data       <= RX_DATA;
   rxpipe_rx_rem        <= RX_REM;

   rx_pipe_gen : if RX_PIPE = true generate
      rx_pipe : entity work.fl_pipe
      generic map(
         DATA_WIDTH     => FL_WIDTH,
         USE_OUTREG     => true
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
 
         RX_SOF_N       => rxpipe_rx_sof_n,
         RX_SOP_N       => rxpipe_rx_sop_n,
         RX_EOP_N       => rxpipe_rx_eop_n,
         RX_EOF_N       => rxpipe_rx_eof_n,
         RX_SRC_RDY_N   => rxpipe_rx_src_rdy_n,
         RX_DST_RDY_N   => rxpipe_rx_dst_rdy_n,
         RX_DATA        => rxpipe_rx_data,
         RX_REM         => rxpipe_rx_rem,
 
         TX_SOF_N       => rxpipe_tx_sof_n,
         TX_EOP_N       => rxpipe_tx_eop_n,
         TX_SOP_N       => rxpipe_tx_sop_n,
         TX_EOF_N       => rxpipe_tx_eof_n,
         TX_SRC_RDY_N   => rxpipe_tx_src_rdy_n,
         TX_DST_RDY_N   => rxpipe_tx_dst_rdy_n,
         TX_DATA        => rxpipe_tx_data,
         TX_REM         => rxpipe_tx_rem
      );
   end generate;

   rx_pipe_not_gen : if RX_PIPE = false generate
      rxpipe_tx_sof_n     <= rxpipe_rx_sof_n;
      rxpipe_tx_sop_n     <= rxpipe_rx_sop_n;
      rxpipe_tx_eop_n     <= rxpipe_rx_eop_n;
      rxpipe_tx_eof_n     <= rxpipe_rx_eof_n;
      rxpipe_tx_data      <= rxpipe_rx_data;
      rxpipe_tx_rem       <= rxpipe_rx_rem;
      rxpipe_tx_src_rdy_n <= rxpipe_rx_src_rdy_n;
      rxpipe_rx_dst_rdy_n <= rxpipe_tx_dst_rdy_n;
   end generate;


   -- --------------------------------------------------------------------------
   -- TX PIPE
   -- --------------------------------------------------------------------------

   TX_SOF_N             <= txpipe_tx_sof_n;
   TX_SOP_N             <= txpipe_tx_sop_n;
   TX_EOP_N             <= txpipe_tx_eop_n;
   TX_EOF_N             <= txpipe_tx_eof_n;
   TX_SRC_RDY_N         <= txpipe_tx_src_rdy_n;
   txpipe_tx_dst_rdy_n  <= TX_DST_RDY_N;
   TX_DATA              <= txpipe_tx_data;
   TX_REM               <= txpipe_tx_rem;

   tx_pipe_gen : if TX_PIPE = true generate
      tx_pipe : entity work.fl_pipe
      generic map(
         DATA_WIDTH     => FL_WIDTH,
         USE_OUTREG     => true
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
 
         RX_SOF_N       => txpipe_rx_sof_n,
         RX_SOP_N       => txpipe_rx_sop_n,
         RX_EOP_N       => txpipe_rx_eop_n,
         RX_EOF_N       => txpipe_rx_eof_n,
         RX_SRC_RDY_N   => txpipe_rx_src_rdy_n,
         RX_DST_RDY_N   => txpipe_rx_dst_rdy_n,
         RX_DATA        => txpipe_rx_data,
         RX_REM         => txpipe_rx_rem,
 
         TX_SOF_N       => txpipe_tx_sof_n,
         TX_EOP_N       => txpipe_tx_eop_n,
         TX_SOP_N       => txpipe_tx_sop_n,
         TX_EOF_N       => txpipe_tx_eof_n,
         TX_SRC_RDY_N   => txpipe_tx_src_rdy_n,
         TX_DST_RDY_N   => txpipe_tx_dst_rdy_n,
         TX_DATA        => txpipe_tx_data,
         TX_REM         => txpipe_tx_rem
      );
   end generate;

   tx_pipe_not_gen : if TX_PIPE = false generate
      txpipe_tx_sof_n     <= txpipe_rx_sof_n;
      txpipe_tx_sop_n     <= txpipe_rx_sop_n;
      txpipe_tx_eop_n     <= txpipe_rx_eop_n;
      txpipe_tx_eof_n     <= txpipe_rx_eof_n;
      txpipe_tx_data      <= txpipe_rx_data;
      txpipe_tx_rem       <= txpipe_rx_rem;
      txpipe_tx_src_rdy_n <= txpipe_rx_src_rdy_n;
      txpipe_rx_dst_rdy_n <= txpipe_tx_dst_rdy_n;
   end generate;

   -- --------------------------------------------------------------------------
   -- Internals
   -- --------------------------------------------------------------------------

   fl_masker_fsm : entity work.fl_masker_fsm
   port map (
      CLK           => CLK,
      RESET         => RESET,

      RX_SRC_RDY_N  => rxpipe_tx_src_rdy_n,
      TX_DST_RDY_N  => txpipe_rx_dst_rdy_n,
      RX_EOF_N      => rxpipe_tx_eof_n,
      RX_SOF_N      => rxpipe_tx_sof_n,
      WR_REQ        => wr_req,

      WR_ACK        => wr_ack
   );

   MI32_ARDY <= MI32_RD or MI32_WR;

   txpipe_rx_sof_n      <= rxpipe_tx_sof_n;
   txpipe_rx_sop_n      <= rxpipe_tx_sop_n;
   txpipe_rx_eop_n      <= rxpipe_tx_eop_n;
   txpipe_rx_eof_n      <= rxpipe_tx_eof_n;
   txpipe_rx_src_rdy_n  <= rxpipe_tx_src_rdy_n or wr_ack;
   rxpipe_tx_dst_rdy_n  <= txpipe_rx_dst_rdy_n or wr_ack;
   txpipe_rx_rem        <= rxpipe_tx_rem;

   mask_gen : for i in 0 to FL_WIDTH-1 generate
      txpipe_rx_data(i) <= rxpipe_tx_data(i) and reg_mask(conv_integer(cnt)*FL_WIDTH + i);
   end generate;

   cnt_proc : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            cnt <= (others => '0');
         else
            if rxpipe_tx_src_rdy_n = '0' and txpipe_rx_dst_rdy_n = '0' and wr_ack = '0' then
               if rxpipe_tx_eof_n = '0' then
                  cnt <= (others => '0');
               else
                  cnt <= cnt + 1;
               end if;
            end if;
         end if;
      end if;
   end process;

   addr <= MI32_ADDR;
   MI32_DRD <= mx_read;
   wr <= MI32_WR;
   dwr <= MI32_DWR;

   mi32_we_req_proc : process(wr, addr)
   begin
      if wr = '1' and addr = 0 then
         we_req <= '1';
      else
         we_req <= '0';
      end if;
   end process;

   mi32_we_mask_gen : for i in 0 to (NUMBER_OF_WORDS*FL_WIDTH-1)/32 generate
   begin
      mi32_we_mask_proc : process(wr, addr)
      begin
         if wr = '1' and conv_integer(addr) = 4*(i+1) then
            we_mask(i) <= '1';
         else
            we_mask(i) <= '0';
         end if;
      end process;
   end generate;

   mi32_write_req_proc : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            wr_req <= '0';
         else
            if we_req = '1' then
               wr_req <= dwr(1);
            end if;
         end if;
      end if;
   end process;

   mi32_write_mask_gen : for i in 0 to (NUMBER_OF_WORDS*FL_WIDTH-1)/32-1 generate
   begin
      mi32_write_mask_proc : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            if RESET = '1' then
               reg_mask(32*(i+1)-1 downto 32*i) <= RESET_VALUE(32*(i+1)-1 downto 32*i);
            else
               if we_mask(i) = '1' then
                  reg_mask(32*(i+1)-1 downto 32*i) <= dwr;
               end if;
            end if;
         end if;
      end process;
   end generate;

   mi32_write_mask_last_proc : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_mask(NUMBER_OF_WORDS*FL_WIDTH-1 downto
               ((NUMBER_OF_WORDS*FL_WIDTH-1)/32)*32) <= RESET_VALUE(
               NUMBER_OF_WORDS*FL_WIDTH-1 downto ((NUMBER_OF_WORDS*FL_WIDTH-1)/32)*32);
         else
            if we_mask((NUMBER_OF_WORDS*FL_WIDTH-1)/32) = '1' then
               reg_mask(NUMBER_OF_WORDS*FL_WIDTH-1 downto
                  ((NUMBER_OF_WORDS*FL_WIDTH-1)/32)*32) <= dwr;
            end if;
         end if;
      end if;
   end process;

   mi32_read_proc : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         mx_read <= (others => '0');
         case conv_integer(addr) is
            when 0 => mx_read(1 downto 0) <= wr_req & wr_ack;
            when others =>
               mx_read <= reg_mask(8*conv_integer(addr)-1 downto 8*(conv_integer(addr)-4));
         end case;
      end if;
   end process;

   MI32_DRDY <= MI32_RD;

end architecture full;
