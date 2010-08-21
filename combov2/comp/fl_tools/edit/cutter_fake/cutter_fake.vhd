-- cutter_fake.vhd: FrameLink cutter one-purpose (fake) architecture.
-- Copyright (C) 2007 CESNET
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.numeric_std.all;

-- Math package - log2 function
use work.math_pack.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity fl_cutter_fake is
   generic(
      DATA_WIDTH  : integer := 128; -- FrameLink width
      PART        : integer := 1;   -- Number of modified part, 0 = first part
      OFFSET      : integer := 0;   -- Position from SOP, 0 = first byte
      SIZE        : integer := 2    -- Removed block size, greater than 0
   );
   port(
      CLK         : in std_logic;
      RESET       : in std_logic;

      -- Cutted data
      CUTTED_DATA : out std_logic_vector(SIZE*8 - 1 downto 0);
      CUTTED_VLD  : out std_logic; -- cutted data is valid (one cycle)

      -- Write interface
      RX_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM      : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SRC_RDY_N : in  std_logic;
      RX_DST_RDY_N : out std_logic;
      RX_SOP_N    : in  std_logic;
      RX_EOP_N    : in  std_logic;
      RX_SOF_N    : in  std_logic;
      RX_EOF_N    : in  std_logic;

      -- Read interface
      TX_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM      : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N : out std_logic;
      TX_DST_RDY_N : in  std_logic;
      TX_SOP_N    : out std_logic;
      TX_EOP_N    : out std_logic;
      TX_SOF_N    : out std_logic;
      TX_EOF_N    : out std_logic
   );
end entity fl_cutter_fake;

-- ------------------------------------------------------------------------
--                        Architecture declaration
-- ------------------------------------------------------------------------
architecture full of fl_cutter_fake is

   signal reg_data      : std_logic_vector(DATA_WIDTH-1 downto 0)
      := (others => '0');
   signal cnt_part      : std_logic_vector(2 downto 0) := "000";
   signal reg_part      : std_logic_vector(2 downto 0) := "000";
   signal cnt_word      : std_logic_vector(9 downto 0) := "0000000000";
   signal reg_src_rdy   : std_logic := '0';
   signal reg_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0)
      := (others => '0');
   signal reg_eop       : std_logic := '0';
   signal reg_eof       : std_logic := '0';
   signal reg_sop       : std_logic := '0';
   signal reg_sop2      : std_logic := '0';
   signal reg_sof       : std_logic := '0';
   signal sig_cut_vld   : std_logic := '0';
   signal reg_cut_vld   : std_logic := '0';
   signal reg_cut_data  : std_logic_vector(15 downto 0) := (others => '0');

-- ------------------------------------------------------------------------
--                        Architecture body
-- ------------------------------------------------------------------------
begin

   assert (DATA_WIDTH = 128) or (DATA_WIDTH = 16)
      report "FL_CUTTER_FAKE: Unsupported DATA_WIDTH generic."
      severity error;
   assert (PART = 1)
      report "FL_CUTTER_FAKE: Unsupported PART generic."
      severity error;
   assert (OFFSET = 0) or (OFFSET = 2)
      report "FL_CUTTER_FAKE: Unsupported OFFSET generic."
      severity error;
   assert (SIZE = 2)
      report "FL_CUTTER_FAKE: Unsupported SIZE generic."
      severity error;

   RX_DST_RDY_N <= TX_DST_RDY_N;

   -- ---------------------------------------------------------------------
   --                     Register pipeline
   -- ---------------------------------------------------------------------

   GEN_128_SRC_RDY: if (DATA_WIDTH = 128) generate

      reg_datap: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (TX_DST_RDY_N = '0' and RX_SRC_RDY_N = '0') then
               if (conv_integer(cnt_part) = 1) then
                  if (RX_SOP_N = '0') then
                     if (OFFSET = 0) then
                        reg_data(128-16-1 downto 0) <= RX_DATA(128-1 downto 16);
                     else
                        reg_data(15 downto 0) <= RX_DATA(15 downto 0);
                        reg_data(128-16-1 downto 16) <= RX_DATA(128-1 downto 32);
                     end if;
                  else
                     reg_data(128-16-1 downto 0) <= RX_DATA(128-1 downto 16);
                  end if;
               else
                  -- just copy to reg and then to output
                  reg_data <= RX_DATA;
               end if;
            end if;
         end if;
      end process;
 
      -- output data multiplexer
      out_datap: process(RX_DATA, RX_SRC_RDY_N, reg_data, TX_DST_RDY_N,
         cnt_part, RX_SOP_N)
      begin
         TX_DATA <= reg_data;
         if (TX_DST_RDY_N = '0' and RX_SRC_RDY_N = '0') then
            if (conv_integer(cnt_part) = 1) then
               if (RX_SOP_N = '1') then
                  TX_DATA(128-1 downto 128-16) <= RX_DATA(15 downto 0);
               end if;
            end if;
         end if;
      end process;
 
      reg_src_rdyp: process(CLK, RESET)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               reg_src_rdy <= '0';
            else
 
               if (TX_DST_RDY_N = '0') then
 
               if (conv_integer(cnt_part) = 1) then
                  if (RX_SOP_N = '0') then
                     if (RX_EOP_N = '0') then
                        reg_src_rdy <= not RX_SRC_RDY_N;
                     else
                        reg_src_rdy <= '0';
                     end if;
                  else
                     if (RX_EOP_N = '0' and conv_integer(RX_REM) < 2) then
                        reg_src_rdy <= '0';
                     else
                        reg_src_rdy <= not RX_SRC_RDY_N;
                     end if;
                  end if;
               else
                  reg_src_rdy <= not RX_SRC_RDY_N;
               end if;
 
               end if;
 
            end if;
         end if;
      end process;
 
      out_src_rdyp: process(reg_src_rdy, cnt_part, RX_EOP_N, RX_SRC_RDY_N,
         RX_REM, RX_SOP_N)
      begin
         TX_SRC_RDY_N <= not reg_src_rdy;
         if (conv_integer(cnt_part) = 1) then
            if (RX_SOP_N = '1') then
               if (reg_src_rdy = '1' and conv_integer(reg_part) = 0) then
                  TX_SRC_RDY_N <= '0';
               else
                  TX_SRC_RDY_N <= RX_SRC_RDY_N;
               end if;
            end if;
            if (RX_SRC_RDY_N = '0' and RX_EOP_N = '0') then
               if (conv_integer(RX_REM) < 2) then
                  TX_SRC_RDY_N <= '0';
               end if;
            end if;
         end if;
      end process;

   end generate;

   GEN_16_SRC_RDY: if (DATA_WIDTH = 16) generate

      TX_DATA        <= reg_data;
      TX_SRC_RDY_N   <= not reg_src_rdy;

      reg_datap: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0') then
               reg_data <= RX_DATA;
            end if;
         end if;
      end process;

      reg_src_rdyp: process(RESET, CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               reg_src_rdy <= '0';
            else
               if (TX_DST_RDY_N = '0') then
                  if (sig_cut_vld = '1') then
                     reg_src_rdy <= '0';
                  else
                     reg_src_rdy <= not RX_SRC_RDY_N;
                  end if;
               end if;
            end if;
         end if;
      end process;

   end generate;

   GEN_128_REM: if (DATA_WIDTH = 128) generate

      reg_remp: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0') then
               if (conv_integer(cnt_part) = 1) then
                  if (RX_EOP_N = '0') then
                     reg_rem <= RX_REM - 2;
                  else
                     reg_rem <= (others => '1');
                  end if;
               else
                  reg_rem <= RX_REM;
               end if;
            end if;
         end if;
      end process;
 
      -- TX_REM multiplexor
      out_remp: process(cnt_part, RX_EOP_N, RX_REM, reg_rem)
      begin
         if (conv_integer(cnt_part) = 1) then
            if (RX_EOP_N = '0') then
               if (conv_integer(RX_REM) < 2) then
                  TX_REM <= reg_rem - (1 - conv_integer(RX_REM));
               else
                  TX_REM <= reg_rem;
               end if;
            else
               TX_REM <= reg_rem;
            end if;
         else
            TX_REM <= reg_rem;
         end if;
      end process;

   end generate;

   GEN_16_REM: if (DATA_WIDTH = 16) generate

      remp: process(RESET, CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0') then
               reg_rem <= RX_REM;
            end if;
         end if;
      end process;

   TX_REM <= reg_rem;

   end generate;

   TX_SOF_N <= not reg_sof;
   TX_SOP_N <= not reg_sop;

   GEN_128_SOP: if ((DATA_WIDTH = 128) or (DATA_WIDTH = 16 and OFFSET = 2))
   generate


      reg_sopp: process(CLK, RESET)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               reg_sop <= '0';
               reg_sof <= '0';
            else
               if (RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0') then
                  reg_sop <= not RX_SOP_N;
                  reg_sof <= not RX_SOF_N;
               end if;
            end if;
         end if;
      end process;

   end generate;

   GEN_16_SOP: if (DATA_WIDTH = 16 and OFFSET = 0) generate

      reg_sopp: process(CLK, RESET)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               reg_sop  <= '0';
               reg_sop2 <= '0';
               reg_sof  <= '0';
            else
               if (RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0') then
                  reg_sop  <= not RX_SOP_N;
                  reg_sop2 <= not RX_SOP_N;
                  reg_sof  <= not RX_SOF_N;
                  if (conv_integer(cnt_part) = 1) then
                     reg_sop <= reg_sop2;
                  end if;
               end if;
            end if;
         end if;
      end process;

   end generate;

   -- ---------------------------------------------------------------------
   --                    End of packet/frame
   -- ---------------------------------------------------------------------

   reg_eopp: process(CLK, RESET)
   begin
      if (CLK'event and CLk = '1') then
         if (RESET = '1') then
            reg_eop <= '0';
            reg_eof <= '0';
         else
            if (RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0') then
               reg_eop <= not RX_EOP_N;
               reg_eof <= not RX_EOF_N;
            end if;
         end if;
      end if;
   end process;
 
   GEN_128_EOP: if (DATA_WIDTH = 128) generate

      out_eopp: process(reg_eop, RX_EOP_N, RX_REM, cnt_part, RX_SRC_RDY_N)
      begin
         TX_EOP_N <= not reg_eop;
         if (conv_integer(cnt_part) = 1) then
            if (RX_SRC_RDY_N = '0' and RX_EOP_N = '0') then
               if (conv_integer(RX_REM) < 2) then
                  TX_EOP_N <= '0';
               end if;
            end if;
         end if;
      end process;
 
      out_eofp: process(reg_eof, RX_EOF_N, RX_REM, cnt_part, RX_SRC_RDY_N)
      begin
         TX_EOF_N <= not reg_eof;
         if (conv_integer(cnt_part) = 1) then
            if (RX_SRC_RDY_N = '0' and RX_EOF_N = '0') then
               if (conv_integer(RX_REM) < 2) then
                  TX_EOF_N <= '0';
               end if;
            end if;
         end if;
      end process;

   end generate;

   GEN_16_EOP: if (DATA_WIDTH = 16) generate

      TX_EOP_N <= not reg_eop;
      TX_EOF_N <= not reg_eof;

   end generate;

   -- ---------------------------------------------------------------------
   --                    Cutted data & valid
   -- ---------------------------------------------------------------------

   CUTTED_DATA <= reg_cut_data;
   CUTTED_VLD  <= reg_cut_vld;

   GEN_128_CUT: if (DATA_WIDTH = 128) generate

      GEN_CUT_DATA0: if (OFFSET = 0) generate
         reg_cut_datap: process(CLK)
         begin
            if (CLK'event and CLK = '1') then
               reg_cut_data <= RX_DATA(15 downto 0);
            end if;
         end process;
      end generate;
 
      GEN_CUT_DATA2: if (OFFSET = 2) generate
         reg_cut_datap: process(CLK)
         begin
            if (CLK'event and CLK = '1') then
               reg_cut_data <= RX_DATA(31 downto 16);
            end if;
         end process;
      end generate;
 
      reg_cut_vldp: process(CLK, RESET)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               reg_cut_vld <= '0';
            else
               if (RX_SRC_RDY_N = '0') then
                  if (conv_integer(cnt_part) = 1) then
                     if (RX_SOP_N = '0') then
                        reg_cut_vld <= '1';
                     else
                        reg_cut_vld <= '0';
                     end if;
                  else
                     reg_cut_vld <= '0';
                  end if;
               else
                  reg_cut_vld <= '0';
               end if;
            end if;
         end if;
      end process;

   end generate;

   GEN_16_CUT: if (DATA_WIDTH = 16) generate

      reg_cut_datap: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            reg_cut_data <= RX_DATA;
         end if;
      end process;

      reg_cut_vldp: process(CLK, RESET)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               reg_cut_vld <= '0';
            else
               reg_cut_vld <= '0';
               if (RX_SRC_RDY_N = '0') then
                  if (sig_cut_vld = '1') then
                     reg_cut_vld <= '1';
                  end if;
               end if;
            end if;
         end if;
      end process;

      GEN_16_CUT_OFF_0: if (OFFSET = 0) generate
         sig_cut_vldp: process(cnt_part, cnt_word)
         begin
            sig_cut_vld <= '0';
            if (conv_integer(cnt_part) = 1) then
               if (conv_integer(cnt_word) = 0) then
                  sig_cut_vld <= '1';
               end if;
            end if;
         end process;
      end generate;

      GEN_16_CUT_OFF_2: if (OFFSET = 2) generate
         sig_cut_vldp: process(cnt_part, cnt_word)
         begin
            sig_cut_vld <= '0';
            if (conv_integer(cnt_part) = 1) then
               if (conv_integer(cnt_word) = 1) then
                  sig_cut_vld <= '1';
               end if;
            end if;
         end process;
      end generate;

   end generate;

   -- ---------------------------------------------------------------------
   --                    FrameLink part counter
   -- ---------------------------------------------------------------------

   cnt_partp: process(CLK, RESET)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            cnt_part <= (others => '0');
         else
            if (RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0') then
               if (RX_EOF_N = '0') then
                  cnt_part <= (others => '0');
               else
                  if (RX_EOP_N = '0') then
                     cnt_part <= cnt_part + 1;
                  end if;
               end if;
            end if;
         end if;
      end if;
   end process;

   reg_partp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         reg_part <= cnt_part;
      end if;
   end process;

   -- ---------------------------------------------------------------------
   --                    FrameLink word counter
   -- ---------------------------------------------------------------------

   GEN_WORD_CNT: if (DATA_WIDTH = 16) generate

      cnt_wordp: process(CLK, RESET)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               cnt_word <= (others => '0');
            else
               if (RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0') then
                  if (RX_EOP_N = '0') then
                     cnt_word <= (others => '0');
                  else
                     cnt_word <= cnt_word + 1;
                  end if;
               end if;
            end if;
         end if;
      end process;

   end generate;

   -- ---------------------------------------------------------------------

end architecture full;
