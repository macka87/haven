-- cutter.vhd: FrameLink cutter - remove defined bytes from FrameLink packet
-- Copyright (C) 2007 CESNET
-- Author(s): Michal Trs <trsm1@liberouter.org>
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
-- $Id:
--


library ieee;
use ieee.std_logic_1164.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of FL_CUTTER is

   -- ------------------ Constants declaration --------------------------------
   constant CNT_MSB        : integer := 12; -- maximum length of packet
   constant START_BASE     : integer := OFFSET / (DATA_WIDTH/8);
   constant END_BASE       : integer := (OFFSET + SIZE - 1) / (DATA_WIDTH/8);
   constant START_OFFSET   : integer := (OFFSET*8) rem DATA_WIDTH;
   constant END_OFFSET     : integer := ((OFFSET + SIZE)*8 - 1) rem DATA_WIDTH;
   constant ALIGN          : boolean := (START_OFFSET = 0)
                                        and (END_OFFSET = (DATA_WIDTH - 1));
   constant SHIFT_OFFSET   : integer := (SIZE rem (DATA_WIDTH/8)) * 8;
   constant ALIGN_AFTER    : boolean := (SHIFT_OFFSET = 0);


   -- ------------------ Signals declaration ----------------------------------
   signal reg1_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg1_rem      : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal reg1_sop      : std_logic;
   signal reg1_sof      : std_logic;
   signal reg1_eop      : std_logic;
   signal reg1_eof      : std_logic;
   signal reg1_vld      : std_logic;

   signal reg2_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg2_rem      : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal reg2_sop      : std_logic;
   signal reg2_sof      : std_logic;
   signal reg2_eop      : std_logic;
   signal reg2_eof      : std_logic;
   signal reg2_vld      : std_logic;

   signal reg3_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg3_rem      : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal reg3_sop      : std_logic;
   signal reg3_sof      : std_logic;
   signal reg3_eop      : std_logic;
   signal reg3_eof      : std_logic;
   signal reg3_vld      : std_logic;

   signal reg_ce        : std_logic; -- CLK enable signal for reg2 & reg3
   signal reg_ce_reg    : std_logic; -- register fo TX_RDY

   signal hdr_frame     : std_logic;
   signal pld_frame     : std_logic;
   signal ftr_frame     : std_logic;

   signal cut_frame     : std_logic;

   signal cnt_clk       : std_logic_vector(CNT_MSB downto 0); -- position cnt
   signal cnt_clk_reg   : std_logic_vector(CNT_MSB downto 0);
   signal cnt_ce        : std_logic;
   signal cnt_rst       : std_logic;

   signal cut_start     : boolean; -- start cutting data
   signal cut_stop      : boolean; -- stop cutting data
   signal mov_ssig      : boolean; -- move sop & sof back
   signal mov_esig      : boolean; -- move eop & eof front
   signal cutting       : boolean; -- beetwen 'cut_start' and 'cut_stop'
   signal cutting_reg   : boolean; -- RS reg for generate cutting signal
   signal hold          : boolean; -- true when fsm is in st_wait

   signal mux_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal mux_rem       : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal mux_sop       : std_logic;
   signal mux_sof       : std_logic;

   signal rx_src_rdy    : std_logic; -- rdy signal for FL_DEC
   signal rx_dst_rdy    : std_logic; -- rdy signal for FL_DEC
   signal rdy           : std_logic; -- All rdy signals

   type t_states is (st_direct, st_cut, st_wait, st_cut2, st_shift);
   signal cur_state     : t_states;
   signal next_state    : t_states;

   -- cutted data register (for store cutted data)
   signal cdata_reg     : std_logic_vector
      (max(((END_BASE-START_BASE-1)*DATA_WIDTH - 1), 0) downto 0);
   signal cdata_rbegin  : std_logic_vector(DATA_WIDTH - 1 downto START_OFFSET);
   signal cdata_rend    : std_logic_vector(END_OFFSET downto 0);
   signal cdata_vld     : std_logic;

   signal mux_sel       : std_logic_vector(1 downto 0);
   -- 00 = direct, 01 = cut, 10 = shift, 11 = cut2


   component FL_DEC is
   generic(
      -- Header data present
      HEADER      : boolean := true;
      -- Footer data present
      FOOTER      : boolean := true
   );
   port(
      CLK         : in  std_logic;
      RESET       : in  std_logic;
      -- FrameLink interface
      SOF_N       : in  std_logic;
      SOP_N       : in  std_logic;
      EOP_N       : in  std_logic;
      EOF_N       : in  std_logic;
      SRC_RDY_N   : in  std_logic;
      DST_RDY_N   : out std_logic;
      -- decoder signals
      SOF         : out std_logic;  -- start of frame
      SOHDR       : out std_logic;  -- start of header
      EOHDR       : out std_logic;  -- end of header
      HDR_FRAME   : out std_logic;  -- header part is transmitted
      SOPLD       : out std_logic;  -- start of payload
      EOPLD       : out std_logic;  -- end of payload
      PLD_FRAME   : out std_logic;  -- payload part is transmitted
      SOFTR       : out std_logic;  -- start of footer
      EOFTR       : out std_logic;  -- end of footer
      FTR_FRAME   : out std_logic;  -- footer part is transmitted
      EOF         : out std_logic;  -- end of frame
      SRC_RDY     : out std_logic;  -- source ready
      DST_RDY     : in  std_logic   -- destination ready
   );
   end component FL_DEC;


begin

   i_fl_dec: FL_DEC
   generic map(
      HEADER   => HEADER,
      FOOTER   => FOOTER
   )
   port map(
      CLK         => CLK,
      RESET       => RESET,
      SOF_N       => RX_SOF_N,
      SOP_N       => RX_SOP_N,
      EOP_N       => RX_EOP_N,
      EOF_N       => RX_EOF_N,
      SRC_RDY_N   => RX_SRC_RDY_N,
      DST_RDY_N   => RX_DST_RDY_N,
      -- decoder signals
      SOF         => open,
      SOHDR       => open,
      EOHDR       => open,
      HDR_FRAME   => hdr_frame,
      SOPLD       => open,
      EOPLD       => open,
      PLD_FRAME   => pld_frame,
      SOFTR       => open,
      EOFTR       => open,
      FTR_FRAME   => ftr_frame,
      EOF         => open,
      SRC_RDY     => rx_src_rdy,
      DST_RDY     => rx_dst_rdy
   );


   -- cut frame
   process(hdr_frame, pld_frame, ftr_frame)
   begin
      if CUT_HDR then
         cut_frame <= hdr_frame;
      elsif CUT_PLD then
         cut_frame <= pld_frame;
      else
         cut_frame <= ftr_frame;
      end if;
   end process;


   -- clk counter
   --------------
   cnt_ce <= cut_frame and rdy;
   cnt_rst <= reg1_eop and rdy and not cut_frame;

   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         if RESET = '1' or cnt_rst = '1' then -- reset counter
            cnt_clk <= (others => '0');
         elsif cnt_ce = '1' then
            cnt_clk <= cnt_clk + 1;
         end if;
      end if;
   end process;

   -- clk counter reg
   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         cnt_clk_reg <= cnt_clk;
      end if;
   end process;


   cut_start <= (cnt_clk = conv_std_logic_vector(START_BASE,cnt_clk'length))
               and (rdy = '1') and (cut_frame = '1');

   cut_stop <= ((cnt_clk = conv_std_logic_vector(END_BASE,cnt_clk'length))
               and (rdy = '1') and (cut_frame = '1') and (SIZE /= 0))
               or (cutting_reg and RX_EOP_N = '0');

   -- cutting RS register with reset
   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         if cut_stop or RESET = '1' then
            cutting_reg <= false;
         elsif cut_start then
            cutting_reg <= true;
         end if;
      end if;
   end process;


   -- move SOP, SOF flag
   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         mov_ssig <= (OFFSET = 0) and (SIZE >= DATA_WIDTH/8) and cutting;
      end if;
   end process;

   -- move EOP, EOF flag
   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         mov_esig <= (RX_EOP_N = '0') and cutting
            and (RX_REM >= conv_std_logic_vector(SIZE-1,log2(DATA_WIDTH/8)));
      end if;
   end process;


   --generate wait states (cutting signal)
   process(cutting_reg, cut_start, cut_stop)
   begin
      if rx_src_rdy = '0' then
         cutting <= false;
      elsif ALIGN then
         cutting <= cutting_reg or cut_start;
      elsif SIZE >= DATA_WIDTH/8 then
         if START_OFFSET = 0 then
            cutting <= (cutting_reg or cut_start) and not cut_stop;
         elsif (END_OFFSET = DATA_WIDTH-1) or ALIGN_AFTER then
            cutting <= cutting_reg;
         end if;
      else
         if SIZE = 0 then
            cutting <= cutting_reg;
         else
            cutting <= false;
         end if;
      end if;
   end process;


   -- for aligned cutted data (no MUX is needed)
   ag: if ALIGN generate
      mux_data <= reg1_data;
      mux_rem <= reg1_rem;
   end generate;

   -- for all other unaligned data
   nag: if not ALIGN generate
   -- data mux
   process(mux_sel, RX_DATA, reg1_data, reg2_data, rdy)
   begin
      if rdy = '1' then
         case mux_sel is
            when "00" => -- direct
               mux_data <= reg1_data;
            when "01" => -- cut
               if START_BASE = END_BASE then
                  if START_OFFSET = 0 then
                     mux_data <= RX_DATA(SIZE*8 - 1 downto 0) &
                                 reg1_data(DATA_WIDTH - 1 downto END_OFFSET + 1);
                  elsif END_OFFSET = DATA_WIDTH-1 then
                     mux_data <= RX_DATA(SIZE*8 - 1 downto 0) &
                                 reg1_data(START_OFFSET - 1 downto 0);
                  else
                     mux_data <= RX_DATA(SIZE*8 - 1 downto 0) &
                                 reg1_data(DATA_WIDTH - 1 downto END_OFFSET+1) &
                                 reg1_data(START_OFFSET - 1 downto 0);
                  end if;
               elsif START_OFFSET > END_OFFSET then
                  mux_data <= RX_DATA(DATA_WIDTH - START_OFFSET + END_OFFSET
                                 downto END_OFFSET + 1) &
                              reg1_data(START_OFFSET - 1 downto 0);
               else
                  mux_data <= reg1_data;
               end if;
            when "10" => -- shift
               mux_data <= RX_DATA(SHIFT_OFFSET - 1 downto 0) &
                           reg1_data(DATA_WIDTH - 1 downto SHIFT_OFFSET);
            when "11" => -- cut 2
               if END_OFFSET = DATA_WIDTH - 1 then
                  mux_data <= RX_DATA(SHIFT_OFFSET - 1 downto 0) &
                              reg2_data(START_OFFSET - 1 downto 0);
               else
                  if START_OFFSET > END_OFFSET then
                     mux_data <= RX_DATA(DATA_WIDTH - START_OFFSET + END_OFFSET
                                    downto END_OFFSET + 1) &
                                 reg2_data(START_OFFSET - 1 downto 0);
                  else
                     mux_data <= RX_DATA(END_OFFSET - START_OFFSET downto 0) &
                                 reg1_data(DATA_WIDTH - 1 downto END_OFFSET + 1) &
                                 reg2_data(START_OFFSET - 1 downto 0);
                  end if;
               end if;
            when others => null;
         end case;
      end if;
   end process;

   -- REM mux
   process(reg1_rem, reg1_eop, rdy)
   begin
      if rdy = '1' then
         if reg1_eop = '1' and cut_frame = '1' then -- end of cutting packet
            if (SIZE = 0) and (START_OFFSET /= 0) then -- unalign cutting to end
               mux_rem <=
                  conv_std_logic_vector(START_OFFSET/8,log2(DATA_WIDTH/8));
            elsif ALIGN_AFTER then  -- align cutting
               mux_rem <= reg1_rem;
            else -- unalign cutting
               mux_rem <= reg1_rem
                        - conv_std_logic_vector(SHIFT_OFFSET/8,log2(DATA_WIDTH/8));
            end if;
         else -- else packets
            mux_rem <= reg1_rem;
         end if;
      end if;
   end process;
   end generate;


   -- Cutted data logic
   ----------------------------------
   cdg: if SIZE /= 0 generate
      occ: -- cutted data in 1 CLK cycle
      if START_BASE = END_BASE generate
         CUTTED_DATA <= reg1_data(END_OFFSET downto START_OFFSET);

         -- cutted data valid signal register
         process(cut_stop, cut_frame, rdy)
         begin
            if cut_stop and cut_frame = '1' and rdy = '1' then
               cdata_vld <= '1';
            else
               cdata_vld <= '0';
            end if;
         end process;
      end generate;

      mcc: -- cutted data in >1 CLK cycle
      if START_BASE /= END_BASE generate
         process(CLK)
         begin
            if CLK = '1' and CLK'event then
               if cnt_clk_reg = START_BASE then
                  cdata_rbegin <= reg1_data(DATA_WIDTH - 1 downto START_OFFSET);
               end if;
            end if;
         end process;

         cdg_gen: -- register for cutted data
         for i in 0 to END_BASE - START_BASE - 2 generate
            process(CLK)
            begin
               if CLK = '1' and CLK'event then
                  if cnt_clk_reg = i + START_BASE + 1 then
                     cdata_reg((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH) <= reg1_data;
                  end if;
               end if;
            end process;
         end generate;

         process(CLK)
         begin
            if CLK = '1' and CLK'event then
               if cnt_clk_reg = END_BASE then
                  cdata_rend <= reg1_data(END_OFFSET downto 0);
               end if;
            end if;
         end process;


         -- assign signal to IFC
         equ: if START_BASE + 1 = END_BASE generate
            CUTTED_DATA <= cdata_rend & cdata_rbegin;
         end generate;

         add: if START_BASE + 1 < END_BASE generate
            CUTTED_DATA <= cdata_rend & cdata_reg & cdata_rbegin;
         end generate;


         -- cutted data valid signal register
         process(CLK)
         begin
            if CLK = '1' and CLK'event then
               if cut_stop and cut_frame = '1' and rdy = '1' then
                  cdata_vld <= '1';
               else
                  cdata_vld <= '0';
               end if;
            end if;
         end process;
      end generate;

      -- cutted data ENTITY signal
      process(CLK)
      begin
         if CLK = '1' and CLK'event then
               CUTTED_VLD <= cdata_vld;
         end if;
      end process;
   end generate;


   -- for cutting to end (unknown registry size)
   cdg_empty: if SIZE = 0 generate
      CUTTED_VLD <= '0';
   end generate;
   ----------------------------------


   -- control pipeline (w RESET signal) --
   ---------------------------------------
   -- stage 1 --
   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         if RESET = '1' then
            reg1_rem    <= (others => '0');
            reg1_sop    <= '0';
            reg1_sof    <= '0';
            reg1_eop    <= '0';
            reg1_eof    <= '0';
         elsif rdy = '1' then
            reg1_rem    <= RX_REM;
            reg1_sop    <= mux_sop;
            reg1_sof    <= mux_sof;
            reg1_eop    <= not RX_EOP_N;
            reg1_eof    <= not RX_EOF_N;
         end if;
      end if;
   end process;

   -- SOx pipeline mux (for moving with SOx)
   mux_sop <= reg1_sop when mov_ssig else not RX_SOP_N;
   mux_sof <= reg1_sof when mov_ssig else not RX_SOF_N;


   -- stage 2 --
   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         if RESET = '1' then
            reg2_rem    <= (others => '0');
            reg2_sop    <= '0';
            reg2_sof    <= '0';
         elsif reg1_vld = '1' and reg_ce = '1' then
            reg2_rem    <= mux_rem;
            reg2_sop    <= reg1_sop;
            reg2_sof    <= reg1_sof;
         end if;
      end if;
   end process;

   -- EOx pipeline registers (for moving with EOx)
   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         if RESET = '1' then
            reg2_eop <= '0';
            reg2_eof <= '0';
         elsif (reg1_vld = '1' and reg_ce = '1') or mov_esig then
            reg2_eop <= reg1_eop;
            reg2_eof <= reg1_eof;
         end if;
      end if;
   end process;


   -- stage 3 --
   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         if RESET = '1' then
            reg3_rem    <= (others => '0');
            reg3_sop    <= '0';
            reg3_sof    <= '0';
            reg3_eop    <= '0';
            reg3_eof    <= '0';
         elsif reg2_vld = '1' and reg_ce = '1' then
            reg3_rem    <= reg2_rem;
            reg3_sop    <= reg2_sop;
            reg3_sof    <= reg2_sof;
            reg3_eop    <= reg2_eop;
            reg3_eof    <= reg2_eof;
         end if;
      end if;
   end process;
   ----------------------------------


   -- data pipeline (wo RESET signal)
   ----------------------------------
   -- stage 1 --
   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         if rdy = '1' then
            reg1_data   <= RX_DATA;
         end if;
      end if;
   end process;

   -- stage 2 --
   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         if reg1_vld = '1' and
          (reg_ce = '1' or mux_sel = "10" or mux_sel = "11") then
            reg2_data   <= mux_data;
         end if;
      end if;
   end process;

   -- stage 3 --
   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         if reg2_vld = '1' and reg_ce = '1' then
            reg3_data   <= reg2_data;
         end if;
      end if;
   end process;
   ----------------------------------


   -- TX ifc connection
   TX_DATA  <= reg3_data;
   TX_REM   <= reg3_rem;
   TX_SOP_N <= not reg3_sop;
   TX_SOF_N <= not reg3_sof;
   TX_EOP_N <= not reg3_eop;
   TX_EOF_N <= not reg3_eof;


   -- Signal VLD pipeline
   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         reg1_vld <= rdy;
         if reg_ce = '1' then
            reg2_vld <= reg1_vld;
            reg3_vld <= reg2_vld;
         end if;
      end if;
   end process;


   -- reg2 & reg3 ce signal
   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         if cutting or hold then
            reg_ce <= '0';
         else
            reg_ce <= '1';
         end if;
      end if;
   end process;


   -- reg_ce register
   process(CLK)
   begin
      if CLK = '1' and CLK'event then
         if rdy = '1' then
            reg_ce_reg <= reg_ce;
         end if;
      end if;
   end process;


   -- FSM
   ----------------------------------
   process(CLK,RESET)
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' then
            cur_state <= st_direct;
         elsif rdy = '1' then
            cur_state <= next_state;
         end if;
      end if;
   end process;

   -- next state logic
   process(cur_state, cut_start, cut_stop, cutting, RX_EOP_N, reg1_eop)
   begin
      next_state <= cur_state;

      case cur_state is
         when st_direct =>
            if cut_start and ALIGN and (SIZE /= DATA_WIDTH/8) then
               next_state <= st_wait;
            elsif cut_start and (SIZE * 8 > DATA_WIDTH) then
               next_state <= st_wait;
            elsif cut_start then
               next_state <= st_cut;
            end if;
         when st_cut =>
            if reg1_eop = '1' then
               next_state <= st_direct;
            elsif SIZE = 0 then
               next_state <= st_wait;
            elsif (START_BASE = END_BASE) or (SIZE < DATA_WIDTH/8) then
               next_state <= st_shift;
            elsif cut_stop and ALIGN_AFTER then
               next_state <= st_direct;
            elsif cut_stop then
               next_state <= st_cut2;
            else
               next_state <= st_wait;
            end if;
         when st_wait =>
            if (cut_stop and ALIGN) or (RX_EOP_N = '0') then
               next_state <= st_direct;
            elsif cut_stop and (START_OFFSET > END_OFFSET) then
               next_state <= st_shift;
            elsif cut_stop then
               next_state <= st_cut2;
            end if;
         when st_cut2 =>
            if ALIGN_AFTER then
               next_state <= st_direct;
            else
               next_state <= st_shift;
            end if;
         when st_shift =>
            if reg1_eop = '1' then
               next_state <= st_direct;
            end if;
      end case;
   end process;

   -- output logic
   process(cur_state, cut_stop)
   begin
      mux_sel <= "00"; -- direct
      hold <= false;

      case cur_state is
         when st_direct =>
            mux_sel <= "00"; -- direct
         when st_cut =>
            mux_sel <= "01"; -- cut
         when st_wait =>
            if cut_stop and (START_OFFSET > END_OFFSET) then
               mux_sel <= "11"; -- cut2
            else
               hold <= true;
            end if;
         when st_cut2 =>
            if (START_OFFSET = 0) and (SIZE*8 > DATA_WIDTH) then
               mux_sel <= "10"; -- shift
            else
               mux_sel <= "11"; -- cut2
            end if;
         when st_shift =>
            mux_sel <= "10"; -- shift
      end case;
   end process;
   ----------------------------------


   -- RDY signals
   rdy <= rx_src_rdy and not TX_DST_RDY_N;
   rx_dst_rdy <= not TX_DST_RDY_N;
   TX_SRC_RDY_N <= not (reg3_vld and reg_ce_reg);

end architecture FULL;
