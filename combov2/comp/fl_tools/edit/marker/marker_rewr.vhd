-- marker_rewr.vhd: FrameLink header / footer marker (rewrite) architecture
-- Copyright (C) 2006 CESNET
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
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Entity declaration
-- ----------------------------------------------------------------------------

entity FL_MARKER_REWRITE is
   generic(
      DATA_WIDTH   : integer := 32;
      HEADER       : boolean := true;
      FOOTER       : boolean := true;
      OFFSET       : integer := 4;
      SIZE         : integer := 1;
      MARK_HDR     : boolean := true;
      MARK_FTR     : boolean := false
   );
   port(
      CLK          : in std_logic;
      RESET        : in std_logic;
      MARK         : in  std_logic_vector(SIZE*8-1 downto 0);
      MARK_NEXT    : out std_logic;
      RX_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM       : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SRC_RDY_N : in  std_logic;
      RX_DST_RDY_N : out std_logic;
      RX_SOP_N     : in  std_logic;
      RX_EOP_N     : in  std_logic;
      RX_SOF_N     : in  std_logic;
      RX_EOF_N     : in  std_logic;
      TX_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM       : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N : out std_logic;
      TX_DST_RDY_N : in  std_logic;
      TX_SOP_N     : out std_logic;
      TX_EOP_N     : out std_logic;
      TX_SOF_N     : out std_logic;
      TX_EOF_N     : out std_logic
   );
end entity FL_MARKER_REWRITE;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full_rewrite of FL_MARKER_REWRITE is

   -- ------------------ Components declaration -------------------------------
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


   -- ------------------ Constants declaration --------------------------------

   constant CNT_WIDTH      : integer := log2(OFFSET+2); -- in Bytes, should be 2^n
   constant FRAME_POS      : integer := OFFSET / (DATA_WIDTH/8);
   constant POS_OFFSET     : integer := OFFSET rem (DATA_WIDTH/8);

   -- ------------------ Signals declaration ----------------------------------

   signal hdr_frame     : std_logic;
   signal ftr_frame     : std_logic;
   signal frame         : std_logic;

   signal rx_src_rdy    : std_logic;
   signal rx_dst_rdy    : std_logic;
   signal tx_src_rdy    : std_logic;
   signal tx_dst_rdy    : std_logic;
   signal rdy           : std_logic;

   signal mux_sel       : std_logic;
   signal data_reg      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal ins_data      : std_logic_vector(DATA_WIDTH-1 downto 0);

   signal mark_next_reg : std_logic;
   signal cnt_frm       : std_logic_vector(CNT_WIDTH downto 0);
   signal cnt_frm_of    : std_logic;

begin

   -- ------------------------------- Body ------------------------------------

   assert (MARK_HDR xor MARK_FTR)
      report "FL_MARKER: Bad use - only 1 of MARK_HDR or MARK_FTR must be true"
      severity error;

   assert (not MARK_HDR or HEADER)
      report "FL_MARKER: Bad use - header mark can't be add to FL without HEADER frame"
      severity error;

   assert (not MARK_FTR or FOOTER)
      report "FL_MARKER: Bad use - footer mark can't be add to FL without FOOTER frame"
      severity error;

   assert (POS_OFFSET + SIZE <= DATA_WIDTH/8)
      report "SIZE of MARK is to big or OFFSET is set into 2 clk cycles"
      severity error;


   fl_dec_i: FL_DEC
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
      PLD_FRAME   => open,
      SOFTR       => open,
      EOFTR       => open,
      FTR_FRAME   => ftr_frame,
      EOF         => open,
      SRC_RDY     => rx_src_rdy,
      DST_RDY     => rx_dst_rdy
   );


   -- switch between mark header / footer
   frame <= hdr_frame when MARK_HDR else ftr_frame;

   -- frame cycle counter
   process(CLK, RESET)
   begin
      if RESET = '1' then
         cnt_frm <= (others => '0');
         cnt_frm_of <= '0';
      elsif CLK = '1' and CLK'event then
         if (frame = '1') and (rdy = '1') then
            cnt_frm <= cnt_frm + '1';
            if (cnt_frm = not conv_std_logic_vector(0,CNT_WIDTH)) then
              cnt_frm_of <= '1'; -- catch counter overflow
            end if;
         elsif frame = '0' then
            cnt_frm <= (others => '0');
            cnt_frm_of <= '0';
         end if;
      end if;
   end process;

   -- direct / insert mark
   mux_sel  <= '1' when (cnt_frm = FRAME_POS) and (frame = '1') and (cnt_frm_of='0') else '0';

	---------------------------------------------------------
   -- DATA

   -- insert data extra process (avoid synthesis warning)
   process(RX_DATA,MARK)
   begin
      if (POS_OFFSET+SIZE = DATA_WIDTH/8) and (POS_OFFSET = 0) then
         ins_data <= MARK;
      elsif (POS_OFFSET+SIZE = DATA_WIDTH/8) and (POS_OFFSET /= 0) then
         ins_data <= MARK & RX_DATA(POS_OFFSET*8-1 downto 0);
      elsif (POS_OFFSET+SIZE /= DATA_WIDTH/8) and (POS_OFFSET = 0) then
         ins_data <= RX_DATA(DATA_WIDTH-1 downto (POS_OFFSET+SIZE)*8) & MARK;
      else
         ins_data <= RX_DATA(DATA_WIDTH-1 downto (POS_OFFSET+SIZE)*8) &
                     MARK &
                     RX_DATA(POS_OFFSET*8-1 downto 0);
      end if;
   end process;


   -- TX data mux
   process(mux_sel,RX_DATA,ins_data)
   begin
      case mux_sel is
         when '0' =>      -- direct
            data_reg <= RX_DATA;
         when '1' =>      -- insert
            data_reg <= ins_data;
         when others => null;
      end case;
   end process;

   -- TX data reg
   process(CLK,RESET)
   begin
      if RESET = '1' then
         TX_DATA <= (others => '0');
      elsif CLK = '1' and CLK'event then
         if rdy = '1' then
            TX_DATA <= data_reg;
         end if;
      end if;
   end process;

   -- TX REM reg
   process(CLK,RESET)
   begin
      if RESET = '1' then
         TX_REM <= (others => '0');
      elsif CLK = '1' and CLK'event then
         if rdy = '1' then
            TX_REM <= RX_REM;
         end if;
      end if;
   end process;

   ---------------------------------------------------------
   --  RDY logic & signals
   ---------------------------------------------------------

   -- connection with ENTITY signals
   tx_dst_rdy   <= not TX_DST_RDY_N;
   TX_SRC_RDY_N <= not tx_src_rdy;

   rx_dst_rdy <= tx_dst_rdy;

   -- global RDY signal, without "add_last" stal
   rdy <= rx_src_rdy and tx_dst_rdy;

   -- tx_src_rdy register
   process(CLK,RESET)
   begin
      if RESET = '1' then
         tx_src_rdy <= '0';
      elsif CLK = '1' and CLK'event then
         if tx_dst_rdy = '1' then
            tx_src_rdy <= rx_src_rdy;
         end if;
      end if;
   end process;


   ---------------------------------------------------------
   --  SOF, EOF, SOP, EOP reg
   process(CLK,RESET)
   begin
      if RESET = '1' then
         TX_SOF_N <= '1';
         TX_SOP_N <= '1';
         TX_EOP_N <= '1';
         TX_EOF_N <= '1';
      elsif CLK = '1' and CLK'event then
         if rdy = '1' then -- store rx
            TX_SOF_N <= RX_SOF_N;
            TX_SOP_N <= RX_SOP_N;
            TX_EOP_N <= RX_EOP_N;
            TX_EOF_N <= RX_EOF_N;
         end if;
      end if;
   end process;


   -- mark next generator
   process(CLK,RESET)
   begin
      if RESET = '1' then
         mark_next_reg <= '0';
      elsif CLK = '1' and CLK'event then
         if rdy = '1' then
            if mux_sel = '1' then -- insert mark
               mark_next_reg <= '1';
            else
               mark_next_reg <= '0';
            end if;
         end if;
      end if;
   end process;

   MARK_NEXT <= mark_next_reg and rdy;

end architecture full_rewrite;
