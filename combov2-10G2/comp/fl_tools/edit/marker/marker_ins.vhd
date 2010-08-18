-- marker_ins.vhd: FrameLink header / footer marker (insert mark) architecture
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Entity declaration
-- ----------------------------------------------------------------------------

entity FL_MARKER_INSERT is
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
end entity FL_MARKER_INSERT;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full_insert of FL_MARKER_INSERT is

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


   component FL_MARKER_CU is
      generic(
         DATA_WIDTH   : integer := 32;
         FRAME_POS    : integer;
         MARK_SIZE    : integer
      );
      port(
         CLK          : in std_logic;
         RESET        : in std_logic;

         FRAME        : in std_logic;
         RX_SRC_RDY   : in std_logic;
         TX_DST_RDY   : in std_logic;
         RX_EOP       : in std_logic;
         RX_REM       : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
         RX_STALL     : out std_logic;
         TX_EOP       : out std_logic;
         TX_REM       : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
         OUTPUT       : out std_logic_vector(1 downto 0)
      );
   end component;


   -- ------------------ Constants declaration --------------------------------

   constant FRAME_POS      : integer := OFFSET / (DATA_WIDTH/8);
   constant POS_OFFSET     : integer := OFFSET rem (DATA_WIDTH/8);

   -- ------------------ Signals declaration ----------------------------------

   signal eohdr         : std_logic;
   signal hdr_frame     : std_logic;
   signal eopld         : std_logic;
   signal eoftr         : std_logic;
   signal ftr_frame     : std_logic;
   signal tx_eop_mark   : std_logic;

   signal rx_src_rdy    : std_logic;
   signal rx_src_rdy_reg: std_logic;
   signal rx_dst_rdy    : std_logic;
   signal tx_src_rdy    : std_logic;
   signal tx_dst_rdy    : std_logic;

   signal rx_rdy        : std_logic;
   signal tx_rdy        : std_logic;
   signal rdy           : std_logic;

   signal frame         : std_logic;
   signal rx_eop        : std_logic;
   signal rx_stall      : std_logic;
   signal cu2mux        : std_logic_vector(1 downto 0);
   signal stored_data   : std_logic_vector(SIZE*8 - 1 downto 0);
   signal ins_data      : std_logic_vector(DATA_WIDTH + SIZE*8 - 1 downto 0);
   signal shifted_data  : std_logic_vector(DATA_WIDTH-1 downto 0);

   signal tx_data_reg   : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal add_last      : std_logic;
   signal add_last_reg  : std_logic;
   signal mark_next_reg : std_logic;

   begin

      assert (MARK_HDR xor MARK_FTR)
         report "FL_MARKER: Bad use - only 1 of MARK_HDR or MARK_FTR must be true"
         severity error;

      assert (not MARK_HDR or HEADER)
         report "FL_MARKER: Bad use - header mark can't be add to FL without HEADER frame"
         severity error;

      assert (not MARK_FTR or FOOTER)
         report "FL_MARKER: Bad use - footer mark can't be add to FL without FOOTER frame"
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
         EOHDR       => eohdr,
         HDR_FRAME   => hdr_frame,
         SOPLD       => open,
         EOPLD       => eopld,
         PLD_FRAME   => open,
         SOFTR       => open,
         EOFTR       => eoftr,
         FTR_FRAME   => ftr_frame,
         EOF         => open,
         SRC_RDY     => rx_src_rdy,
         DST_RDY     => rx_dst_rdy
      );


      cu_i: FL_MARKER_CU
      generic map(
         DATA_WIDTH     => DATA_WIDTH,
         FRAME_POS      => FRAME_POS,
         MARK_SIZE      => SIZE
      )
      port map(
         CLK      => CLK,
         RESET    => RESET,
         FRAME    => frame,
         RX_SRC_RDY   => rx_src_rdy,
         TX_DST_RDY   => tx_dst_rdy,
         RX_EOP   => rx_eop,
         RX_REM   => RX_REM,
         RX_STALL => rx_stall,
         TX_EOP   => tx_eop_mark,
         TX_REM   => TX_REM,
         OUTPUT   => cu2mux
      );


      -- TX data reg
      process(CLK, RESET)
      begin
         if RESET = '1' then
               TX_DATA <= (others => '0');
         else
           if CLK = '1' and CLK'event then
              if rdy = '1' then
                 TX_DATA <= tx_data_reg;
              end if;
           end if;
         end if;
      end process;


      -- shifted data buffer
      process(CLK)
      begin
         if CLK = '1' and CLK'event then
            if RESET = '1' then
               stored_data <= (others => '0');
            elsif rdy = '1' then
               if cu2mux = "01" then
                  stored_data <=ins_data(DATA_WIDTH+SIZE*8-1 downto DATA_WIDTH);
               else
                  stored_data <= RX_DATA(DATA_WIDTH-1 downto DATA_WIDTH-SIZE*8);
               end if;
            end if;
         end if;
      end process;

      -- insert data
      process(RX_DATA,MARK)
      begin
         if POS_OFFSET /= 0 then -- data before mark
		    ins_data(POS_OFFSET*8-1 downto 0) <= RX_DATA(POS_OFFSET*8-1 downto 0);
         end if;

         ins_data(SIZE*8+POS_OFFSET*8-1 downto POS_OFFSET*8) <= MARK;
         ins_data(DATA_WIDTH+SIZE*8-1 downto SIZE*8+POS_OFFSET*8) <=
            RX_DATA(DATA_WIDTH-1 downto POS_OFFSET*8);
      end process;

      -- shifted data
      process(RX_DATA,stored_data)
      begin
         if DATA_WIDTH = SIZE*8 then
            shifted_data <= stored_data;
         else
            shifted_data <= RX_DATA(DATA_WIDTH-SIZE*8-1 downto 0) & stored_data;
         end if;
      end process;

      -- TX DATA MUX
      process(cu2mux,RX_DATA,ins_data,shifted_data,stored_data)
      begin
         case cu2mux is
            when "00" =>      -- direct
               tx_data_reg <= RX_DATA;
            when "01" =>      -- insert
               tx_data_reg <= ins_data(DATA_WIDTH-1 downto 0);
            when "10" =>      -- shift
               tx_data_reg <= shifted_data;
            when "11" =>      -- add last
               tx_data_reg <= (others => '0');
               tx_data_reg(SIZE*8-1 downto 0) <= stored_data;
            when others => null;
         end case;
      end process;


      ---------------------------------------------------------
      --  signals to / from control unit
      ---------------------------------------------------------

      frame  <= hdr_frame when MARK_HDR else ftr_frame;
      rx_eop <= eohdr when MARK_HDR else eoftr;
      add_last <= '1' when (cu2mux = "11") else '0';

      -- add_last register for tx_src_rdy (when come EOP)
      process(CLK)
      begin
         if CLK = '1' and CLK'event then
            if RESET = '1' then
               add_last_reg <= '0';
            else
               add_last_reg <= add_last;
            end if;
         end if;
      end process;

      ---------------------------------------------------------
      --  RDY logic & signals
      ---------------------------------------------------------

      -- connection with ENTITY signals
      tx_dst_rdy   <= not TX_DST_RDY_N;
      TX_SRC_RDY_N <= not tx_src_rdy;

      -- global RDY signal, without "add_last" stal
      rdy <= (rx_src_rdy and tx_dst_rdy) or
             (add_last and tx_dst_rdy) or
             (rx_stall and tx_dst_rdy);


      -- rx_src_rdy register
      process(CLK)
      begin
         if CLK = '1' and CLK'event then
            if RESET = '1' then
               rx_src_rdy_reg <= '0';
            else
	       if (tx_dst_rdy='1' and (rx_src_rdy_reg ='1' or rx_src_rdy='1' or rx_stall= '1')) then
                  rx_src_rdy_reg <= rx_src_rdy or rx_stall;
	       end if;
            end if;
         end if;
      end process;

      rx_dst_rdy <= tx_dst_rdy and not add_last and not rx_stall;
      rx_rdy     <= rx_src_rdy and rx_dst_rdy;

      tx_src_rdy <= rx_src_rdy_reg or add_last_reg or rx_stall;
      tx_rdy     <= tx_dst_rdy and tx_src_rdy;

      ---------------------------------------------------------
      --  SOF, EOF, SOP, EOP logic
      ---------------------------------------------------------

      -- TX_SOF_N reg
      process(CLK)
      begin
         if CLK = '1' and CLK'event then
            if RESET = '1' then
               TX_SOF_N <= '1';
            elsif rx_rdy = '1' then -- store rx
               TX_SOF_N <= RX_SOF_N;
            elsif tx_rdy = '1' then -- clear
               TX_SOF_N <= '1';
            end if;
         end if;
      end process;

      ------------------------------------------
      -- TX_SOP_N reg
      process(CLK)
      begin
         if CLK = '1' and CLK'event then
            if RESET = '1' then
               TX_SOP_N <= '1';
            elsif rx_rdy = '1' then -- store rx
               TX_SOP_N <= RX_SOP_N;
            elsif tx_rdy = '1' then -- clear
               TX_SOP_N <= '1';
            end if;
         end if;
      end process;

      ------------------------------------------
      -- TX_EOP_N logic & reg
      process(CLK)
      begin
         if CLK = '1' and CLK'event then
            if RESET = '1' then
               TX_EOP_N <= '1';
            elsif rdy = '1' then
               if MARK_HDR then
                  TX_EOP_N <= not (tx_eop_mark or eopld or eoftr);
               else -- MARK_FTR
                  TX_EOP_N <= not (eohdr or eopld or tx_eop_mark);
               end if;
            end if;
         end if;
      end process;


      ------------------------------------------
      -- TX_EOF_N logic & reg
      process(CLK)
      begin
         if CLK = '1' and CLK'event then
            if RESET = '1' then
               TX_EOF_N <= '1';
            elsif rdy = '1' then
               if MARK_FTR then
                  TX_EOF_N <= not tx_eop_mark;
               elsif rx_rdy = '1' then 
                  TX_EOF_N <= RX_EOF_N;
               elsif tx_rdy = '1' then
                  TX_EOF_N <= '1';
               end if;
            end if;
         end if;
      end process;


      -- mark next generator
      process(CLK)
      begin
         if CLK = '1' and CLK'event then
            if RESET = '1' then
               mark_next_reg <= '0';
            elsif cu2mux = "01" then -- insert mark
               mark_next_reg <= '1';
            elsif tx_rdy = '1' then
               mark_next_reg <= '0';
            end if;
         end if;
      end process;

      MARK_NEXT <= mark_next_reg and tx_rdy;

end architecture full_insert;
