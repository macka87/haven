-- ver_top.vhd: IBUF verification toplevel 
-- Copyright (C) 2008 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
use work.ib_pkg.all; -- Internal Bus Package
use work.lb_pkg.all; -- Local Bus Package
use work.ib_sim_oper.all; -- Internal Bus Simulation Package
use work.ibuf_general_pkg.all;

-- ----------------------------------------------------------------------------
--  Entity declaration: TRIMMING_UNIT
-- ----------------------------------------------------------------------------
entity VER_TOP is
   generic(
      DATA_WIDTH : integer := 128
   );
   port(
      -- common signals
      -- global FGPA clock
      CLK            : in  std_logic;
      CLK_156        : in  std_logic;

      -- global synchronous reset
      RESET          : in  std_logic;
      RESET_IBUF     : in  std_logic;

      -- RX Framelink interface
      RX_DATA        : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;

      -- TX FrameLink interface
      TX_DATA       : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      TX_REM        : out std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      TX_SOF_N      : out std_logic;
      TX_EOF_N      : out std_logic;
      TX_SOP_N      : out std_logic;
      TX_EOP_N      : out std_logic;
      TX_SRC_RDY_N  : out std_logic;
      TX_DST_RDY_N  : in  std_logic
   );
end entity VER_TOP;

architecture full of VER_TOP is
   signal XGMII_D        : std_logic_vector(31 downto 0);
   signal XGMII_C        : std_logic_vector(3 downto 0);
   signal XGMII_CLK      : std_logic;
   
   constant DATA_PATHS : integer := DATA_WIDTH/8;
   -- PACODAG interface
   signal CTRL_CLK       : std_logic; -- out
   signal CTRL_RESET     : std_logic; -- out
   signal CTRL_DI        : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal CTRL_REM       : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal CTRL_SRC_RDY_N : std_logic;
   signal CTRL_SOP_N     : std_logic;
   signal CTRL_EOP_N     : std_logic;
   signal CTRL_DST_RDY_N : std_logic; -- out
   signal CTRL_RDY       : std_logic; -- PACODAG is ready

    -- IBUF status interface - out
   signal SOP            : std_logic;
   signal STAT           : t_ibuf_general_stat;
   signal STAT_DV        : std_logic;
   
   -- registers
   signal reg_payload_len    : std_logic_vector(15 downto 0);
   signal reg_payload_len_we : std_logic;

   signal cnt_packet     : std_logic_vector(10 downto 0); 
   signal cnt_packet_we  : std_logic;
   
   -- FSM signals
   type t_state is (S_WORD1, S_WORD2 , S_IDLE, S_WAIT_FOR_VALID);
   signal present_state, next_state : t_state;
   
   signal reg_FRAME_ERROR       : std_logic; -- 0: OK, 1: Error occured
   signal reg_CRC_CHECK_FAILED  : std_logic; -- 0: OK, 1: Bad CRC 
   signal reg_MAC_CHECK_FAILED  : std_logic; -- 0: OK, 1: Bad MAC
   signal reg_LEN_BELOW_MIN     : std_logic; -- 0: OK, 1: Length is below min
   signal reg_LEN_OVER_MTU      : std_logic; -- 0: OK, 1: Length is over MTU
   
   signal mi320                : t_mi32;
   signal mi321                : t_mi32;
 
   -- IB_SIM component ctrl      
   signal ib_sim_ctrl0         : t_ib_ctrl;
   signal ib_sim_strobe0       : std_logic;
   signal ib_sim_busy0         : std_logic;
   
   -- IB_SIM component ctrl      
   signal ib_sim_ctrl1        : t_ib_ctrl;
   signal ib_sim_strobe1      : std_logic;
   signal ib_sim_busy1        : std_logic;
   
begin

   obuf: entity work.obuf_xgmii
      generic map (
         -- Frames contain control part
         CTRL_CMD          => false,
         -- FrameLink width
         FL_WIDTH_RX       => DATA_WIDTH,
         -- Number of items in Data FIFO (FL_WIDTH_RX + control signals wide).
         -- !!!!!!!!!!! Must be 2^n, n>=2 !!!!!!!!!!!!!!!!!!!!!!
         DFIFO_SIZE        => 1024,
         -- HFIFO item count (1-bit wide)
         HFIFO_SIZE        => 256
      )
      port map (
         -- Common signals
         -- Global reset
         RESET             => RESET,

         -- XGMII interface
         -- XGMII Transmit Clock
         XGMII_TXCLK       => XGMII_CLK,
         -- XGMII Transmit Data
         XGMII_TXD         => XGMII_D,
         -- XGMII Transmit Control
         XGMII_TXC         => XGMII_C,
         -- Reference Transmit Clock provided by user (156.25MHz)
         TX_CLK_REF        => CLK_156,

         -- Input FrameLink inteface
         RX_SOF_N          => RX_SOF_N,
         RX_SOP_N          => RX_SOP_N,
         RX_EOP_N          => RX_EOP_N,
         RX_EOF_N          => RX_EOF_N,
         RX_SRC_RDY_N      => RX_SRC_RDY_N,
         RX_DST_RDY_N      => RX_DST_RDY_N,
         RX_DATA           => RX_DATA,
         RX_REM            => RX_REM,
         -- Clock for FrameLink interface.
         FL_CLK            => CLK,

         -- Status interface
         OUTGOING_PCKT     => open,

         -- MI32 interface
         MI                => mi321,
         -- Clock for MI32 interface
         MI_CLK            => CLK
      );

   ibuf: entity work.ibuf_xgmii
      generic map (
         DFIFO_SIZE        => 1024,
         HFIFO_SIZE        => 128,
         CTRL_HDR_EN       => true,
         CTRL_FTR_EN       => false,
         MACS              => 16,
         INBANDFCS      	=> false,
         CNT_ERROR_SIZE    => 5,
         FL_WIDTH_TX       => DATA_WIDTH,
         FL_RELAY          => false
      )
      port map (
         RESET             => RESET_IBUF,
         XGMII_RXCLK       => XGMII_CLK,
         -- XGMII Receive Data
         XGMII_RXD         => XGMII_D,
         -- XGMII Receive Control
         XGMII_RXC         => XGMII_C,

         -- Internal clock
         -- Clock for SAU component
         INT_CLK           => open,
         INT_RESET         => open,

         -- Sampling unit interface
         -- Request for sampling information
         SAU_REQ           => open,
         -- Accept incoming frame
         SAU_ACCEPT        => '1',
         -- Sampling information valid
         SAU_DV            => '1',

         -- Control data generator interface
         -- PACODAG_CLOCK
         CTRL_CLK          => CTRL_CLK,
         CTRL_RESET        => CTRL_RESET,
         -- Control data
         CTRL_DATA         => CTRL_DI,
         -- Specifies the number of valid bytes in the last CTRL_DATA beat;
         -- valid only when CTRL_EOP is asserted
         CTRL_REM          => CTRL_REM,
         -- Asserted when the input signals from control data generator are valid
         CTRL_SRC_RDY_N    => CTRL_SRC_RDY_N,
         -- Signals the start of the incoming control data
         CTRL_SOP_N        => CTRL_SOP_N,
         -- Signals the end of the incoming control data
         CTRL_EOP_N        => CTRL_EOP_N,
         -- Asserted when data from control data generator will be accepted
         CTRL_DST_RDY_N    => CTRL_DST_RDY_N,
         -- New frame is being received; prepare to generate new control data
         CTRL_REQ          => SOP,
         -- Send control data
         CTRL_SEND         => STAT_DV,
         -- Discard control data
         CTRL_RELEASE      => open,
         -- Control data generator is ready to receive new request
         CTRL_RDY          => CTRL_RDY,

         -- Statistic data, active in '1'
         STAT              => STAT,
         -- Statistic is valid
         STAT_VLD          => open,

         -- State of the link signals
         -- Active when link is up
         LINK_UP        => open,
         -- Active when a packet is being received
         INCOMING_PCKT  => open,

         -- Output FrameLink inteface
         TX_SOF_N          => TX_SOF_N,
         TX_SOP_N          => TX_SOP_N,
         TX_EOP_N          => TX_EOP_N,
         TX_EOF_N          => TX_EOF_N,
         TX_SRC_RDY_N      => TX_SRC_RDY_N,
         TX_DST_RDY_N      => TX_DST_RDY_N,
         TX_DATA           => TX_DATA,
         TX_REM            => TX_REM,
         -- Clock for FrameLink interface. Might be asynchronous to IBUF clock
         FL_CLK            => CLK,

         -- MI32 interface
         MI                => mi320,
         -- Clock for MI32 interface
         MI_CLK            => CLK
      );

--MI320.ARDY <= MI320.RD or MI320.WR;
--MI321.ARDY <= MI321.RD or MI321.WR;

   pckt_cnt: process(CTRL_RESET, CTRL_CLK)
   begin
      if (CTRL_RESET = '1') then
         cnt_packet <= (others => '0');
      else
         if (CTRL_CLK'event and CTRL_CLK = '1') then
	    if (cnt_packet_we = '1') then
	       cnt_packet <= cnt_packet + 1;
	    end if;
	 end if;
      end if;
   end process;
   
   reg_payload_len_we   <= STAT_DV;

   -- STORE all wanted STATs --------------------------------------------------
   process(CTRL_RESET, CTRL_CLK)
   begin
      if (CTRL_RESET = '1') then
         reg_payload_len <= (others => '0');
         reg_FRAME_ERROR <= '0';
	 reg_CRC_CHECK_FAILED <= '0';
	 reg_MAC_CHECK_FAILED <= '0';
	 reg_LEN_BELOW_MIN <= '0';
	 reg_LEN_OVER_MTU <= '0';
      elsif (CTRL_CLK'event AND CTRL_CLK = '1') then
         if (reg_payload_len_we = '1') then
            reg_payload_len <= STAT.PAYLOAD_LEN;
	    reg_FRAME_ERROR <= STAT.FRAME_ERROR;
	    reg_CRC_CHECK_FAILED <= STAT.CRC_CHECK_FAILED;
	    reg_MAC_CHECK_FAILED <= STAT.MAC_CHECK_FAILED;
	    reg_LEN_BELOW_MIN <= STAT.LEN_BELOW_MIN;
	    reg_LEN_OVER_MTU <= STAT.LEN_OVER_MTU;
         end if;
      end if;
   end process;
   
   gen16: if DATA_WIDTH = 16 generate
      -- FSM present state register ----------------------------------------------
      sync_logic : process(CTRL_RESET, CTRL_CLK)
      begin
         if (CTRL_RESET = '1') then
            present_state <= S_IDLE;
         elsif (CTRL_CLK'event AND CTRL_CLK = '1') then
            present_state <= next_state;
         end if;
      end process sync_logic;
   
      -- FSM next state logic ----------------------------------------------------
      next_state_logic : process(present_state, SOP, CTRL_DST_RDY_N, STAT_DV)
      begin
         case present_state is
   
            -- -----------------------------------------
            when S_IDLE => 
               if (SOP = '1') then
                  next_state <= S_WAIT_FOR_VALID;
               else
                  next_state <= S_IDLE;
               end if;

            -- -----------------------------------------
            when S_WAIT_FOR_VALID => 
               if (STAT_DV = '1') then
                  next_state <= S_WORD1;
               else
                  -- NOTE: We don't generate any data when another SOP arrives
                  next_state <= S_WAIT_FOR_VALID;
               end if;

            -- -----------------------------------------
            when S_WORD1 => 
               if (CTRL_DST_RDY_N = '0') then
                  next_state <= S_WORD2;
               else
                  next_state <= S_WORD1;
               end if;

            -- -----------------------------------------
            when S_WORD2 => 
               if (CTRL_DST_RDY_N = '0') then
                  next_state <= S_IDLE;
               else
                  next_state <= S_WORD2;
               end if;

            -- -----------------------------------------
            when others =>
               next_state <= S_IDLE;
         end case;
      end process next_state_logic;
   
      -- FSM output logic---------------------------------------------------------
      output_logic : process(present_state, STAT_DV, reg_payload_len, reg_FRAME_ERROR, reg_CRC_CHECK_FAILED,  reg_MAC_CHECK_FAILED,  reg_LEN_BELOW_MIN, reg_LEN_OVER_MTU, cnt_packet, CTRL_DST_RDY_N)
      begin
   
         CTRL_DI       <= (others => '0');
         CTRL_REM        <= (others => '0');
         CTRL_SRC_RDY_N  <= '1';
         CTRL_SOP_N      <= '1';
         CTRL_EOP_N      <= '1';
         CTRL_RDY        <= '0';
         cnt_packet_we   <= '0';
	 
         case present_state is
   
            when S_IDLE =>
               CTRL_RDY <= '1';

            when S_WAIT_FOR_VALID =>
               CTRL_RDY <= '1';

            -- -----------------------------------------
            when S_WORD1 => 
               CTRL_DI(15 downto 0)  <= reg_payload_len(15 downto 0);  
               CTRL_REM        <= (others=>'1');
               CTRL_SRC_RDY_N  <= '0';
               CTRL_SOP_N      <= '0';
   
            -- -----------------------------------------
            when S_WORD2 => 
               CTRL_DI(0)  <= reg_FRAME_ERROR;
	       CTRL_DI(1)  <= reg_CRC_CHECK_FAILED;
	       CTRL_DI(2)  <= reg_MAC_CHECK_FAILED;
	       CTRL_DI(3)  <= reg_LEN_BELOW_MIN;
	       CTRL_DI(4)  <= reg_LEN_OVER_MTU;
	       CTRL_DI(15 downto 5) <= cnt_packet;
               CTRL_REM        <= (others=>'1');
               CTRL_SRC_RDY_N  <= '0';
               CTRL_EOP_N      <= '0';
	       if (CTRL_DST_RDY_N = '0') then
                  cnt_packet_we   <= '1';
	       end if;
            -- -----------------------------------------
            when others =>
         end case;
      end process output_logic;
   end generate;
   
   genelse: if DATA_WIDTH /= 16 generate
      -- FSM present state register ----------------------------------------------
   sync_logic : process(CTRL_RESET, CTRL_CLK)
   begin
      if (CTRL_CLK'event AND CTRL_CLK = '1') then
         if (CTRL_RESET = '1') then
            present_state <= S_IDLE;
         else
            present_state <= next_state;
         end if;
      end if;
   end process sync_logic;
   
   -- FSM next state logic ----------------------------------------------------
   next_state_logic : process(present_state, SOP, STAT_DV, CTRL_DST_RDY_N)
   begin
      case present_state is
   
         -- -----------------------------------------
         when S_IDLE => 
            if (SOP = '1') then
               next_state <= S_WAIT_FOR_VALID;
            else
               next_state <= S_IDLE;
            end if;

          -- -----------------------------------------
         when S_WAIT_FOR_VALID => 
            if (STAT_DV = '1') then
               next_state <= S_WORD1;
            else
               next_state <= S_WAIT_FOR_VALID;
            end if;

         -- -----------------------------------------
         when S_WORD1 => 
            if (CTRL_DST_RDY_N = '0') then
               next_state <= S_IDLE;
            else
               next_state <= S_WORD1;
            end if;

         -- -----------------------------------------
         when others =>
            next_state <= S_IDLE;
      end case;
   end process next_state_logic;

   CTRL_REM        <= conv_std_logic_vector(3,log2(DATA_PATHS));
   CTRL_DI(15 downto 0)  <= reg_payload_len(15 downto 0);
   CTRL_DI(16)  <= reg_FRAME_ERROR;
   CTRL_DI(17)  <= reg_CRC_CHECK_FAILED;
   CTRL_DI(18)  <= reg_MAC_CHECK_FAILED;
   CTRL_DI(19)  <= reg_LEN_BELOW_MIN;
   CTRL_DI(20)  <= reg_LEN_OVER_MTU;
   CTRL_DI(31 downto 21) <= cnt_packet;

   -- FSM output logic---------------------------------------------------------
   output_logic : process( present_state, CTRL_DST_RDY_N)
   begin
      CTRL_RDY        <= '0' after 1ps;
      CTRL_SRC_RDY_N  <= '1' after 1ps;
      CTRL_SOP_N      <= '1' after 1ps;
      CTRL_EOP_N      <= '1' after 1ps;
       cnt_packet_we  <= '0' after 1ps;
      case present_state is

         when S_IDLE =>
            CTRL_RDY <= '1' after 1ps;

         when S_WAIT_FOR_VALID =>
            CTRL_RDY <= '1' after 1ps;

         -- -----------------------------------------
         when S_WORD1 =>
            CTRL_SRC_RDY_N  <= '0' after 1ps;
            CTRL_RDY        <= '0' after 1ps;
            CTRL_SOP_N      <= '0' after 1ps;
	    CTRL_EOP_N      <= '0' after 1ps;
	    if (CTRL_DST_RDY_N = '0') then
               cnt_packet_we   <= '1' after 1ps;
	    end if;
         -- -----------------------------------------
         when others => null;
      end case;
   end process output_logic;
   end generate;

MI32_SIM0_U : entity work.MI32_SIM
   generic map (
      UPSTREAM_LOG_FILE   => "ib_upstream_log0.txt",
      DOWNSTREAM_LOG_FILE => "ib_downstream_log0.txt",
      BASE_ADDR           => X"00001000",
      LIMIT               => X"00000100",
      FREQUENCY           => LOCAL_BUS_FREQUENCY,
      BUFFER_EN           => false
   )
   port map (
      -- Common interface
      IB_RESET           => reset,
      IB_CLK             => clk,

      -- User Component Interface
      CLK                => clk,
      MI32               => mi320,

      -- IB SIM interface
      CTRL               => ib_sim_ctrl0,
      STROBE             => ib_sim_strobe0,
      BUSY               => ib_sim_busy0
      );
   
MI32_SIM1_U : entity work.MI32_SIM
   generic map (
      UPSTREAM_LOG_FILE   => "ib_upstream_log1.txt",
      DOWNSTREAM_LOG_FILE => "ib_downstream_log1.txt",
      BASE_ADDR           => X"00002000",
      LIMIT               => X"00000100",
      FREQUENCY           => LOCAL_BUS_FREQUENCY,
      BUFFER_EN           => false
   )
   port map (
      -- Common interface
      IB_RESET           => reset,
      IB_CLK             => clk,

      -- User Component Interface
      CLK                => clk,
      MI32               => mi321,

      -- IB SIM interface
      CTRL               => ib_sim_ctrl1,
      STROBE             => ib_sim_strobe1,
      BUSY               => ib_sim_busy1
      );
      
      
      tb : process
-- ----------------------------------------------------------------------------
--                                 Procedures declaration
-- ----------------------------------------------------------------------------
-- ----------------------------------------------------------------------------
-- Support for ib_op
procedure ib_op0(ctrl : in t_ib_ctrl) is
begin
   wait until (CLK'event and CLK='1' and ib_sim_busy0 = '0');
   ib_sim_ctrl0 <= ctrl;
   ib_sim_strobe0 <= '1';
   wait until (CLK'event and CLK='1');
   ib_sim_strobe0 <= '0';
end ib_op0;

procedure ib_op1(ctrl : in t_ib_ctrl) is
begin
   wait until (CLK'event and CLK='1' and ib_sim_busy1 = '0');
   ib_sim_ctrl1 <= ctrl;
   ib_sim_strobe1 <= '1';
   wait until (CLK'event and CLK='1');
   ib_sim_strobe1 <= '0';
end ib_op1;

-- start testing ---------------------------------------------------------------
begin

   -- Testbench
   wait for 10000 ns;
   ib_op0(ib_local_write(X"00001020", X"00000000", 4, 16#ABAB#, '0', X"0000000000000001"));
   ib_op1(ib_local_write(X"00002020", X"00000000", 4, 16#ABAB#, '0', X"0000000000000001"));
   wait;
end process;

end architecture full;
