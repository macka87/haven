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
      DATA_WIDTH : integer := 16
   );
   port(
      -- common signals
      -- global FGPA clock
      CLK            : in  std_logic;
      CLK_125        : in  std_logic;

      -- global synchronous reset
      RESET          : in  std_logic;

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
   signal D              : std_logic_vector(7 downto 0);
   signal EN             : std_logic;
   signal ER             : std_logic;
   signal GCLK           : std_logic;
   
   constant DATA_PATHS : integer := DATA_WIDTH/8;
   -- PACODAG interface
   signal CTRL_CLK       : std_logic; -- out
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

obuf: entity work.obuf_gmii 
   generic map(
      DATA_PATHS => DATA_WIDTH / 8,
      DFIFO_SIZE  => 4096,
      SFIFO_SIZE  => 128
   )
   port map(
      RESET      => RESET,

      -- FrameLink input interface
      WRCLK      => CLK,
      DATA       => RX_DATA,
      DREM       => RX_REM,
      SRC_RDY_N  => RX_SRC_RDY_N,
      SOF_N      => RX_SOF_N,
      SOP_N      => RX_SOP_N,
      EOF_N      => RX_EOF_N,
      EOP_N      => RX_EOP_N,
      DST_RDY_N  => RX_DST_RDY_N,

      -- transmit gmii interface
      REFCLK     => CLK_125,
      TXCLK      => GCLK,
      TXD	 => D,
      TXEN	 => EN,
      TXER	 => ER,

      -- PHY status interface
      LINK_STATUS       => '1',  -- 0: link down, 1: link up
      DUPLEX_MODE       => '1',  -- 0: half duplex, 1: full duplex
      SPEED             => "10", -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
      SGMII             => '1',  -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
                                 -- 1: SGMII mode active, the PHY status ports are valid
      -- address decoder interface
      ADC_CLK    => open,
      ADC_RD     => MI320.RD,
      ADC_WR     => MI320.WR,
      ADC_ADDR   => MI320.ADDR(7 downto 2),
      ADC_DI     => MI320.DWR,
      ADC_DO     => MI320.DRD,
      ADC_DRDY   => MI320.DRDY
   );
   
ibuf:entity work.ibuf_gmii 
   generic map(
      DATA_PATHS  => DATA_WIDTH / 8,
      DFIFO_SIZE  => 4096,
      HFIFO_SIZE  => 128,
      CTRL_HDR_EN => true,
      CTRL_FTR_EN => false
   )
   port map(
      RESET     => RESET,

      -- GMII RX interface
      RXCLK     => GCLK,
      RXD       => D,
      RXDV      => EN,
      RXER      => ER,

      -- PHY status interface
      -- PHY status interface
      LINK_STATUS       => '1',  -- 0: link down, 1: link up
      DUPLEX_MODE       => '1',  -- 0: half duplex, 1: full duplex
      SPEED             => "10", -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
      SGMII             => '1',  -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
                                 -- 1: SGMII mode active, the PHY status ports are valid
      -- PACODAG interface
      CTRL_CLK       => CTRL_CLK,
      CTRL_DI        => CTRL_DI,
      CTRL_REM       => CTRL_REM,
      CTRL_SRC_RDY_N => CTRL_SRC_RDY_N,
      CTRL_SOP_N     => CTRL_SOP_N,
      CTRL_EOP_N     => CTRL_EOP_N,
      CTRL_DST_RDY_N => CTRL_DST_RDY_N,
      CTRL_RDY       => CTRL_RDY,
      
      -- IBUF status interface
      SOP            => SOP,
      STAT           => STAT,
      STAT_DV        => STAT_DV,

      -- Sampling unit interface
      SAU_ACCEPT => '1',
      SAU_DV     => '1',

      -- FrameLink interface
      RDCLK      => CLK,
      DATA       => TX_DATA,
      DREM       => TX_REM,
      SRC_RDY_N  => TX_SRC_RDY_N,
      SOF_N      => TX_SOF_N,
      SOP_N      => TX_SOP_N,
      EOF_N      => TX_EOF_N,
      EOP_N      => TX_EOP_N,
      DST_RDY_N  => TX_DST_RDY_N,

      -- address decoder interface
      ADC_CLK    => open,
      ADC_RD     => MI321.RD,
      ADC_WR     => MI321.WR,
      ADC_ADDR   => MI321.ADDR(7 downto 2),
      ADC_DI     => MI321.DWR,
      ADC_DO     => MI321.DRD,
      ADC_DRDY   => MI321.DRDY
   );
   
MI320.ARDY <= MI320.RD or MI320.WR;
MI321.ARDY <= MI321.RD or MI321.WR;

   pckt_cnt: process(RESET, CTRL_CLK)
   begin
      if (RESET = '1') then
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
   process(RESET, CTRL_CLK)
   begin
      if (RESET = '1') then
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
      sync_logic : process(RESET, CTRL_CLK)
      begin
         if (RESET = '1') then
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
   sync_logic : process(RESET, CTRL_CLK)
   begin
      if (CTRL_CLK'event AND CTRL_CLK = '1') then
         if (RESET = '1') then
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
   
   -- FSM output logic---------------------------------------------------------
   output_logic : process( present_state, reg_payload_len, reg_FRAME_ERROR, reg_CRC_CHECK_FAILED,  reg_MAC_CHECK_FAILED,  reg_LEN_BELOW_MIN, reg_LEN_OVER_MTU, cnt_packet, CTRL_DST_RDY_N)
   begin
      CTRL_RDY        <= '0';
      CTRL_SRC_RDY_N  <= '1';
      CTRL_DI       <= (others => '0');
      CTRL_REM        <= (others => '0');
      CTRL_SOP_N      <= '1';
      CTRL_EOP_N      <= '1';
       cnt_packet_we  <= '0';
      case present_state is
   
         when S_IDLE => 
            CTRL_RDY <= '1';

         when S_WAIT_FOR_VALID =>
            CTRL_RDY <= '1';

         -- -----------------------------------------
         when S_WORD1 => 
            CTRL_SRC_RDY_N  <= '0';
            CTRL_RDY        <= '0';
            CTRL_SOP_N      <= '0';
	    CTRL_EOP_N      <= '0';
	    CTRL_REM        <= conv_std_logic_vector(3,log2(DATA_PATHS));
	    CTRL_DI(15 downto 0)  <= reg_payload_len(15 downto 0);  
	    CTRL_DI(16)  <= reg_FRAME_ERROR;
	    CTRL_DI(17)  <= reg_CRC_CHECK_FAILED;
	    CTRL_DI(18)  <= reg_MAC_CHECK_FAILED;
	    CTRL_DI(19)  <= reg_LEN_BELOW_MIN;
	    CTRL_DI(20)  <= reg_LEN_OVER_MTU;
	    CTRL_DI(31 downto 21) <= cnt_packet;
	    if (CTRL_DST_RDY_N = '0') then
               cnt_packet_we   <= '1';
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
      FREQUENCY           => 100,
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
      FREQUENCY           => 100,
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
   wait for 100 ns;
   ib_op0(ib_local_write(X"00001020", X"00000000", 4, 16#ABAB#, '0', X"0000000000000001"));
   ib_op1(ib_local_write(X"00002020", X"00000000", 4, 16#ABAB#, '0', X"0000000000000001"));
   wait;
end process;

end architecture full;
