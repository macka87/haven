--
-- obuf_gmii_buf.vhd: Output buffer for GMII - buffer part
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
--            Libor Polcak <polcak_l@liberouter.org>
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
-- - connect cnt_notsent correctly, now is allways 0
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on

use work.cnt_types.all;
use work.math_pack.all;
use work.obuf_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_gmii_buf is
   generic(
      --ADDR_WIDTH : integer := 4;

      DATA_PATHS : integer;
      DFIFO_SIZE : integer;
      SFIFO_SIZE : integer;

      CTRL_CMD   : boolean

   );
   port(
      RESET   : in  std_logic;

      -- obuf_gmii_cmd interface
      WR_CLK          : in  std_logic;

      DFIFO_DI       : in  std_logic_vector((DATA_PATHS*9-1) downto 0);
      DFIFO_WR       : in  std_logic;
      DFIFO_FULL     : out std_logic;
 
      SFIFO_DI       : in  std_logic_vector(1 downto 0);
      SFIFO_WR       : in  std_logic;
      SFIFO_FULL     : out std_logic;

      -- obuf_gmii_tx interface
      TX_CLK         : in  std_logic;
      TX_DO          : out std_logic_vector(7 downto 0);
      TX_DV          : out std_logic;
      TX_ER          : out std_logic;
      TX_BUSY        : in  std_logic;
      SGMII_DV_P     : out std_logic;

      -- PHY status interface
      LINK_STATUS       : in std_logic; -- 0: link down, 1: link up
      DUPLEX_MODE       : in std_logic; -- 0: half duplex, 1: full duplex
      SPEED             : in std_logic_vector(1 downto 0); -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
      SGMII             : in std_logic; -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
                                             -- 1: SGMII mode active, the PHY status ports are valid
      -- Address decoder interface
      ADC_CLK     : out std_logic;
      ADC_RD      : in  std_logic; -- Read Request
      ADC_WR      : in  std_logic; -- Write Request
      ADC_ADDR    : in  std_logic_vector(3  downto 0);  -- Address
      ADC_DI      : in  std_logic_vector(31 downto 0); -- Input Data
      ADC_DO      : out std_logic_vector(31 downto 0);  -- Output Data
      ADC_DRDY    : out std_logic
   );
end entity obuf_gmii_buf;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_gmii_buf is

   signal dfifo_do     : std_logic_vector(DATA_PATHS*9-1 downto 0);
   signal dfifo_do_i   : std_logic_vector(DATA_PATHS*9-1 downto 0);
   signal dfifo_do_dv  : std_logic;
   signal dfifo_rd     : std_logic;
   signal dfifo_full_i     : std_logic;
   
   signal sfifo_rd     : std_logic;
   signal sfifo_do     : std_logic_vector(1 downto 0);
   signal sfifo_empty  : std_logic;
   signal sfifo_full_i     : std_logic;
   
   signal eop          : std_logic;
   signal store        : std_logic;
   signal last_word    : std_logic;
   signal fsm_disable  : std_logic;

   signal cnt_packets  : std_logic_vector(63 downto 0);
   signal cnt_sent     : std_logic_vector(63 downto 0);
   signal cnt_sent_ce : std_logic;
   signal cnt_notsent  : std_logic_vector(63 downto 0);
   signal cnt_notsent_ce : std_logic;
   signal reg_enable   : std_logic;
   signal reg_obuf_status  : std_logic_vector(7 downto 0);
   
   signal reg_cnt_packets  : std_logic_vector(63 downto 0);
   signal reg_cnt_sent     : std_logic_vector(63 downto 0);
   signal reg_cnt_notsent  : std_logic_vector(63 downto 0);
   signal reset_counters   : std_logic;
   signal reg_cnts_ce      : std_logic;

   signal cs_cnt_packets_l : std_logic;
   signal cs_cnt_packets_h : std_logic;
   signal cs_cnt_sent_l    : std_logic;
   signal cs_cnt_sent_h    : std_logic;
   signal cs_cnt_notsent_l : std_logic;
   signal cs_cnt_notsent_h : std_logic;
   signal cs_reg_enable  : std_logic;
   signal cs_reg_mac     : std_logic_vector(1 downto 0);
   signal cs_reg_obuf_ctrl : std_logic;
   signal cs_reg_obuf_status : std_logic;

   type t_mux is array (0 to DATA_PATHS) of std_logic_vector(8 downto 0);

   signal reg_do       : t_mux;
   signal cnt_mac : std_logic_vector(3 downto 0);
   signal cnt_mac_load : std_logic;
   signal cnt_mac_ce : std_logic;
   signal reg_replc_mac : std_logic;
   signal reg_replc_mac_rst : std_logic;
   signal reg_replc_mac_set : std_logic;
   signal reg_mac : std_logic_vector(47 downto 0);
   signal reg_mac_we : std_logic_vector(1 downto 0);
   signal tx_do_mx   : std_logic_vector(7 downto 0);
   signal replace_mac : std_logic;
   
   -- Command comparators
   signal strobe_counters_c : std_logic;
   signal reset_counters_c  : std_logic;
   signal set_speed10_c     : std_logic;
   signal set_speed100_c    : std_logic;
   signal set_speed1000_c   : std_logic;
   
   signal reg_speed         : std_logic_vector(1 downto 0);
   signal sgmii_dv : std_logic;
   signal cnt_sgmii_ovf_10 : std_logic;
   signal cnt_sgmii_ovf_100 : std_logic;
   signal cnt_sgmii_ovf : std_logic;
   signal cnt_sgmii_ce : std_logic;
   signal cnt_sgmii_load : std_logic;
   signal cnt_sgmii : std_logic_vector(6 downto 0);
   signal shift : std_logic;
   
begin
   
   -- ADRESS DECODER ----------------------------------------------------------
   ADC_CLK <= TX_CLK;
   
   cs_cnt_packets_l <= '1' when (ADC_ADDR="0000") else '0';   -- 00
   cs_cnt_packets_h <= '1' when (ADC_ADDR="0100") else '0';   -- 10
   cs_cnt_sent_l    <= '1' when (ADC_ADDR="0001") else '0';   -- 04
   cs_cnt_sent_h    <= '1' when (ADC_ADDR="0101") else '0';   -- 14
   cs_cnt_notsent_l <= '1' when (ADC_ADDR="0010") else '0';   -- 08
   cs_cnt_notsent_h <= '1' when (ADC_ADDR="0110") else '0';   -- 18
   
   cs_reg_enable  <= '1' when (ADC_ADDR="1000") else '0';   -- 20
   cs_reg_mac(0)  <= '1' when (ADC_ADDR="1001") else '0';   -- 24
   cs_reg_mac(1)  <= '1' when (ADC_ADDR="1010") else '0';   -- 28
   cs_reg_obuf_ctrl   <= '1' when (ADC_ADDR="1011") else '0'; -- 2C
   cs_reg_obuf_status <= '1' when (ADC_ADDR="1100") else '0'; -- 30

   ADC_DO  <= X"0000000" & "000" & reg_enable when (cs_reg_enable='1')  else --enable
              reg_cnt_packets(31 downto 0)    when (cs_cnt_packets_l='1') else --cnt_packets
              reg_cnt_packets(63 downto 32)   when (cs_cnt_packets_h='1') else --cnt_packets
              reg_cnt_sent(31 downto 0)       when (cs_cnt_sent_l='1')    else --cnt_sent
              reg_cnt_sent(63 downto 32)      when (cs_cnt_sent_h='1')    else --cnt_sent
              reg_cnt_notsent(31 downto 0)    when (cs_cnt_notsent_l='1') else --cnt_notsent
              reg_cnt_notsent(63 downto 32)   when (cs_cnt_notsent_h='1') else --cnt_notsent
              reg_mac(31 downto 0)            when (cs_reg_mac(0)='1')  else --reg_mac
              X"0000" & reg_mac(47 downto 32) when (cs_reg_mac(1)='1')  else --reg_mac
              X"000000" & reg_obuf_status     when (cs_reg_obuf_status='1') else -- obuf_status
	      (others=>'0');

   cnt_reg_p: process (TX_CLK, RESET)
   begin
      if (RESET='1') then
         reg_cnt_packets <= (others=>'0');
         reg_cnt_sent    <= (others=>'0');
         reg_cnt_notsent <= (others=>'0');
         ADC_DRDY        <= '0';
      elsif (TX_CLK'event and TX_CLK='1') then
         ADC_DRDY        <= ADC_RD; -- drdy is delayed adc_rd
         if (reg_cnts_ce = '1') then
            reg_cnt_packets <= cnt_packets;
            reg_cnt_sent    <= cnt_sent;
            reg_cnt_notsent <= cnt_notsent;
         end if;
      end if;
   end process;

   -- enable register ---------------------------------------------------------
   reg_enable_p: process (RESET, TX_CLK)
   begin
      if (RESET='1') then
         reg_enable <= '1';
      elsif (TX_CLK'event and TX_CLK='1') then
         if (ADC_WR='1' and cs_reg_enable='1') then
            reg_enable <= ADC_DI(0);
         end if;
      end if;
   end process;

   -- OBUF status register
   process (RESET, TX_CLK)
   begin
      if (RESET='1') then
         reg_obuf_status <= (7 => '0', others=>'0');
      elsif (TX_CLK'event and TX_CLK='1') then
         reg_obuf_status(0) <= dfifo_full_i;
         reg_obuf_status(1) <= sfifo_full_i;
         reg_obuf_status(5 downto 4) <= reg_speed;
      end if;
   end process;

   -- control register
   strobe_counters_c <= '1' when (ADC_DI(7 downto 0) = OBUFCMD_STROBE_COUNTERS) and (cs_reg_obuf_ctrl = '1') and (ADC_WR = '1') else
                        '0';
   reset_counters_c  <= '1' when (ADC_DI(7 downto 0) = OBUFCMD_RESET_COUNTERS) and (cs_reg_obuf_ctrl = '1') and (ADC_WR = '1')  else
                        '0';
   set_speed10_c     <= '1' when (ADC_DI(7 downto 0) = OBUFCMD_SET_SPEED10) and (cs_reg_obuf_ctrl = '1') and (ADC_WR = '1')  else
                        '0';
   set_speed100_c    <= '1' when (ADC_DI(7 downto 0) = OBUFCMD_SET_SPEED100) and (cs_reg_obuf_ctrl = '1') and (ADC_WR = '1')  else
                        '0';
   set_speed1000_c   <= '1' when (ADC_DI(7 downto 0) = OBUFCMD_SET_SPEED1000) and (cs_reg_obuf_ctrl = '1') and (ADC_WR = '1')  else
                        '0';

   -- -------------------------------------------------------------
   -- Speed settings
   -- -------------------------------------------------------------
   process(RESET, TX_CLK)
   begin
      if (RESET = '1') then
         reg_speed <= "10";  -- 1000Mb as a default
      elsif (TX_CLK'event AND TX_CLK = '1') then
         if (set_speed10_c = '1' or set_speed100_c = '1' or set_speed1000_c = '1') then
            reg_speed <= ADC_DI(1 downto 0);
         end if;
      end if;
   end process;
   
   -- -------------------------------------------------------------
   -- Packet counters
   -- -------------------------------------------------------------
   
   reset_counters <= RESET or reset_counters_c;
   -- all packets counter
   cnt_packets_u : entity work.cnt
   generic map(
      WIDTH => 64,
      DIR   => up,
      CLEAR => false
   )
   port map(
      RESET => reset_counters,
      CLK   => WR_CLK,
      DO    => cnt_packets,
      CLR   => '0',
      CE    => SFIFO_WR --fixme
   );

    -- sent packets counter 
   cnt_sent_u : entity work.cnt
   generic map(
      WIDTH => 64,
      DIR   => up,
      CLEAR => false
   )
   port map(
      RESET => reset_counters,
      CLK   => TX_CLK,
      DO    => cnt_sent,
      CLR   => '0',
      CE    => cnt_sent_ce
   );

    -- not sent packets counter 
   cnt_notsent_u : entity work.cnt
   generic map(
      WIDTH => 64,
      DIR   => up,
      CLEAR => false
   )
   port map(
      RESET => reset_counters,
      CLK   => TX_CLK,
      DO    => cnt_notsent,
      CLR   => '0',
      CE    => cnt_notsent_ce
   );

   -- strobe counters registers
   process (RESET, TX_CLK)
   begin
      if (RESET='1') then
         reg_cnts_ce <= '0';
      elsif (TX_CLK'event and TX_CLK='1') then
         if (strobe_counters_c='1') then
            reg_cnts_ce <= '1';
         else
            reg_cnts_ce <= '0';
         end if;
      end if;
   end process;

   ----------------------------------------------------------------------------
   -- DFIFO instatination
   DFIFO_U : entity work.asfifo_bram
   generic map(
      ITEMS        => DFIFO_SIZE,
      BRAM_TYPE    => 0, -- 0 denotes auto computation of best type
      DATA_WIDTH   => DATA_PATHS*9,
      STATUS_WIDTH => 1
   )
   port map(
      RESET    => reset,
   
      -- Write interface
      CLK_WR   => WR_CLK,
      WR       => DFIFO_WR,
      DI       => DFIFO_DI,
      FULL     => dfifo_full_i,
      STATUS   => open,
   
      -- Read interface
      CLK_RD   => TX_CLK,
      RD       => dfifo_rd,
      DO       => dfifo_do_i,
      DO_DV    => dfifo_do_dv,
      EMPTY    => open
   );
   DFIFO_FULL <= dfifo_full_i;

   -- In case of eop the data valid bits are inverted
   dfifo_do((DATA_PATHS*8)-1 downto 0) <= dfifo_do_i((DATA_PATHS*8)-1 downto 0);
   dfifo_do_gen: for i in 0 to DATA_PATHS-1 generate
      dfifo_do((DATA_PATHS*8)+i) <= dfifo_do_i((DATA_PATHS*8)+i) xor eop;
   end generate;
   
   -- SFIFO instatination -----------------------------------------------------
   SFIFO_U : entity work.asfifo
   generic map (
      ITEMS        => SFIFO_SIZE,
      DISTMEM_TYPE => 16,
      DATA_WIDTH   => 2,
      STATUS_WIDTH => 1
   )
   port map(
      RESET    => reset,
   
      -- Write interface
      CLK_WR   => WR_CLK,
      WR       => SFIFO_WR,
      DI       => SFIFO_DI,
      FULL     => sfifo_full_i,
      STATUS   => open,
   
      -- Read interface
      CLK_RD   => TX_CLK,
      RD       => sfifo_rd,
      DO       => sfifo_do,
      EMPTY    => sfifo_empty
   );
   SFIFO_FULL <= sfifo_full_i;

   -- eop comparator ----------------------------------------------------------
   -- eop = '1' when one or more dfifo_do bits are deasserted
   -- (it means that this is last data)
   eop_p: process(dfifo_do)
   begin
      eop <= '0';
      for i in 0 to DATA_PATHS-1 loop
	 if (dfifo_do_i(DATA_PATHS*8+i)='0') then
	    eop <= '1';
	 end if;
      end loop;
   end process;
   
   -- FSM instantination ---------------------------------------------------
   BUF_FSM_U : entity work.obuf_gmii_buf_fsm
   generic map (
      DATA_PATHS   => DATA_PATHS
   )
   port map (
      RESET        => RESET,
      CLK          => TX_CLK,
      BUSY         => fsm_disable,
      LAST_WORD    => last_word,
      DATA_DV      => dfifo_do_dv,
      EOP          => eop,
      STATUS_EMPTY => sfifo_empty,      
      SGMII_DV     => sgmii_dv,
      
      DATA_RD      => dfifo_rd,
      STATUS_RD    => sfifo_rd,
      STORE        => store,
      SHIFT        => shift
   );
      
   fsm_disable <= TX_BUSY or (not reg_enable);
   -- NOTE: case of one data path is solved in FSM, we don't need to compute
   --       last_word signal
   
   reg_do(DATA_PATHS) <= (others=>'0'); -- we will shift zeros for determine last word

   ------------------------- more paths ---------------------------------------
   gen_last_word_more_paths : if (DATA_PATHS>1) generate
      last_word <= not reg_do(2)(8);
   end generate;

   --reg_do_last_p : process (RESET, TX_CLK)
--	begin-
--	   if (RESET='1') then
	--      reg_do(DATA_PATHS-1) <= (others=>'0');
	--   elsif (TX_CLK'event and TX_CLK='1') then
	--      if (store='1') then
	--         -- control (dv) bit is asserted only when sfifo_do = '1' (valid packet)
        --         reg_do(DATA_PATHS-1) <= (dfifo_do(DATA_PATHS*8+DATA_PATHS-1) and sfifo_do(0)) &
	--	                         dfifo_do(DATA_PATHS*8-1 downto (DATA_PATHS-1)*8);
	--      else
	--         reg_do(DATA_PATHS-1) <= (others=>'0');
	--      end if;
	--   end if;
	--end process;

   gen_reg_do : for i in 0 to DATA_PATHS-1 generate
      reg_do_others_p : process (RESET, TX_CLK)
      begin
         if (RESET='1') then
	         reg_do(i) <= (others=>'0');
	      elsif (TX_CLK'event and TX_CLK='1') then
	         if (store='1') then
               -- control (dv) bit is asserted only when sfifo_do = '1' (valid packet)
               reg_do(i) <= (dfifo_do(DATA_PATHS*8+i) and sfifo_do(0)) & dfifo_do((i+1)*8-1 downto i*8);
            elsif(shift='1') then
               reg_do(i) <= reg_do(i+1);
            end if;
	      end if;
      end process;
   end generate;

   process (RESET, TX_CLK)
   begin
      if (RESET='1') then
         cnt_notsent_ce <= '0';
	   elsif (TX_CLK'event and TX_CLK='1') then
	      if (store='1' and eop='1') then
            cnt_notsent_ce <= not (dfifo_do(DATA_PATHS*8) and sfifo_do(0));
         else
            cnt_notsent_ce <= '0';
         end if;
      end if;
   end process;
            
   process (RESET, TX_CLK)
   begin
      if (RESET='1') then
         cnt_sent_ce <= '0';
	   elsif (TX_CLK'event and TX_CLK='1') then
	      if (store='1' and eop='1') then
            cnt_sent_ce <= dfifo_do(DATA_PATHS*8) and sfifo_do(0);
         else
            cnt_sent_ce <= '0';
         end if;
      end if;
   end process;
            
   -- -------------------------------------------------------------
   -- MAC address replacement
replace_mac <= reg_replc_mac;
   
cnt_mac_load <= eop;
cnt_mac_ce <= sfifo_do(1) and reg_do(0)(8) and SGMII_DV and (not reg_replc_mac_rst);
process(RESET, TX_CLK)
begin
   if (RESET = '1') then
      cnt_mac <= (others => '0');
   elsif (TX_CLK'event AND TX_CLK = '1') then
      if (cnt_mac_load = '1') then
         cnt_mac <= (others => '0');
      elsif (cnt_mac_ce='1') then
         cnt_mac <= cnt_mac + 1;
      end if;
   end if;
end process;


reg_replc_mac_rst <= '1' when cnt_mac = X"B" and SGMII_DV = '1' else
                     '0';

reg_replc_mac_set <= '1' when (cnt_mac = X"5") and SGMII_DV = '1' else
                     '0';

process(RESET, TX_CLK)
begin
   if (RESET = '1') then
      reg_replc_mac <= '0';
   elsif (TX_CLK'event AND TX_CLK = '1') then
      if (reg_replc_mac_rst = '1') then
         reg_replc_mac <= '0';
      elsif (reg_replc_mac_set = '1') then
         reg_replc_mac <= '1';
      end if;
   end if;
end process;


reg_mac_we(0) <= cs_reg_mac(0) and ADC_WR;
reg_mac_we(1) <= cs_reg_mac(1) and ADC_WR;
process(RESET, TX_CLK)
begin
   if (RESET = '1') then
      reg_mac <= (others => '0');
   elsif (TX_CLK'event AND TX_CLK = '1') then
      if (reg_mac_we(0) = '1') then
         reg_mac(31 downto 0) <= ADC_DI;
      end if;
      if (reg_mac_we(1) = '1') then
         reg_mac(47 downto 32) <= ADC_DI(15 Downto 0);
      end if;
   end if;
end process;

tx_do_mx <= reg_do(0)(7 downto 0) when replace_mac = '0' else
            reg_mac(47 downto 40) when cnt_mac = X"6" else
            reg_mac(39 downto 32) when cnt_mac = X"7" else
            reg_mac(31 downto 24) when cnt_mac = X"8" else
            reg_mac(23 downto 16) when cnt_mac = X"9" else
            reg_mac(15 downto 8) when cnt_mac = X"A" else
            reg_mac(7 downto 0);

   -- -------------------------------------------------------------
   -- SGMII logic
   -- -------------------------------------------------------------
   sgmii_dv <= '1' when SGMII = '0' else
               cnt_sgmii_ovf;
   
   cnt_sgmii_ovf_10 <= '1' when cnt_sgmii = "1100011" else
                       '0';
   cnt_sgmii_ovf_100 <= '1' when cnt_sgmii = "0001001" else
                        '0';
   cnt_sgmii_ovf <= cnt_sgmii_ovf_10 when reg_speed = "00" else
                    cnt_sgmii_ovf_100 when reg_speed = "01" else
                    '1'; -- 1000Mb: all data are relevant

-- cnt_sgmii counter : 
cnt_sgmii_ce <= '1';
cnt_sgmii_load <= cnt_sgmii_ovf;
process(RESET, TX_CLK)
begin
   if (RESET = '1') then
      cnt_sgmii <= (others => '0');
   elsif (TX_CLK'event AND TX_CLK = '1') then
      if (cnt_sgmii_load = '1') then
         cnt_sgmii <= "0000000";
      elsif (cnt_sgmii_ce='1') then
         cnt_sgmii <= cnt_sgmii + 1;
      end if;
   end if;
end process;

   -- output signal assignment ------------------------------------------------
   TX_DO <= tx_do_mx;
   TX_DV <= reg_do(0)(8);
   TX_ER <= '0';
   SGMII_DV_P   <= sgmii_dv;

end architecture full;

