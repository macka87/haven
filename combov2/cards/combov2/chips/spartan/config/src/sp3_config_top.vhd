--
-- sp3_config_top.vhd: Top level for FPGA sp3e config design (sp3e -> virtex5)
-- Copyright (C) 2008  CESNET
-- Author: Milan Malich <malich@mail.muni.cz>
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

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

entity sp3_config_top is
    Port ( 
  -- Oscilator (U17)
    CCLK           : in std_logic;
  -- Reset (BT1)
    RESET_N        : in std_logic;
  -- Led
    CLED           : out std_logic_vector( 3 downto 0 );
  -- Virtex 5
    -- Config
    XRCCLK         : out std_logic;
    XDONE          : in std_logic;
    XPROGRAM_N     : out std_logic;
    XM0            : out std_logic;
    XRRDWR_N       : out std_logic;
    XRDIN          : out std_logic;
    XRCS_N         : out std_logic;
    XRDOUT         : in std_logic;
    XINIT_N        : in std_logic;
    --
    XRHSH          : inout std_logic_vector( 11 downto 0 );
    XRD            : out std_logic_vector( 7 downto 0 );
  -- PSRAM & Flash (U13 & U14)
    -- Adress --
    FA             : out std_logic_vector( 25 downto 0 );
    -- Data --
    FD             : in std_logic_vector( 15 downto 0 );
    -- Control --
    FWE_N          : out std_logic;
    FCSFLASH_N     : out std_logic;
    FCSRAM_N       : out std_logic;
    FOE_N          : out std_logic;
    FBYTE_N        : out std_logic;
    FRY            : inout std_logic;
    FLB_N          : out std_logic;     
    FUB_N          : out std_logic;
    FZZ_N          : out std_logic 
    );
end sp3_config_top;

architecture behavioral of sp3_config_top is
  -- DCM Setting
  -- Input CCLK is 100Mhz (10ns period)
  -- Output DCM is 100Mhz (10ns period)
  constant CLK_DIVIDE : integer := 2;
  constant CLK_MULTIPLY : integer := 2;
  
  -- Timing is ( datasheet_value(ns) / 10 )
  -- Virtex5 Timing
  constant T_PROG : integer := 300;
  -- Flash Memory Timing
  constant T_ACC : integer := 11;
  constant T_PACC : integer := 4;
  
  --
  constant PROG_B_PULSE_WIDTH : integer := T_PROG;
  constant LATENCY_COMP : integer := 2;
  constant NORMAL_MODE_ACCESS_CYCLE : integer := T_ACC - LATENCY_COMP;
  constant PAGE_MODE_ACCESS_TIME : integer := T_PACC - LATENCY_COMP;
  constant FIRST_CLK_LOW : integer := 5;
  constant FIRST_CLK_HIGH : integer := 5;
  
  --
  type TYPE_CONFIG_FSM_STATE is ( STATE_RESET,
                                  STATE_PROG_PULSE,
                                  STATE_WAIT_FOR_INIT,
                                  STATE_GEN_FLASH_ADRESS,
                                  STATE_WAIT_FLASH_DATA,
                                  STATE_WRITE_TO_FPGA,
                                  STATE_SETUP_DATA,
                                  STATE_STARTUP_FINISH,
                                  STATE_FINISH
                                  );
  signal fsm_config_state : TYPE_CONFIG_FSM_STATE;
   
  --
  signal rst : std_logic;
  signal clk : std_logic;
  signal locked : std_logic;
  --
  signal virtex5_prog_b_n : std_logic;
  signal virtex5_init_b : std_logic;
  signal virtex5_data : std_logic_vector( XRD'range );
  signal virtex5_done : std_logic;
  signal virtex5_cclk : std_logic;
  signal virtex5_cs_n : std_logic;
  --
  constant RESET : std_logic := '1';
  constant RUN : std_logic := '0';
  signal counter : std_logic_vector(8 downto 0);
  signal counter_top : std_logic_vector( counter'range );
  signal counter_reset : std_logic;
  signal counter_finish : std_logic;
  --
  signal flash_memory_adress : std_logic_vector( FA'range );
  signal adress_counter : std_logic_vector( FA'range );
  signal flash_memory_data : std_logic_vector( FD'range );
  signal high_byte_memory_data : std_logic_vector( 7 downto 0 );
  signal startup_clk_count : std_logic_vector( 2 downto 0 );
  signal flash_memory_cs_n : std_logic;
  signal flash_memory_oe_n : std_logic;
  signal word_part : std_logic;
  --
  constant STATUS_RESET             : std_logic_vector( CLED'range ) := X"1";
  constant STATUS_PROG_PULSE        : std_logic_vector( CLED'range ) := X"2";
  constant STATUS_WAIT_FOR_INIT     : std_logic_vector( CLED'range ) := X"3";
  constant STATUS_FIRST_CLK_LOW     : std_logic_vector( CLED'range ) := X"4";
  constant STATUS_FIRST_CLK_HIGH    : std_logic_vector( CLED'range ) := X"5";
  constant STATUS_GEN_FLASH_ADRESS  : std_logic_vector( CLED'range ) := X"6";
  constant STATUS_WAIT_FLASH_DATA   : std_logic_vector( CLED'range ) := X"7";
  constant STATUS_WRITE_TO_FPGA     : std_logic_vector( CLED'range ) := X"8";
  constant STATUS_SETUP_DATA        : std_logic_vector( CLED'range ) := X"9";
  constant STATUS_STARTUP_FINISH    : std_logic_vector( CLED'range ) := X"A";
  constant STATUS_FINISH            : std_logic_vector( CLED'range ) := X"B";
  --
  signal status_led : std_logic_vector( CLED'range );
  --
  signal prescaler : std_logic_vector( 24 downto 0);
  --
  component clk_generator
  generic(
    CLK_DIVIDE : integer;
    CLK_MULTIPLY : integer
  );
	port(
		CLK_I : IN std_logic;
		RST_I : IN std_logic;          
		CLK_O : OUT std_logic;
		LOCKED_O : OUT std_logic
	);
	end component;
begin

  -- Led
  CLED <= not status_led;
  
  -- Virtex 5
  XM0 <= '0';       -- Slave SelectMAP
  XRRDWR_N <= '0';  -- the data pins are inputs (writing to the FPGA)
  XPROGRAM_N <= virtex5_prog_b_n;
  virtex5_init_b <= XINIT_N;
  XRCS_N <= virtex5_cs_n;
  --XRCS_N <= '0';
  XRCCLK <= virtex5_cclk;
  XRD <= virtex5_data;
  virtex5_done <= XDONE;
  XRDIN <= '0';
  XRHSH <= (others=>'Z');
  
  -- Flash
  FBYTE_N <= '1';    -- Only Flash word acces
  FA <= flash_memory_adress;
  FCSFLASH_N <= flash_memory_cs_n;
  FOE_N <= flash_memory_oe_n;
  flash_memory_data <= FD;
  FWE_N <= '1';
  FRY <= 'Z';

  -- PSRAM
  FLB_N <= '1';     
  FUB_N <= '1'; 
  FZZ_N <= '1'; 
  FCSRAM_N <= '1';    -- Disable

  INST_CLK_GENERATOR: clk_generator
  generic map(
    CLK_DIVIDE => CLK_DIVIDE,
    CLK_MULTIPLY => CLK_MULTIPLY
  )
  port map(
		CLK_I => CCLK,
		RST_I => '0',
		CLK_O => clk,
		LOCKED_O => locked
	);
  
  rst <= not (locked and RESET_N);
  
  process( rst, clk )
  begin
    if( rst = '1' )then
      counter <= (others=>'0');
      counter_finish <= '0';
    elsif( clk='1' and clk'event )then
      if( counter_reset = RESET )then
        counter <= (others=>'0');
        counter_finish <= '0';
      else
        if( counter = counter_top )then
          counter_finish <= '1';
        else
          counter <= counter + 1;
        end if;
      end if;
    end if;
  end process;
  
  --
  process( rst, clk )
  begin
    if( rst = '1' )then
      fsm_config_state <= STATE_RESET;
      counter_top <= (others=>'0');
      counter_reset <= RESET;
      word_part <= '0';
      startup_clk_count <= (others=>'0');
      --
      virtex5_cclk <= '0';
      virtex5_prog_b_n <= '1';
      virtex5_data <= (others=>'0');
      virtex5_cs_n <= '1';
      --
      adress_counter <= (others=>'0');
      flash_memory_adress <= (others=>'0');
      flash_memory_cs_n <= '0';
      flash_memory_oe_n <= '0';
      --
      status_led <= STATUS_RESET;
    elsif( clk='1' and clk'event )then
      case fsm_config_state is
        --
        when STATE_RESET =>
            virtex5_prog_b_n <= '1';
            counter_top <= conv_std_logic_vector( PROG_B_PULSE_WIDTH, counter_top'length );
            counter_reset <= RUN;
            fsm_config_state <= STATE_PROG_PULSE;
            -- Debug
            status_led <= STATUS_RESET;
        --
        when STATE_PROG_PULSE => 
            virtex5_prog_b_n <= '0';
            counter_reset <= RUN;
            if( counter_finish = '1' )then
                if( virtex5_init_b = '0' ) then
                    fsm_config_state <= STATE_WAIT_FOR_INIT;
                    counter_reset <= RESET;
                end if;
            end if;
            -- Debug
            status_led <= STATUS_PROG_PULSE;
        --
        when STATE_WAIT_FOR_INIT => 
            virtex5_prog_b_n <= '1';
            if( virtex5_init_b = '1' )then
              fsm_config_state <= STATE_WAIT_FLASH_DATA;             
              flash_memory_adress <= adress_counter; -- first adress for flash
              counter_top <= conv_std_logic_vector( NORMAL_MODE_ACCESS_CYCLE, counter_top'length );
              counter_reset <= RUN;
              adress_counter <= adress_counter + 1;
            end if;
            -- Debug
            status_led <= STATUS_WAIT_FOR_INIT;
        --
        when STATE_WAIT_FLASH_DATA =>
            if( counter_finish = '1' )then
              fsm_config_state <= STATE_SETUP_DATA;
              counter_reset <= RESET;
            end if;
            virtex5_cclk <= '0';
            virtex5_cs_n <= '0';
            -- Debug
            status_led <= STATUS_WAIT_FLASH_DATA;
        --
        when STATE_SETUP_DATA =>
            virtex5_cclk <= '0';
            if( word_part = '0' )then
              virtex5_data <= flash_memory_data(7 downto 0);
              fsm_config_state <= STATE_GEN_FLASH_ADRESS;
              high_byte_memory_data <= flash_memory_data(15 downto 8);
            else
              virtex5_data <= high_byte_memory_data;
              fsm_config_state <= STATE_WRITE_TO_FPGA;
            end if;
            -- Debug
            status_led <= STATUS_SETUP_DATA;
        --
        when STATE_GEN_FLASH_ADRESS =>
            flash_memory_adress <= adress_counter;
            --
            if( adress_counter(2 downto 0) = "000" )then
              counter_top <= conv_std_logic_vector( NORMAL_MODE_ACCESS_CYCLE, counter_top'length );
              counter_reset <= RUN;
            else
              counter_top <= conv_std_logic_vector( PAGE_MODE_ACCESS_TIME, counter_top'length );
              counter_reset <= RUN;
            end if;
            adress_counter <= adress_counter + 1;
            fsm_config_state <= STATE_WRITE_TO_FPGA;
            virtex5_cclk <= '0';
            -- Debug
            status_led <= STATUS_GEN_FLASH_ADRESS;
        --
        when STATE_WRITE_TO_FPGA =>
            virtex5_cclk <= '1';
            if( word_part = '0' )then
              fsm_config_state <= STATE_SETUP_DATA;
            else
              if( virtex5_done = '1' )then  -- Finish config -> Start-up Start
                fsm_config_state <= STATE_STARTUP_FINISH;
              else
                fsm_config_state <= STATE_WAIT_FLASH_DATA;
              end if;
            end if;
            word_part <= not word_part;
            -- Debug
            status_led <= STATUS_WRITE_TO_FPGA;
        --
        when STATE_STARTUP_FINISH =>
            virtex5_cclk <= '0';
            if( virtex5_cclk = '1' )then
              startup_clk_count <= startup_clk_count + 1;
            end if;
            if( startup_clk_count = "111" )then
                fsm_config_state <= STATE_FINISH;
            end if;
            virtex5_cclk <= not virtex5_cclk;
            -- Debug
            status_led <= STATUS_STARTUP_FINISH;
        --
        when STATE_FINISH =>
            virtex5_cclk <= '0';
            virtex5_data <= (others=>'Z');
            -- Debug
            status_led <= prescaler( prescaler'high ) & prescaler( prescaler'high ) & prescaler( prescaler'high ) & prescaler( prescaler'high );
        --
        when others =>
      end case;
    end if;
  end process;
  
process( rst, clk )
begin
    if( rst = '1' )then
        prescaler <= (others=>'0');
    elsif( clk = '1' and clk'event )then
        if( fsm_config_state = STATE_FINISH )then
            prescaler <= prescaler + 1;
        end if;
    end if;
end process;

end behavioral;
