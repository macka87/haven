-- 
-- fpga_config.vhd: FPGA booting component for the ComboV2 (FLASH/PSRAM read 
--                  and FPGA boot)
-- Copyright (C) 2008  CESNET
-- Author: Milan Malich <malich@mail.muni.cz>
--         Stepan Friedl <friedl@liberouter.org>
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

entity fpga_config is
    Port ( 
    -- Oscilator (U17)
    CCLK           : in std_logic;
    CCLK_O         : out std_logic;    
    -- Reset (BT1)
    RESET_N        : in std_logic;
    -- Led
    CLED           : out std_logic_vector( 3 downto 0 );
    -- 
    START          : in std_logic;
    START_ADDRESS  : in std_logic_vector( 25 downto 0 ); -- Flash start address
    FLASH_SEL      : in std_logic;
    BOOT_DONE      : out std_logic;
    BOOT_TIMEOUT   : out std_logic;
    -- Virtex Config
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
    FRY            : in  std_logic;
    FLB_N          : out std_logic;     
    FUB_N          : out std_logic;
    FZZ_N          : out std_logic 
    );
end fpga_config;

architecture behavioral of fpga_config is
   -- 25 downto 0
   -- "00" & X"000000";
   --      27 26 25 24 23
   -- SW: F/P X  X  A  X"AAAAAA";
   --       1 0  0  1  X"C00000"
  constant RESCUE_FLASH_ADDRESS : std_logic_vector(25 downto 0) := "01" & "1100" & X"00000"; -- Block 7
  -- DCM Setting
  -- Input CCLK is 100Mhz (10ns period)
  -- Output DCM is 100Mhz (10ns period)
  constant CLK_DIVIDE : integer := 2;
  constant CLK_MULTIPLY : integer := 2;
  
  -- Timing is ( datasheet_value(ns) / 10  = 250ns/10 = 25)
  -- Virtex5 Timing
  constant T_PROG : integer := 300; -- 
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
                                  STATE_FINISH,
                                  STATE_TIMEOUT
                                  );
  signal fsm_config_state : TYPE_CONFIG_FSM_STATE;
   
  --
  signal rst_v : std_logic_vector(3 downto 0) := (others => '1');
  signal rst_i : std_logic;
  signal rst : std_logic;
  signal clk : std_logic;
  signal locked : std_logic;
  --
  signal virtex5_prog_b_n : std_logic;
  signal virtex5_init_b : std_logic;
  signal virtex5_done : std_logic;  
  signal virtex5_data : std_logic_vector( XRD'range );
  signal virtex5_cclk : std_logic;
  signal reg_virtex5_init_b : std_logic;
  signal reg_virtex5_done : std_logic;  
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
  signal psram_cs_n : std_logic;
  signal word_part : std_logic;
  signal start_address_reg : std_logic_vector(START_ADDRESS'range);
  --
  constant STATUS_RESET             : std_logic_vector( CLED'range ) := X"1";
  constant STATUS_PROG_PULSE        : std_logic_vector( CLED'range ) := X"C";
  constant STATUS_WAIT_FOR_INIT     : std_logic_vector( CLED'range ) := X"3";
  constant STATUS_FIRST_CLK_LOW     : std_logic_vector( CLED'range ) := X"4";
  constant STATUS_FIRST_CLK_HIGH    : std_logic_vector( CLED'range ) := X"5";
  constant STATUS_GEN_FLASH_ADRESS  : std_logic_vector( CLED'range ) := X"6";
  constant STATUS_WAIT_FLASH_DATA   : std_logic_vector( CLED'range ) := X"7";
  constant STATUS_WRITE_TO_FPGA     : std_logic_vector( CLED'range ) := X"8";
  constant STATUS_SETUP_DATA        : std_logic_vector( CLED'range ) := X"9";
  constant STATUS_STARTUP_FINISH    : std_logic_vector( CLED'range ) := X"A";
  constant STATUS_FINISH            : std_logic_vector( CLED'range ) := X"B";
  constant STATUS_TIMEOUT           : std_logic_vector( CLED'range ) := X"C";
  --
  signal status_led : std_logic_vector( CLED'range );
  --
  signal prescaler  : std_logic_vector( 24 downto 0);
  signal watch_en   : std_logic;
  signal watch_clr  : std_logic;
  signal watch_cntr : std_logic_vector( 22 downto 0); -- 2^22 = 4M
  --

begin

  -- Led
  CLED <= not status_led;
  
  -- Virtex 5
  XM0 <= '0';       -- Slave SelectMAP parallel
  XRRDWR_N <= '0';  -- the data pins are inputs (writing to the FPGA)
  XPROGRAM_N <= virtex5_prog_b_n;
  XRCS_N <= virtex5_cs_n;
  --XRCS_N <= '0';
  XRCCLK <= virtex5_cclk;
  XRD <= virtex5_data;
  XRDIN <= '0';
  
  -- Flash
  FBYTE_N    <= '1';    -- Only Flash word acces
  FA         <= flash_memory_adress;
  FCSFLASH_N <= flash_memory_cs_n;
  FOE_N      <= flash_memory_oe_n;
  flash_memory_data <= FD;
  FWE_N <= '1';

  -- PSRAM
  FLB_N <= '0';     
  FUB_N <= '0'; 
  FZZ_N <= '1'; 
  FCSRAM_N <= psram_cs_n;    -- Disable
  
  V5_SYNC: process(CCLK)
  begin
     if CCLK'event and CCLK = '1' then
        reg_virtex5_init_b <= XINIT_N;
        reg_virtex5_done   <= XDONE;
        
        virtex5_init_b <= reg_virtex5_init_b;
        virtex5_done   <= reg_virtex5_done;
     end if;
  end process;
   
  clk    <= CCLK;
  CCLK_O <= clk;
  
  rst_i <= (not RESET_N) or (START);
  rst_sync: process(CLK)
  begin
     if CLK'event and CLK = '1' then
        rst_v <= rst_v(rst_v'high-1 downto 0) & rst_i;
     end if;
  end process;   
  
  rst <= rst_v(rst_v'high);
  
  process( rst, clk )
  begin
    if( clk='1' and clk'event )then
      if (counter_reset = RESET ) or (rst = '1') then
        counter <= (others=>'0');
        counter_finish <= '0';
      else
        if (counter = counter_top )then
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
    if( clk='1' and clk'event )then
       if (rst = '1' )then
          fsm_config_state  <= STATE_RESET;
          counter_top       <= (others=>'0');
          counter_reset     <= RESET;
          word_part         <= '0';
          startup_clk_count <= (others=>'0');
          --
          virtex5_cclk      <= '0';
          virtex5_prog_b_n  <= '1';
          virtex5_data      <= (others=>'0');
          virtex5_cs_n      <= '1';
          --
          adress_counter      <= (others=>'0');
          flash_memory_adress <= (others=>'0');
          flash_memory_cs_n   <= '1';
          psram_cs_n          <= '1';
          flash_memory_oe_n   <= '0';
          BOOT_DONE           <= '0';
          BOOT_TIMEOUT        <= '0';
          --
          status_led <= STATUS_RESET;
          
       else
       
         BOOT_DONE    <= '0';
         BOOT_TIMEOUT <= '0';
         watch_en     <= '0';
         watch_clr    <= '0';
         
         case fsm_config_state is
           --
           when STATE_RESET =>
               virtex5_cclk      <= not virtex5_cclk;
               virtex5_prog_b_n  <= '1';
               flash_memory_cs_n <= not FLASH_SEL;
               psram_cs_n        <= FLASH_SEL;
               virtex5_cs_n      <= '1';
               counter_top       <= conv_std_logic_vector( PROG_B_PULSE_WIDTH, counter_top'length );
               counter_reset     <= RUN;
               fsm_config_state  <= STATE_PROG_PULSE;
               start_address_reg <= START_ADDRESS;
               -- Debug
               status_led <= STATUS_RESET;
           --
           when STATE_PROG_PULSE => 
               virtex5_cclk     <= not virtex5_cclk;
               virtex5_prog_b_n <= '0';
               counter_reset    <= RUN;
               if( counter_finish = '1' )then
                   virtex5_prog_b_n <= '1';
                   if( virtex5_init_b = '0' ) then
                       fsm_config_state <= STATE_WAIT_FOR_INIT;
                       counter_reset <= RESET;
                       watch_clr     <= '1';                       
                   end if;
               end if;
               -- Debug
               status_led <= STATUS_PROG_PULSE;
           --
           when STATE_WAIT_FOR_INIT => 
               virtex5_prog_b_n <= '1';
               counter_reset    <= RESET;
               virtex5_cclk     <= not virtex5_cclk;            
               if (virtex5_init_b = '1') then
                 fsm_config_state <= STATE_WAIT_FLASH_DATA;
                 flash_memory_adress <= start_address_reg; -- first adress for flash
                 counter_top    <= conv_std_logic_vector( NORMAL_MODE_ACCESS_CYCLE, counter_top'length );
                 counter_reset  <= RUN;
                 adress_counter <= start_address_reg + 1;
               end if;
               -- Debug
               status_led <= STATUS_WAIT_FOR_INIT;
           --
           when STATE_WAIT_FLASH_DATA =>
               if (counter_finish = '1' )then
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
               if (word_part = '0' )then
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
                 watch_en <= '1';
               else
                 if (virtex5_done = '1') then  -- Finish config -> Start-up Start
                    fsm_config_state <= STATE_STARTUP_FINISH;
                 elsif (watch_cntr(watch_cntr'high) = '1') then
                    fsm_config_state <= STATE_TIMEOUT;
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
                   BOOT_DONE        <= '1';
               end if;
               virtex5_cclk <= not virtex5_cclk;
               -- Debug
               status_led <= STATUS_STARTUP_FINISH;
           --
           when STATE_FINISH =>
               virtex5_cclk <= '0';
               virtex5_data <= (others=>'Z');
               flash_memory_cs_n <= '1';
               psram_cs_n        <= '1';
               virtex5_cs_n      <= '1';
               -- Debug
               status_led        <= prescaler( prescaler'high ) & prescaler( prescaler'high ) & prescaler( prescaler'high ) & prescaler( prescaler'high );
               status_led        <= STATUS_FINISH; 
           --
           when STATE_TIMEOUT => -- Boot the rescue design from FLASH
              BOOT_TIMEOUT      <= '1';
              flash_memory_cs_n <= '0';
              psram_cs_n        <= '1';
              virtex5_cs_n      <= '1';
              -- boot_cntr         <= boot_cntr + 1;
              start_address_reg <= RESCUE_FLASH_ADDRESS(start_address_reg'range);
              counter_top       <= conv_std_logic_vector(PROG_B_PULSE_WIDTH, counter_top'length );
              counter_reset     <= RUN;
              fsm_config_state  <= STATE_PROG_PULSE;
              -- Debug
              status_led        <= STATUS_TIMEOUT;
               
           when others =>
         end case;
      end if;
    end if;
  end process;
  
process( rst, clk )
begin
    if( clk = '1' and clk'event )then
       prescaler <= prescaler + 1;
    end if;
end process;

process( rst, clk )
begin
   if( clk = '1' and clk'event )then
      if (watch_clr = '1') then
         watch_cntr <= (others => '0');
      elsif (watch_en = '1') then
         watch_cntr <= watch_cntr + 1;
      end if;
   end if;
end process;

end behavioral;
