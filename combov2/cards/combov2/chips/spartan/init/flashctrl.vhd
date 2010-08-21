-- flashctrl.vhd : ComboV2 flash controller
-- Copyright (C) 2008 CESNET
-- Author(s): Stepan Friedl <friedl@liberouter.org>
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
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;
use work.ib_pkg.all;

library UNISIM;
use UNISIM.vcomponents.all;

-- ----------------------------------------------------------------------------
--             Architecture declaration  --  Ml555 Top Level                 --
-- ----------------------------------------------------------------------------

entity flashctrl is
   port (
      RESET      : in std_logic; -- Global async reset
      CLK        : in std_logic; -- 
      -- write interface
      INIT       : in  std_logic; -- Do initialization
      ERASE      : in  std_logic; -- Do sector erase
      WRITE      : in  std_logic; -- Prepare for the write operation (unlock)
      WEN        : in  std_logic; -- Write operation
      REN        : in  std_logic; -- Read operation
      --
      ADDR       : in  std_logic_vector(25 downto 0);
      DRD        : out std_logic_vector(31 downto 0);
      DRD_VAL    : out std_logic;
      DWR        : in  std_logic_vector(31 downto 0);
      PSRAM_SEL  : in  std_logic; -- '1' -- PSRAM select, '0' = FLASH select
      -- Status 
      RDY        : out std_logic; -- Ready for new data
      BUSY       : out std_logic; -- No IDLE, not ready for new command
      -- FLASH interface --
      FA         : out std_logic_vector( 25 downto 0 );
      FD_I       : in  std_logic_vector( 15 downto 0 );
      FD_O       : out std_logic_vector( 15 downto 0 );
      FD_OE      : out std_logic;
      FWE_N      : out std_logic;
      FCSFLASH_N : out std_logic;
      FCSRAM_N   : out std_logic;
      FOE_N      : out std_logic;
      FBYTE_N    : out std_logic;
      FRY        : in  std_logic;
      FLB_N      : out std_logic;     
      FUB_N      : out std_logic;
      FZZ_N      : out std_logic;
      -- Debug
      STATE      : out std_logic_vector(7 downto 0)
   );
end flashctrl;

architecture structural of flashctrl is
  
  constant PSRAM_INIT_CR : std_logic_vector(17 downto 0) := "000000000010010000"; -- Enable Page mode, Sleep mode PAR
  constant LATENCY_COMP : integer := 2;
    
  -- Timing is ( datasheet_value(ns) / 10 )
  -- Flash Memory Timing
  constant T_ACC  : integer := 16; -- Access time
  constant T_PACC : integer := 4;  -- Page access time
  constant T_WC   : integer := 13 - LATENCY_COMP; -- Write cycle time
  constant T_WP   : integer := 5 - LATENCY_COMP;  -- Write pulse low time
  constant T_WPH  : integer := 8 - LATENCY_COMP;  -- Write pulse high time;
  -- PSRAM timing
  constant T_PS_ACC  : integer := 9; -- Access time
  constant T_PS_PACC : integer := 3; -- Page access time
  --
  constant NORMAL_MODE_ACCESS_CYCLE : integer := T_ACC - LATENCY_COMP;
  constant PAGE_MODE_ACCESS_TIME    : integer := T_PACC - LATENCY_COMP;
  constant PSRAM_READ_CYCLE_TIME   : integer := T_PS_ACC - LATENCY_COMP;
  constant PSRAM_PAGE_READ_ACCESS_TIME : integer := T_PS_PACC - LATENCY_COMP;
  constant PSRAM_WRITE_CYCLE_TIME  : integer := T_PS_ACC - LATENCY_COMP;
  
  
  --
  type TYPE_CONFIG_FSM_STATE is ( STATE_IDLE,
                                  STATE_INIT,
                                  STATE_READ0,
                                  STATE_READ1,
                                  STATE_ERASE0,
                                  STATE_ERASE1,
                                  STATE_ERASE2,
                                  STATE_ERASE3,
                                  STATE_ERASE4,
                                  STATE_ERASE5,
                                  STATE_ERASE_WAIT,
                                  STATE_WRITE0,
                                  STATE_WRITE1,
                                  STATE_WRITE2,
                                  STATE_WRITE_DATA0,
                                  STATE_WRITE_DATA1,
                                  STATE_WRITE_DATA2,
                                  STATE_WRITE_DATA3,
                                  STATE_WRITE_WAIT0,
                                  STATE_WRITE_WAIT1,
                                  STATE_LOCK_RESET0,
                                  STATE_LOCK_RESET1,
                                  STATE_PS_READ0,
                                  STATE_PS_READ1,
                                  STATE_PS_WRITE0,
                                  STATE_PS_WRITE1                                  
                                  );
  signal fsm_state : TYPE_CONFIG_FSM_STATE;
  
  type T_WR_STATE is (SETUP,
                      WR_PULSE,
                      WR_CYCLE,
                      DONE 
                     );
  signal wr_state, next_wr_state   : T_WR_STATE;
   
  --
  signal counter : std_logic_vector(8 downto 0);
  signal counter_top : std_logic_vector( counter'range );
  signal counter_reset    : std_logic;
  signal counter_finish   : std_logic;
  signal counter_finished : std_logic;
  --
  signal flash_memory_adress : std_logic_vector( FA'range ) := (others => '1');
  signal flash_memory_data_o : std_logic_vector( FD_O'range );
  signal address_counter : std_logic_vector( FA'range );
  signal flash_memory_data : std_logic_vector( FD_I'range );
  signal flash_memory_cs_n : std_logic;
  signal flash_memory_oe_n : std_logic;
  signal flash_memory_fd_oe: std_logic;
  signal flash_memory_we_n : std_logic;
  signal flash_data_sync0  : std_logic_vector( FD_I'range );
  signal flash_data        : std_logic_vector( FD_I'range );
  signal flash_data_stable : std_logic;
  
  signal psram_cs_n : std_logic;
  signal psram_zz_n : std_logic;
  signal data7      : std_logic;
  signal data23     : std_logic;
  
  signal rdy_i           : std_logic;
  signal cs_i            : std_logic;
  signal we_i            : std_logic;
  signal wr_done         : std_logic;
  signal wr_start        : std_logic;
  signal counter_top_i   : std_logic_vector(counter'range);
  signal counter_reset_i : std_logic;
    --
--   constant STATUS_RESET             : std_logic_vector( CLED'range ) := X"1";
--   constant STATUS_PROG_PULSE        : std_logic_vector( CLED'range ) := X"2";
--   constant STATUS_WAIT_FOR_INIT     : std_logic_vector( CLED'range ) := X"3";
--   constant STATUS_FIRST_CLK_LOW     : std_logic_vector( CLED'range ) := X"4";
--   constant STATUS_FIRST_CLK_HIGH    : std_logic_vector( CLED'range ) := X"5";
--   constant STATUS_GEN_FLASH_ADRESS  : std_logic_vector( CLED'range ) := X"6";
--   constant STATUS_WAIT_FLASH_DATA   : std_logic_vector( CLED'range ) := X"7";
--   constant STATUS_WRITE_TO_FPGA     : std_logic_vector( CLED'range ) := X"8";
--   constant STATUS_SETUP_DATA        : std_logic_vector( CLED'range ) := X"9";
--   constant STATUS_STARTUP_FINISH    : std_logic_vector( CLED'range ) := X"A";
--   constant STATUS_FINISH            : std_logic_vector( CLED'range ) := X"B";
--   --
--   signal status_led : std_logic_vector( CLED'range );
  
begin

  RDY <= rdy_i;
  
  -- Flash
  FA         <= flash_memory_adress;
  FCSFLASH_N <= flash_memory_cs_n;
  FOE_N      <= flash_memory_oe_n;
  FD_OE      <= flash_memory_fd_oe;
  FD_O       <= flash_memory_data_o;
  flash_memory_data <= FD_I;
  FWE_N      <= flash_memory_we_n;    -- Read only 
  FBYTE_N    <= '1';    -- Only Flash word acces

  -- PSRAM
  FLB_N <= '0';     
  FUB_N <= '0'; 
  FZZ_N    <= psram_zz_n;
  FCSRAM_N <= psram_cs_n;    -- Disable
  
 
  process( RESET, CLK )
  begin
    if( RESET = '1' )then
      counter <= (others=>'0');
      counter_finish <= '0';
      counter_finished <= '0';
    elsif( CLK='1' and CLK'event )then
      if (counter_reset = '1' )then
         counter <= (others=>'0');
      else
         counter <= counter + 1;
      end if;
      
      if (counter = counter_top )then
         counter_finish <= '1';
      else
         counter_finish <= '0';
      end if;
      
      if (counter_reset = '1' )then
         counter_finished <= '0';
      elsif (counter = counter_top )then
         counter_finished <= '1';
      end if;
      
    end if;
  end process;
  
  FLASH_DATA_RECLOCK: process(CLK)
  begin
     if CLK = '1' and CLK'event then
        flash_data_sync0 <= flash_memory_data;
        flash_data       <= flash_data_sync0;
        if (flash_data_sync0 = flash_memory_data) then
           flash_data_stable <= '1';
        else
           flash_data_stable <= '0';
        end if;
     end if;
  end process;
  
  
  --
  FLASH_WRITE_FSM_SEQ: process(RESET, CLK)
  begin
     if (RESET = '1') then
        wr_state <= SETUP;
     elsif CLK = '1' and CLK'event then
        wr_state <= next_wr_state;
     end if;
  end process;
  
  -- FLASH write seq:
  -- 1. CE=1; WE=1; Address; Data -> goto 2. (SETUP)
  -- 2. CE=0; WE=0; wait Twp  -> goto 3. (WRITE_PULSE, data latched on WE->1, addr latched on CE->0) (35ns)
  -- 3. CE=0; WE=1; wait Twc-Twp -> goto 4. (130-35=95ns)
  -- 4. CE=1; WE=1; -> goto 1.    
  FLASH_WRITE_FSM_COMB: process(wr_start, counter_finish)
  begin
     wr_done         <= '0';
     counter_reset_i <= '1';
     counter_top_i   <= conv_std_logic_vector(T_WP, counter_top'length );   
     
     case WR_STATE is
        when SETUP =>    -- Address/data setup cycle
           cs_i            <= '1';
           we_i            <= '1';
           counter_reset_i <= '1';
           if (wr_start = '1') then
              next_wr_state <= WR_PULSE;
           else
              next_wr_state <= SETUP;
           end if;
           
        when WR_PULSE => -- Generate write pulse for Twp time
           cs_i            <= '0';
           we_i            <= '0';
           counter_top_i   <= conv_std_logic_vector(T_WP, counter_top'length );
           counter_reset_i <= '0';
           if (counter_finish = '1') then
              next_wr_state   <= WR_CYCLE;
              counter_reset_i <= '1';
           else
              next_wr_state   <= WR_PULSE;
           end if;
           
        when WR_CYCLE => -- Generate write cycle for Twph time
           cs_i            <= '0';
           we_i            <= '1';
           counter_top_i   <= conv_std_logic_vector(T_WPH, counter_top'length );
           counter_reset_i <= '0';
           if (counter_finish = '1') then
              next_wr_state <= DONE;
           else
              next_wr_state   <= WR_CYCLE;
           end if;
           
        when DONE => 
           cs_i          <= '1';
           we_i          <= '1';
           wr_done       <= '1';
           next_wr_state <= SETUP;
           
     end case;
  end process;
  
  DEBUG_STATE_OUT: process(FSM_STATE)
  begin
     case FSM_STATE is
        when STATE_IDLE     => STATE <= X"00";
        when STATE_INIT     => STATE <= X"01";
        when STATE_READ0    => STATE <= X"02";
        when STATE_READ1    => STATE <= X"03";
        when STATE_ERASE0   => STATE <= X"04";
        when STATE_ERASE1   => STATE <= X"05";
        when STATE_ERASE2   => STATE <= X"06";
        when STATE_ERASE3   => STATE <= X"07";
        when STATE_ERASE4   => STATE <= X"08";
        when STATE_ERASE5   => STATE <= X"09";
        when STATE_WRITE0   => STATE <= X"0a";
        when STATE_WRITE1   => STATE <= X"0b";
        when STATE_WRITE2   => STATE <= X"0c";
        when STATE_PS_READ0 => STATE <= X"0e";
        when STATE_PS_READ1 => STATE <= X"0f";
        when STATE_PS_WRITE0=> STATE <= X"10";
        when STATE_PS_WRITE1=> STATE <= X"11";
        when STATE_WRITE_DATA0 => STATE <= X"12";
        when STATE_WRITE_DATA1 => STATE <= X"13";
        when STATE_WRITE_DATA2 => STATE <= X"14";
        when STATE_WRITE_DATA3 => STATE <= X"15";
        when STATE_LOCK_RESET0 => STATE <= X"16";
        when STATE_LOCK_RESET1 => STATE <= X"17";
        when STATE_WRITE_WAIT0 => STATE <= X"18";
        when STATE_WRITE_WAIT1 => STATE <= X"19";
        when STATE_ERASE_WAIT  => STATE <= X"1a";
        when others            => STATE <= X"FF";
     end case;
  end process;

  --
  process( RESET, CLK )
  begin
    if( RESET = '1' )then
      fsm_state           <= STATE_INIT;
      counter_top         <= (others=>'1');
      counter_reset       <= '1';
      address_counter     <= (others=>'0');
      flash_memory_adress <= (others=>'1');
      flash_memory_cs_n   <= '1';
      flash_memory_oe_n   <= '1';
      flash_memory_fd_oe  <= '0';
      flash_memory_we_n   <= '1';
      psram_cs_n          <= '1';
      psram_zz_n          <= '1';
      wr_start            <= '0';
      rdy_i               <= '0';
      BUSY                <= '1';
      --
    elsif CLK = '1' and CLK'event then
    
      DRD_VAL            <= '0';    
      flash_memory_cs_n  <= '1';
      flash_memory_oe_n  <= '1';
      flash_memory_fd_oe <= '0';
      flash_memory_we_n  <= '1';      
      counter_reset      <= '1';
      psram_cs_n         <= '1';
      psram_zz_n         <= '1';
      wr_start           <= '0';
      BUSY               <= '1';
      rdy_i              <= '0';
      
      case FSM_STATE is
        when STATE_IDLE =>
            counter_reset <= '1';
            rdy_i         <= '1';
            BUSY          <= '0';
            flash_memory_data_o <= (others => '0');
            if (INIT = '1') then 
               psram_zz_n          <= '0';
               flash_memory_adress <= "00000000" & PSRAM_INIT_CR;
               counter_top         <= conv_std_logic_vector(PSRAM_READ_CYCLE_TIME, counter_top'length );
               counter_reset       <= '0';
               fsm_state           <= STATE_INIT;
            elsif (WRITE = '1') and (PSRAM_SEL = '0') then
               fsm_state           <= STATE_WRITE0;
            elsif (WEN = '1')  and (PSRAM_SEL = '1') then
               flash_memory_adress <= ADDR; -- first adress for flash
               address_counter     <= ADDR + 1;
               counter_top         <= conv_std_logic_vector(PSRAM_WRITE_CYCLE_TIME, counter_top'length );
               counter_reset       <= '0';
               flash_memory_fd_oe  <= '1'; -- Enable data output
               fsm_state           <= STATE_PS_WRITE0;
            elsif (ERASE = '1') and (PSRAM_SEL = '0') then 
               fsm_state           <= STATE_ERASE0;
               flash_memory_adress <= (others => '0');
            elsif (REN = '1')  and (PSRAM_SEL = '0') then
               flash_memory_adress <= ADDR; -- first adress for flash
               address_counter     <= ADDR + 1;
               counter_top         <= conv_std_logic_vector(NORMAL_MODE_ACCESS_CYCLE, counter_top'length );
               counter_reset       <= '0';
               fsm_state           <= STATE_READ0;
            elsif (REN = '1')  and (PSRAM_SEL = '1') then
               flash_memory_adress <= ADDR; -- first adress for flash
               address_counter     <= ADDR + 1;
               counter_top         <= conv_std_logic_vector(PSRAM_READ_CYCLE_TIME, counter_top'length );
               counter_reset       <= '0';
               fsm_state           <= STATE_PS_READ0;
            end if;
            
        -- Initialize the PSRAM (enable page mode)
        when STATE_INIT => 
           psram_zz_n        <= '0';
           counter_reset     <= '0';
           psram_cs_n        <= '0'; -- Select PSRAM
           flash_memory_we_n <= '0'; -- Write enable           
           if (counter_finish = '1') then
              psram_zz_n        <= '1';
              counter_reset     <= '1';
              psram_cs_n        <= '1'; -- Select PSRAM
              flash_memory_we_n <= '1'; 
              fsm_state         <= STATE_IDLE;              
           end if;
           
         -- FLASH sector erase - Unlock cycle 1
        when STATE_ERASE0 =>
           flash_memory_adress(11 downto 0) <= X"555";
           flash_memory_data_o(7 downto 0)  <= X"AA";
           flash_memory_fd_oe <= '1';
           flash_memory_cs_n <= cs_i;
           flash_memory_we_n <= we_i;
           counter_reset     <= counter_reset_i;
           counter_top       <= counter_top_i;
           wr_start          <= '1';
           if (wr_done = '1') then
              fsm_state <= STATE_ERASE1;
           end if;
        -- FLASH sector erase - Unlock cycle 2
        when STATE_ERASE1 =>
           flash_memory_adress(11 downto 0) <= X"2AA";           
           flash_memory_data_o(7 downto 0)  <= X"55";
           flash_memory_fd_oe <= '1';
           flash_memory_cs_n <= cs_i;           
           flash_memory_we_n <= we_i;           
           counter_reset     <= counter_reset_i;
           counter_top       <= counter_top_i;
           wr_start          <= '1';
           if (wr_done = '1') then
              fsm_state  <= STATE_ERASE2;
           end if;
        -- FLASH sector erase - Setup command
        when STATE_ERASE2 =>
           flash_memory_adress(11 downto 0) <= X"555";           
           flash_memory_data_o(7 downto 0)  <= X"80";
           flash_memory_fd_oe <= '1';
           flash_memory_cs_n <= cs_i;           
           flash_memory_we_n <= we_i;           
           counter_reset     <= counter_reset_i;
           counter_top       <= counter_top_i;
           wr_start          <= '1';
           if (wr_done = '1') then
              fsm_state <= STATE_ERASE3;
           end if;
        -- FLASH sector erase - additional unlock cycle 1
        when STATE_ERASE3 =>
           flash_memory_adress(11 downto 0) <= X"555";
           flash_memory_data_o(7 downto 0)  <= X"AA";
           flash_memory_fd_oe <= '1';
           flash_memory_cs_n <= cs_i;           
           flash_memory_we_n <= we_i;           
           counter_reset     <= counter_reset_i;
           counter_top       <= counter_top_i;
           wr_start          <= '1';
           if (wr_done = '1') then
              fsm_state <= STATE_ERASE4;
           end if;
        -- FLASH sector erase - additional unlock cycle 2
        when STATE_ERASE4 =>
           flash_memory_adress(11 downto 0) <= X"2AA";           
           flash_memory_data_o(7 downto 0)  <= X"55";
           flash_memory_fd_oe <= '1';
           flash_memory_cs_n <= cs_i;
           flash_memory_we_n <= we_i;
           counter_reset     <= counter_reset_i;
           counter_top       <= counter_top_i;
           wr_start          <= '1';
           if (wr_done = '1') then
              fsm_state <= STATE_ERASE5;
           end if;        
        -- FLASH sector erase - sector erase command
        when STATE_ERASE5 =>
           flash_memory_adress <= ADDR;           
           flash_memory_data_o(7 downto 0)  <= X"30";
           flash_memory_fd_oe <= '1';
           flash_memory_cs_n <= cs_i;
           flash_memory_we_n <= we_i;
           counter_reset     <= counter_reset_i;
           counter_top       <= counter_top_i;
           wr_start          <= '1';
           if (wr_done = '1') then
              fsm_state     <= STATE_ERASE_WAIT;
              wr_start      <= '0';
              counter_reset <= '1';
              counter_top   <= conv_std_logic_vector(4, counter_top'length ); -- Delay value experimental from chipscope
           end if;
           
        when STATE_ERASE_WAIT =>
           flash_memory_fd_oe <= '0';
           flash_memory_oe_n  <= '0';
           flash_memory_cs_n  <= '0';
           flash_memory_we_n  <= '1';
           counter_reset      <= '0';
           if (flash_data(7) = '1') and
             ((counter_finished = '1') and (counter_reset = '0')) then
              fsm_state  <= STATE_IDLE;
           end if;

        -- FLASH single word program - Unlock cycle 1
        when STATE_WRITE0 =>
           flash_memory_adress(11 downto 0) <= X"555";
           flash_memory_data_o(7 downto 0)  <= X"AA";
           flash_memory_fd_oe <= '1';
           flash_memory_cs_n <= cs_i;
           flash_memory_we_n <= we_i;
           counter_reset     <= counter_reset_i;
           counter_top       <= counter_top_i;
           wr_start          <= '1';
           if (wr_done = '1') then
              fsm_state <= STATE_WRITE1;
           end if;
        -- FLASH single word program - Unlock cycle 2
        when STATE_WRITE1 =>
           flash_memory_adress(11 downto 0) <= X"2AA";
           flash_memory_data_o(7 downto 0)  <= X"55";
           flash_memory_fd_oe <= '1';
           flash_memory_cs_n  <= cs_i;
           flash_memory_we_n  <= we_i;
           counter_reset      <= counter_reset_i;
           counter_top        <= counter_top_i;
           wr_start           <= '1';
           if (wr_done = '1') then
              fsm_state <= STATE_WRITE2;
           end if;
        -- FLASH single word program - Confirm unlock 
        when STATE_WRITE2 =>
           flash_memory_adress(11 downto 0) <= X"555";
           flash_memory_data_o(7 downto 0)  <= X"20"; 
           flash_memory_fd_oe <= '1';
           flash_memory_cs_n <= cs_i;
           flash_memory_we_n <= we_i;
           counter_reset     <= counter_reset_i;
           counter_top       <= counter_top_i;
           wr_start          <= '1';
           if (wr_done = '1') then
              fsm_state <= STATE_WRITE_DATA0;
              wr_start  <= '0';
              rdy_i     <= '1';
           end if;
        -- FLASH single word program - setup 
        when STATE_WRITE_DATA0 =>
           rdy_i  <= rdy_i;
           if WEN = '1' then
              address_counter <= ADDR;
              data7  <= DWR(7);
              data23 <= DWR(7+16);
              rdy_i  <= '0';
           end if;
           flash_memory_data_o <= X"00A0";
           flash_memory_fd_oe  <= '1';
           flash_memory_cs_n   <= cs_i;
           flash_memory_we_n   <= we_i;
           counter_reset       <= counter_reset_i;
           counter_top         <= counter_top_i;
           wr_start            <= WEN;
           if (wr_done = '1') then
              fsm_state <= STATE_WRITE_DATA1;
           elsif (WRITE = '0') then
              fsm_state <= STATE_LOCK_RESET0;
              wr_start       <= '0';
           end if;
        -- FLASH single word program - Store address & data
        when STATE_WRITE_DATA1 =>
           flash_memory_adress <= address_counter;
           flash_memory_data_o <= DWR(15 downto 0);
           flash_memory_fd_oe  <= '1';
           flash_memory_cs_n   <= cs_i;
           flash_memory_we_n   <= we_i;
           counter_reset       <= counter_reset_i;
           counter_top         <= counter_top_i;
           wr_start            <= '1';
           if (wr_done = '1') then
              fsm_state       <= STATE_WRITE_WAIT0;
              wr_start        <= '0';
              address_counter <= address_counter + 1;
              counter_reset   <= '1';
              counter_top     <= conv_std_logic_vector(4, counter_top'length ); -- Delay value experimental from chipscope
           end if;
        -- Wait until the FLASH write opeartion is done
        when STATE_WRITE_WAIT0 =>
           counter_reset      <= '0';
           flash_memory_fd_oe <= '0';
           flash_memory_oe_n  <= '0';
           flash_memory_cs_n  <= '0';
           flash_memory_we_n  <= '1';
           if (flash_data(7) = data7) and 
             ((counter_finished = '1') and (counter_reset = '0')) then
              fsm_state <= STATE_WRITE_DATA2;
              flash_memory_oe_n  <= '1';
              counter_reset      <= '1';
           end if;
        -- FLASH single word program - high word - setup 
        when STATE_WRITE_DATA2 =>
           flash_memory_data_o <= X"00A0";
           flash_memory_fd_oe  <= '1';
           flash_memory_cs_n   <= cs_i;
           flash_memory_we_n   <= we_i;
           counter_reset       <= counter_reset_i;
           counter_top         <= counter_top_i;
           wr_start            <= '1';
           if (wr_done = '1') then
              fsm_state <= STATE_WRITE_DATA3;
           end if;
        -- FLASH single word program - Store address & data
        when STATE_WRITE_DATA3 =>
           flash_memory_adress <= address_counter;
           flash_memory_data_o <= DWR(31 downto 16);
           flash_memory_fd_oe  <= '1';
           flash_memory_cs_n   <= cs_i;
           flash_memory_we_n   <= we_i;
           counter_reset       <= counter_reset_i;
           counter_top         <= counter_top_i;
           wr_start            <= '1';
           if (wr_done = '1') then
              fsm_state     <= STATE_WRITE_WAIT1;
              wr_start      <= '0';
              counter_reset <= '1';
              counter_top   <= conv_std_logic_vector(4, counter_top'length ); -- Delay value experimental from chipscope
           end if;
        -- Wait until the FLASH write opeartion is done
        when STATE_WRITE_WAIT1 =>
           flash_memory_fd_oe  <= '0';
           flash_memory_oe_n   <= '0';           
           flash_memory_cs_n   <= '0';
           flash_memory_we_n   <= '1';
           counter_reset       <= '0';
           if (flash_data(7) = data23) and
             ((counter_finished = '1') and (counter_reset = '0')) then
              fsm_state <= STATE_WRITE_DATA0;
              flash_memory_oe_n  <= '1';
              counter_reset      <= '1';
              rdy_i              <= '1';
           end if;
           
        --  Reset the Unlock-bypass state
        when STATE_LOCK_RESET0 =>
           flash_memory_data_o <= X"0090";
           flash_memory_fd_oe  <= '1';
           flash_memory_cs_n   <= cs_i;
           flash_memory_we_n   <= we_i;
           counter_reset       <= counter_reset_i;
           counter_top         <= counter_top_i;
           wr_start            <= '1';
           if (wr_done = '1') then
              fsm_state <= STATE_LOCK_RESET1;
           end if;
           
        when STATE_LOCK_RESET1 =>
           flash_memory_data_o(7 downto 0) <= X"00";
           flash_memory_fd_oe  <= '1';
           flash_memory_cs_n   <= cs_i;
           flash_memory_we_n   <= we_i;
           counter_reset       <= counter_reset_i;
           counter_top         <= counter_top_i;
           wr_start            <= '1';
           if (wr_done = '1') then
              fsm_state <= STATE_IDLE;
              wr_start         <= '0';
           end if;           
           
        -- FLASH memory read 
        when STATE_READ0 => 
           flash_memory_cs_n <= '0';
           flash_memory_oe_n <= '0';
           counter_reset     <= '0';
           if (counter_finish = '1') then
              fsm_state        <= STATE_READ1;
              DRD(15 downto 0) <= flash_memory_data;
              counter_reset    <= '1';
              flash_memory_adress <= address_counter;
              counter_top      <= conv_std_logic_vector(PAGE_MODE_ACCESS_TIME, counter_top'length );
            end if;
        -- 
        when STATE_READ1 => 
           flash_memory_cs_n   <= '0';
           flash_memory_oe_n   <= '0';
           counter_reset       <= '0';
           if (counter_finish = '1') then
              fsm_state         <= STATE_IDLE;
              DRD(31 downto 16) <= flash_memory_data;
              DRD_VAL           <= '1';
              flash_memory_cs_n <= '1';
              flash_memory_oe_n <= '1';
              counter_reset     <= '1';
            end if;
        -- 
        when STATE_PS_READ0 => 
           psram_cs_n        <= '0'; -- Select PSRAM
           flash_memory_oe_n <= '0'; -- 
           counter_reset     <= '0';
           if (counter_finish = '1') then
              fsm_state        <= STATE_PS_READ1;
              DRD(15 downto 0) <= flash_memory_data;
              counter_reset    <= '1';
              flash_memory_adress <= address_counter;
              counter_top      <= conv_std_logic_vector(PSRAM_PAGE_READ_ACCESS_TIME, counter_top'length );
           end if;
        -- 
        when STATE_PS_READ1 => 
           psram_cs_n          <= '0'; -- Select PSRAM
           flash_memory_oe_n   <= '0';
           counter_reset       <= '0';
           if (counter_finish = '1') then
              fsm_state         <= STATE_IDLE;
              DRD(31 downto 16) <= flash_memory_data;
              DRD_VAL           <= '1';
              psram_cs_n        <= '1'; -- Select PSRAM
              flash_memory_oe_n <= '1';
              counter_reset     <= '1';
           end if;
            
        when STATE_PS_WRITE0 => 
           psram_cs_n          <= '0'; -- Select PSRAM
           flash_memory_oe_n   <= '1'; -- 
           flash_memory_we_n   <= '0'; -- Write enable
           counter_reset       <= '0';
           flash_memory_data_o <= DWR(15 downto 0);
           flash_memory_fd_oe  <= '1'; -- Enable data output
           if (counter_finish = '1') then
              fsm_state         <= STATE_PS_WRITE1;
              counter_reset     <= '1';
              flash_memory_we_n <= '1'; 
              psram_cs_n        <= '1'; 
              flash_memory_adress <= address_counter;
              counter_top        <= conv_std_logic_vector(PSRAM_WRITE_CYCLE_TIME, counter_top'length );
           end if;
        -- 
        when STATE_PS_WRITE1 => 
           psram_cs_n          <= '0'; -- Select PSRAM
           flash_memory_oe_n   <= '1'; -- 
           flash_memory_we_n   <= '0'; -- Write enable
           counter_reset       <= '0';
           flash_memory_fd_oe  <= '1'; -- Enable data output
           flash_memory_data_o <= DWR(31 downto 16);
           if (counter_finish = '1') then
              fsm_state         <= STATE_IDLE;
              psram_cs_n        <= '1'; -- Select PSRAM
              counter_reset     <= '1'; -- 
              flash_memory_we_n <= '1'; -- Write enable
           end if;
        when others =>
      end case;
    end if;
  end process;
  
end structural;