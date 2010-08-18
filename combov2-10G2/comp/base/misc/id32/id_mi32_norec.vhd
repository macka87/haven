-- id_mi32.vhd: Combo6 design identification, MI32 interface
-- Copyright (C) 2003 CESNET, Liberouter project
-- Author(s): Patrik Beck <xbeckp00@stud.fit.vutbr.cz>
--            Viktor Pus <pus@liberouter.org>
--            Stepan Friedl <friedl@liberouter.org>
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
-- TODO: -

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.numeric_std.all;

library unisim;
use unisim.vcomponents.ALL;

-- -------------------------------------------------------------
--       Entity :   ID_COMP
-- -------------------------------------------------------------
--* Design identification module
entity ID_COMP_MI32_NOREC is
   Generic (
      PROJECT_ID     : std_logic_vector(15 downto 0):= X"0000";
      SW_MAJOR       : std_logic_vector( 7 downto 0):=   X"00";
      SW_MINOR       : std_logic_vector( 7 downto 0):=   X"00";
      HW_MAJOR       : std_logic_vector(15 downto 0):= X"0000";
      HW_MINOR       : std_logic_vector(15 downto 0):= X"0000";
      PROJECT_TEXT   : std_logic_vector(255 downto 0) :=
      X"0000000000000000000000000000000000000000000000000000000000000000";
      --* Number of DMA channels FPGA -> RAM
      RX_CHANNELS    : std_logic_vector(7 downto 0):= X"FF";
      --* Number of DMA channels RAM -> FPGA
      TX_CHANNELS    : std_logic_vector(7 downto 0):= X"FF";
      --* Enable Sysmon instantion (tested on Virtex 5 FPGAs)
      SYSMON_EN      : boolean := true;
      --+ This module version (should not be changed when instantiating)
      ID_MAJOR       : std_logic_vector(7 downto 0) := X"01";
      ID_MINOR       : std_logic_vector(7 downto 0) := X"01";
      --+ NetCOPE version
      NETCOPE_MAJOR  : std_logic_vector(7 downto 0) := X"00";
      NETCOPE_MINOR  : std_logic_vector(7 downto 0) := X"00";
      --* Date and time of building
      BUILD_TIME     : std_logic_vector(31 downto 0) := X"00000000";
      --* Builder's Unix User ID
      BUILD_UID      : std_logic_vector(31 downto 0) := X"00000000";
      --* CLK_ICS frequency in MHz
      ICS_FREQUENCY  : std_logic_vector(15 downto 0) := X"00BB"; -- 187 MHz
      --* Number of cycles when input INTERRUPT_IN is ignored
      INTERRUPT_IGNORE : std_logic_vector(15 downto 0) := X"00FF";
      --+ User generics (no default meaning)
      USER_GENERIC0  : std_logic_vector(31 downto 0) := X"00000000";
      USER_GENERIC1  : std_logic_vector(31 downto 0) := X"00000000";
      USER_GENERIC2  : std_logic_vector(31 downto 0) := X"00000000";
      USER_GENERIC3  : std_logic_vector(31 downto 0) := X"00000000"
   );
   port (
      --+ Basic interface
      CLK            : in std_logic;
      RESET          : in std_logic;

      --* Contents of the COMMAND register (writable by SW)
      COMMAND        : out std_logic_vector(31 downto 0);
      
      --* Signals readable by SW
      STATUS         : in  std_logic_vector(127 downto 0);
      --* Write enables for four 32bit words of STATUS
      WE             : in  std_logic_vector(3 downto 0);  

      --* Sysmon raised alarm, as programmed by SW
      SYSMON_ALARM   : out std_logic;
      
      ----------------------------------------------------------------
      --* Interrupt input, each one-cycle pulse sets INTERRUPT register 
      --* and is forwarded to INTERRUPT_OUT
      INTERRUPT_IN   : in  std_logic_vector(31 downto 0);
      --* Allows INTERRUPT_IN
      INTR_RDY_IN   : out std_logic;

      --* Output interface Interrupt request
      INTERRUPT_OUT  : out std_logic;
      --* Output interface Data
      INTR_DATA_OUT  : out std_logic_vector(4 downto 0);
      --* Output interface Ready for next request
      INTR_RDY_OUT   : in  std_logic;

      ----------------------------------------------------------------
      --+ MI32 interface
      MI_DWR   : in  std_logic_vector(31 downto 0);
      MI_ADDR  : in  std_logic_vector(31 downto 0);
      MI_RD    : in  std_logic;
      MI_WR    : in  std_logic;
      MI_BE    : in  std_logic_vector( 3 downto 0);
      MI_DRD   : out std_logic_vector(31 downto 0);
      MI_ARDY  : out std_logic;
      MI_DRDY  : out std_logic
   );
end ID_COMP_MI32_NOREC;

-- -------------------------------------------------------------
--       Architecture :   structural description
-- -------------------------------------------------------------
architecture full of ID_COMP_MI32_NOREC is

   -- ----------------- Signal declaration --------------------

   signal reg_address : std_logic_vector(31 downto 0);

   -- Choosed local bus data
   signal mx_string_data   : std_logic_vector(31 downto 0);
   signal mx_ctrl_data     : std_logic_vector(31 downto 0);
   signal mx_ctrl2_data    : std_logic_vector(31 downto 0);
   signal mx_ctrl3_data    : std_logic_vector(31 downto 0);

   signal mx_dout          : std_logic_vector(31 downto 0);
   signal reg_mx_dout      : std_logic_vector(31 downto 0);

   -- Data register
   signal reg_string_data  : std_logic_vector(31 downto 0);
   signal reg_ctrl_data    : std_logic_vector(31 downto 0);
   signal reg_ctrl2_data   : std_logic_vector(31 downto 0);
   signal reg_ctrl3_data   : std_logic_vector(31 downto 0);

   -- Auxiliary wires
   signal neg_data_in      : std_logic_vector(31 downto 0);

   -- Command register
   signal reg_cmd          : std_logic_vector(31 downto 0);

   signal reg_status       : std_logic_vector(127 downto 0);

   -- Register signals
   signal reg_neg    : std_logic_vector(31 downto 0);
   signal reg_neg_we : std_logic;
   signal neg_cs     : std_logic;
   signal reg_drdy   : std_logic;
   signal reg_drdy2  : std_logic;
   -- Sysmon
   signal sysmon_bank : std_logic_vector( 1 downto 0);
   signal sysmon_den  : std_logic;
   signal sysmon_wen  : std_logic;
   signal reg_sysmon_wen : std_logic;
   signal sysmon_do   : std_logic_vector(15 downto 0);
   signal sysmon_addr : std_logic_vector( 6 downto 0);
   signal sysmon_drdy : std_logic;   
   signal sysmon_drdy_rd : std_logic;   
   signal sysmon_alm  : std_logic_vector(2 downto 0);
   signal sysmon_alm_or:std_logic;

   -- Interrupts
   signal reg_intr         : std_logic_vector(31 downto 0);
   signal reg_intr_rd      : std_logic;
   signal sig_intr_in      : std_logic_vector(31 downto 0);
   signal sig_intr_rdy_in  : std_logic;
   signal cnt_intr_ignore  : std_logic_vector(15 downto 0);

   -- ModelSim complaints when this signal is not used
   signal dummy_channel    : std_logic_vector(4 downto 0);

begin

   -- --------------- Output and auxiliary -------------------------
   neg_data_in <= not MI_DWR;


   -- register reg_neg ----------------------------------------------------
   reg_negp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_neg( 7 downto  0) <= (others => '1');
            reg_neg(15 downto  8) <= (others => '1');
            reg_neg(23 downto 16) <= (others => '1');
            reg_neg(31 downto 24) <= (others => '1');
         else
            if (reg_neg_we = '1') then
               if MI_BE(0) = '1' then
                  reg_neg(7 downto 0) <= neg_data_in(7 downto 0);
               end if;
               if MI_BE(1) = '1' then
                  reg_neg(15 downto 8) <= neg_data_in(15 downto 8);
               end if;
               if MI_BE(2) = '1' then
                  reg_neg(23 downto 16) <= neg_data_in(23 downto 16);
               end if;
               if MI_BE(3) = '1' then
                  reg_neg(31 downto 24) <= neg_data_in(31 downto 24);
               end if;
            end if;
         end if;
      end if;
   end process;

   neg_cs <= '1' when (MI_ADDR(7) = '0') and (MI_ADDR(5 downto 2) = 0) else '0';
   reg_neg_we <= neg_cs and MI_WR;

   -- register reg_cmd -----------------------------------------------
   reg_cmd_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if MI_WR = '1' and MI_ADDR(7) = '0' and MI_ADDR(5 downto 2) = "0011" 
         then
            if MI_BE(0) = '1' then
               reg_cmd(7 downto 0) <= MI_DWR(7 downto 0);
            end if;
            if MI_BE(1) = '1' then
               reg_cmd(15 downto 8) <= MI_DWR(15 downto 8);
            end if;
            if MI_BE(2) = '1' then
               reg_cmd(23 downto 16) <= MI_DWR(23 downto 16);
            end if;
            if MI_BE(3) = '1' then
               reg_cmd(31 downto 24) <= MI_DWR(31 downto 24);
            end if;
         end if;
      end if;
   end process;
   
   -- register sysmon_bank -----------------------------------------------
GEN_SYSMON_BANK_REG: if (SYSMON_EN) generate
   
   reg_sysmon_bank : process(CLK)
   begin
      if CLK'event and CLK = '1' then 
         if MI_WR = '1' and MI_ADDR(7 downto 2) = "010001" and MI_BE(0) = '1' -- 0x44
         then
            sysmon_bank <= MI_DWR(1 downto 0);
         end if;         
      end if;
   end process;
   
end generate;

NO_SYSMON_BANK_REG: if (not SYSMON_EN) generate
   sysmon_bank <= (others => '0');
end generate;

   -- register reg_status --------------------------------------------
   reg_status_gen : for i in 0 to 3 generate
      reg_status_p : process(CLK)
      begin
         if CLK'event and CLk = '1' then
            if WE(i) = '1' then
               reg_status((32*i)+31 downto 32*i) <= STATUS((32*i)+31 downto 32*i);
            end if;
         end if;
      end process;
   end generate;

   -- ----------------- Control data multiplex -----------------------
   mx_ctrl_data_p : process(MI_ADDR, reg_neg, reg_cmd, reg_status)
   begin
         mx_ctrl_data  <= (others => '0');
         case MI_ADDR(4 downto 2) is
            when "000" =>   mx_ctrl_data  <= reg_neg;
            when "001" =>   mx_ctrl_data  <= PROJECT_ID&SW_MAJOR&SW_MINOR;
            when "010" =>   mx_ctrl_data  <= HW_MAJOR&HW_MINOR;
            when "011" =>   mx_ctrl_data  <= reg_cmd;
            when "100" =>   mx_ctrl_data  <= reg_status(31 downto 0);
            when "101" =>   mx_ctrl_data  <= reg_status(63 downto 32);
            when "110" =>   mx_ctrl_data  <= reg_status(95 downto 64);
            when others =>  mx_ctrl_data  <= reg_status(127 downto 96);
         end case;
   end process mx_ctrl_data_p;

   -- ---------------- Control data 2 multiplex ----------------------
   mx_ctrl2_data_p : process(MI_ADDR, sysmon_bank, reg_intr)
   begin
         mx_ctrl2_data  <= (others => '0');
         case MI_ADDR(4 downto 2) is
            when "000" => mx_ctrl2_data <= ICS_FREQUENCY -- 0x040
                                             & TX_CHANNELS & RX_CHANNELS;
            when "001" => mx_ctrl2_data <= (31 downto 2 => '0')  -- 0x044
                                             & sysmon_bank;
            when "010" => mx_ctrl2_data <= NETCOPE_MAJOR & NETCOPE_MINOR &
                                           ID_MAJOR & ID_MINOR;  -- 0x48
            when "011" => mx_ctrl2_data <= BUILD_TIME;           -- 0x4C
            when "100" => mx_ctrl2_data <= BUILD_UID;            -- 0x50
            when "101" => mx_ctrl2_data <= reg_intr;             -- 0x54
            when "110" => mx_ctrl2_data <= USER_GENERIC0;        -- 0x58
            when "111" => mx_ctrl2_data <= USER_GENERIC1;        -- 0x5C
            when others => mx_ctrl2_data <= (others => '0');
         end case;
   end process mx_ctrl2_data_p;

   -- ---------------- Control data 3 multiplex ----------------------
   mx_ctrl3_data_p : process(MI_ADDR)
   begin
         mx_ctrl3_data  <= (others => '0');
         case MI_ADDR(4 downto 2) is
            when "000" => mx_ctrl3_data <= USER_GENERIC2;        -- 0x60
            when "001" => mx_ctrl3_data <= USER_GENERIC3;        -- 0x64
            when others => mx_ctrl3_data <= (others => '0');
         end case;
   end process mx_ctrl3_data_p;

   -- ------------------- Pipelined registers ------------------------
   reg_ctrl_data_p : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         reg_ctrl_data <= mx_ctrl_data;
         reg_string_data <= mx_string_data;
         reg_ctrl2_data <= mx_ctrl2_data;
         reg_ctrl3_data <= mx_ctrl3_data;
      end if;
   end process reg_ctrl_data_p;

   reg_address_p : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (MI_WR = '1') or (MI_RD = '1') then
            reg_address <= MI_ADDR;
         end if;
      end if;
   end process reg_address_p;

   reg_drdy_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_drdy <= '0';
            reg_drdy2 <= '0';
         else
            if (SYSMON_EN) then
               reg_drdy <= MI_RD and (not MI_ADDR(7));
            else
               reg_drdy <= MI_RD;
            end if;
            reg_drdy2 <= reg_drdy or sysmon_drdy_rd;
         end if;
      end if;
   end process;

   -- --------------------- Output multiplex --------------------------
   mx_dout_p : process(reg_address, reg_ctrl_data,
                       reg_string_data, reg_ctrl2_data, reg_ctrl3_data, 
                       sysmon_do)
   begin 
      if (reg_address(7) = '0') or (not SYSMON_EN) then -- 0x80
         case reg_address(6 downto 5) is
            when "00"   => mx_dout <= reg_ctrl_data;  -- 0x00...0x1f
            when "01"   => mx_dout <= reg_string_data;-- 0x20...0x3f
            when "10"   => mx_dout <= reg_ctrl2_data; -- 0x40...0x5f
            when "11"   => mx_dout <= reg_ctrl3_data; -- 0x60...0x7f
            when others => mx_dout <= (others => '0');
         end case;
      else
          mx_dout <= X"0000" & sysmon_do;
      end if;
   end process;

   reg_dout_p : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         reg_mx_dout <= mx_dout;
      end if;
   end process reg_dout_p;

   MI_DRD <= reg_mx_dout;
   MI_ARDY <= MI_RD or MI_WR;
   MI_DRDY <= reg_drdy2;

   COMMAND <= reg_cmd;

   -- -----------------------------------------------------------------
   -- ------------------ String address decoder -----------------------
   -- -----------------------------------------------------------------
   --                     (Hard wired solution)
   mx_str_data_p : process(MI_ADDR) -- Synchronous write ro regx
   begin
         mx_string_data  <= (others => '0');
         case MI_ADDR(4 downto 2) is
            when "000" => mx_string_data  <= PROJECT_TEXT(239 downto 224)&PROJECT_TEXT(255 downto 240);
            when "001" => mx_string_data  <= PROJECT_TEXT(207 downto 192)&PROJECT_TEXT(223 downto 208);
            when "010" => mx_string_data  <= PROJECT_TEXT(175 downto 160)&PROJECT_TEXT(191 downto 176);
            when "011" => mx_string_data  <= PROJECT_TEXT(143 downto 128)&PROJECT_TEXT(159 downto 144);
            when "100" => mx_string_data  <= PROJECT_TEXT(111 downto  96)&PROJECT_TEXT(127 downto 112);
            when "101" => mx_string_data  <= PROJECT_TEXT( 79 downto  64)&PROJECT_TEXT( 95 downto  80);
            when "110" => mx_string_data  <= PROJECT_TEXT( 47 downto  32)&PROJECT_TEXT( 63 downto  48);
            when "111" => mx_string_data  <= PROJECT_TEXT( 15 downto   0)&PROJECT_TEXT( 31 downto  16);
            when others => mx_string_data  <= (others => '0');
         end case;
   end process mx_str_data_p;
   
   --* -----------------------------------------------------------------
   --* ------------------     Interrupt manager      -------------------
   --* -----------------------------------------------------------------      
   intr_man_i : entity work.INTERRUPT_MANAGER
   generic map(
      PULSE    => X"FFFFFFFF" -- All inputs must be pulses
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      INTERRUPT_IN   => sig_intr_in,
      INTR_RDY_IN    => sig_intr_rdy_in,

      INTERRUPT_OUT  => INTERRUPT_OUT,
      INTR_DATA_OUT  => INTR_DATA_OUT,
      INTR_RDY_OUT   => INTR_RDY_OUT
   );

   INTR_RDY_IN <= sig_intr_rdy_in;

   -- Count a few cyclew after RESET, before INTERRUPT_IN is propagated
   cnt_intr_ignore_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            cnt_intr_ignore <= INTERRUPT_IGNORE;
         else
            if cnt_intr_ignore /= X"0000" then
               cnt_intr_ignore <= cnt_intr_ignore - 1;
            end if;
         end if;
      end if;
   end process;

   -- INTERRUPT_IN multiplexer
   sig_intrr_in_p : process(INTERRUPT_IN, cnt_intr_ignore, RESET)
   begin
      if (cnt_intr_ignore /= X"0000") or (RESET = '1') then
         sig_intr_in <= X"00000000";
      else
         sig_intr_in <= INTERRUPT_IN;
      end if;
   end process;

   reg_intr_gen : for i in 0 to 31 generate
      --* Interrupt register
      reg_intr_p : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            if RESET = '1' then
               reg_intr(i) <= '0';
            else
               if sig_intr_rdy_in = '1' and INTERRUPT_IN(i) = '1' then
                  reg_intr(i) <= '1';
               end if;
               if reg_intr_rd = '1' then
                  reg_intr(i) <= '0';
               end if;
            end if;
         end if;
      end process;
   end generate;

   reg_intr_rd_p : process(MI_ADDR, MI_RD)
   begin
      if MI_RD = '1' and MI_ADDR(7 downto 2) = "010101" then -- 0x54
         reg_intr_rd <= '1';
      else
         reg_intr_rd <= '0';
      end if;
   end process;

   -- -----------------------------------------------------------------
   -- ------------------     System monitor         -------------------
   -- -----------------------------------------------------------------      
   
GEN_SYSMON: if (SYSMON_EN) generate
   
   sysmon_den  <= MI_ADDR(7) and (MI_RD or MI_WR);
   sysmon_wen  <= MI_ADDR(7) and MI_WR;

   reg_sysmon_wen_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if sysmon_den = '1' then
            reg_sysmon_wen <= sysmon_wen;
         end if;
      end if;
   end process;

   sysmon_addr <= sysmon_bank & MI_ADDR(6 downto 2);
   
   SYSMON_INST : SYSMON
   generic map(
      INIT_40 => X"0000", -- config reg 0
      INIT_41 => X"20FF", -- config reg 1
      INIT_42 => X"1800", -- config reg 2
      INIT_48 => X"0100", -- Sequencer channel selection
      INIT_49 => X"0000", -- Sequencer channel selection
      INIT_4A => X"0000", -- Sequencer Average selection
      INIT_4B => X"0000", -- Sequencer Average selection
      INIT_4C => X"0000", -- Sequencer Bipolar selection
      INIT_4D => X"0000", -- Sequencer Bipolar selection
      INIT_4E => X"0000", -- Sequencer Acq time selection
      INIT_4F => X"0000", -- Sequencer Acq time selection
      INIT_50 => X"b5ed", -- Temp alarm trigger 
      INIT_51 => X"5999", -- Vccint upper alarm limit 
      INIT_52 => X"e000", -- Vccaux upper alarm limit
      INIT_54 => X"a93a", -- Temp alarm reset 
      INIT_55 => X"5111", -- Vccint lower alarm limit 
      INIT_56 => X"caaa", -- Vccaux lower alarm limit
      INIT_57 => X"ae4e"  -- Temp alarm OT reset
   )
   port map (
      RESET             => RESET,   
      -- DRP ---------------------
      DADDR(6 downto 0) => sysmon_addr, 
      DCLK              => CLK,
      DEN               => sysmon_den,
      DI(15 downto 0)   => MI_DWR(15 downto 0),
      DWE               => sysmon_wen,
      DO(15 downto 0)   => sysmon_do,
      DRDY              => sysmon_drdy,
      --
      ALM(2)            => sysmon_alm(0), -- VCCAUX_ALARM_OUT,
      ALM(1)            => sysmon_alm(1), -- VCCINT_ALARM_OUT,
      ALM(0)            => sysmon_alm(2), -- USER_TEMP_ALARM_OUT,
      OT                => open, -- OT_OUT            
      -- 
      VAUXN(15 downto 0)  => "0000000000000000",
      VAUXP(15 downto 0)  => "0000000000000000",
      CHANNEL(4 downto 0) => dummy_channel,
      VN                  => '0',
      VP                  => '0',
      CONVST              => '0',
      CONVSTCLK           => '0',
      BUSY                => open,
      EOC                 => open,
      EOS                 => open,
      JTAGBUSY            => open,
      JTAGLOCKED          => open,
      JTAGMODIFIED        => open
   );

   sysmon_alm_or <= sysmon_alm(0) or sysmon_alm(1) or sysmon_alm(2);
   SYSMON_ALARM <= sysmon_alm_or;
   sysmon_drdy_rd <= sysmon_drdy and (not reg_sysmon_wen);

end generate;

NO_SYSMON: if (not SYSMON_EN) generate
   sysmon_do   <= (others => '0');
   sysmon_drdy_rd <= '0';
   SYSMON_ALARM <= '0';
end generate;

end full;
