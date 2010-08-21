--
-- fifo_async_blocka.vhd: Asynchronous Block FIFO full architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Jan Kastil <xkasti00@stud.fit.vutbr.cz>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Cache package
use work.fifo_pkg.all;

-- Math package - log2 function
use work.math_pack.all;
-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on

architecture full of fifo_async_blocka is

constant FADDR          : integer := LOG2(items)-1;

signal StatusSig        : std_logic_vector(FADDR downto 0);

signal read_cnt         : std_logic_vector(FADDR downto 0);
signal read_dis     : std_logic_vector(FADDR downto 0);
signal read_dis_last: std_logic_vector(FADDR downto 0);

signal read_gray        : std_logic_vector(FADDR downto 0);
signal read_nextgray    : std_logic_vector(FADDR downto 0);
signal read_lastgray    : std_logic_vector(FADDR downto 0);
signal read_dis_nextgray: std_logic_vector(FADDR downto 0);
signal read_dis_gray    : std_logic_vector(FADDR downto 0);
signal read_dis_lastgray: std_logic_vector(FADDR downto 0);

signal write_cnt        : std_logic_vector(FADDR downto 0);
signal write_cnt1       : std_logic_vector(FADDR downto 0);
signal lastwritedblock  : std_logic_vector(FADDR downto 0);
signal write_gray       : std_logic_vector(FADDR downto 0);
signal write_nextgray   : std_logic_vector(FADDR downto 0);
signal write_dis_gray   : std_logic_vector(FADDR downto 0);
signal write_dis_nextgray: std_logic_vector(FADDR downto 0);

signal reg_status         : std_logic_vector(FADDR downto 0);
signal read_truegray      : std_logic_vector(FADDR downto 0);
signal reg_read_truegray  : std_logic_vector(FADDR downto 0);
signal read_bin           : std_logic_vector(FADDR downto 0);
signal reg_cnt_write_addr : std_logic_vector(FADDR downto 0);


signal fcomp            : std_logic_vector(FADDR downto 0);
signal ecomp            : std_logic_vector(FADDR downto 0);
signal emuxcyo          : std_logic_vector(FADDR+1 downto 0);
signal fmuxcyo          : std_logic_vector(FADDR+1 downto 0);

signal fcomp2            : std_logic_vector(FADDR downto 0);
signal ecomp2            : std_logic_vector(FADDR downto 0);
signal emuxcyo2          : std_logic_vector(FADDR+1 downto 0);
signal fmuxcyo2          : std_logic_vector(FADDR+1 downto 0);

signal fcomp3            : std_logic_vector(FADDR downto 0);
signal ecomp3            : std_logic_vector(FADDR downto 0);
signal emuxcyo3          : std_logic_vector(FADDR+1 downto 0);
signal fmuxcyo3          : std_logic_vector(FADDR+1 downto 0);

signal fcomp4            : std_logic_vector(FADDR downto 0);
signal ecomp4            : std_logic_vector(FADDR downto 0);
signal emuxcyo4          : std_logic_vector(FADDR+1 downto 0);
signal fmuxcyo4          : std_logic_vector(FADDR+1 downto 0);


--Vector Size contains size of actual Reading or Writing block for discard purposes
signal DisAdrW          : std_logic_vector(FADDR downto 0);
signal EndAdr           : std_logic_vector(FADDR downto 0);
signal EndAdr1          : std_logic_vector(FADDR downto 0);
signal EndAdrReg        : std_logic_vector(FADDR downto 0);

signal DWE              : std_logic;
signal DRE1             : std_logic;
signal DRE              : std_logic;
signal full_allow       : std_logic;
signal empty_allow      : std_logic;
signal emptyg           : std_logic;
signal fullg            : std_logic;
signal emptyg2           : std_logic;
signal fullg2            : std_logic;
signal emptyg3           : std_logic;
signal fullg3            : std_logic;
signal emptyg4           : std_logic;
signal fullg4            : std_logic;

signal ARE              : std_logic;
signal AWE              : std_logic;

signal EndBlockW        : std_logic;
signal EndBlockR        : std_logic;
signal AdrEq            : std_logic;
signal Diff             : std_logic;
signal fl               : std_logic;
signal emp              : std_logic;
signal emp1             : std_logic;
signal emp2             : std_logic;
signal emp3             : std_logic;
signal emp4             : std_logic;

signal Valid            : std_logic;
signal Valid2           : std_logic;
signal DiscardingR      : std_logic;
signal DiscardingW      : std_logic;
signal EndAdrValid      : std_logic;
signal EndAdrValidReg   : std_logic;
signal EmptyAdr         : std_logic;
signal PostReset        : std_logic;
signal ReadEndAdress    : std_logic;
signal BlFin            : std_logic;
signal BlFinReg         : std_logic;
signal BlReady          : std_logic;
signal WrDiscardStatus  : std_logic;
signal RdDiscardStatus  : std_logic;
signal RdDiscardStatusReg : std_logic;
signal Stat             :std_logic_vector(1 downto 0);

begin 
Stat(1) <= RdDiscardStatus xor RdDiscardStatusReg;
Stat(0) <= WrDiscardStatus;

NON_PREFETCH_GEN: if(prefetch = false) generate
   DRE1 <= DRE;
end generate;

PREFETCH_GEN: if(prefetch = true) generate
   DRE1 <= not emp1;
end generate;

--Use grey counters
--cnt_read_addr_up : entity work.cnt
--   generic map(
--      WIDTH => FADDR+1,
--      DIR   => up,
--      CLEAR => false
--   )
--   port map(
--      RESET => RESET,
--      CLK   => RD_CLK,
--      DO    => read_cnt,
--     CLR   => '0',
--      CE    => DRE
--   );

cnt_read_addr_up : process(reset,RD_CLK,DRE)
begin
   if(Reset='1') then
      read_cnt <= (others =>'0');
   elsif (RD_CLK'event and RD_CLK='1') then
      if(RdDiscardStatus /= RdDiscardStatusReg) then
         read_cnt<=EndAdr;
      elsif(DRE='1') then
         read_cnt<=read_cnt+1;
      end if;
   end if;
end process;

--cnt_write_addr_up : entity work.cnt
--   generic map(
--      WIDTH => FADDR+1,
--      DIR   => up,
--      CLEAR => false
--   )
--   port map(
--      RESET => RESET,
--      CLK   => WR_CLK,
--      DO    => write_cnt1,
--      CLR   => '0',
--      CE    => DWE
--   );

cnt_write_addr_up: process(Reset,WR_CLK,DWE,WrDiscardStatus)
begin
   if(reset='1') then
      write_cnt1 <=  conv_std_logic_vector(1, FADDR+1);
   elsif(WR_CLK'event and WR_CLK='1') then
      if(DWE = '1') then
         write_cnt1 <= write_cnt1+1;
      elsif(WrDiscardStatus = '1') then
         write_cnt1 <= lastwritedblock+1;
  
      end if;
   end if;
end process;

write_cnt_gen_proc: process(WR_CLK,Reset,WrDiscardStatus)
begin
   if(reset = '1') then 
      write_cnt <= (others => '0');
   elsif(WR_CLK'event and WR_CLK = '1') then
     if(DWE='1') then
        write_cnt <= write_cnt1;
     elsif(WrDiscardStatus = '1') then
        write_cnt <=lastwritedblock;
     end if;
   end if;
end process;

write_next_proc: process (WR_CLK,RESET)
begin
   if(RESET = '1') then 
      write_nextgray <= conv_std_logic_vector(2**(FADDR),FADDR+1);
   elsif(WR_CLK'event and WR_CLK='1') then
      if(DWE = '1') then
      write_nextgray(FADDR) <= write_cnt(FADDR);
      for i in FADDR-1 downto 0 loop
         write_nextgray(i) <= write_cnt(i+1) xor write_cnt(i);
      end loop;
      end if;
   end if;
end process;

write_gray_proc: process (WR_CLK,RESET,DWE)
begin
   if(RESET='1') then 
      write_gray <= conv_std_logic_vector(2**(FADDR)+1,FADDR+1);  
   elsif (WR_CLK'event and WR_CLK='1') then
      if(DWE = '1') then
         write_gray <= write_nextgray;
      end if;
   end if;
end process;
   

read_next_proc: process (RD_CLK, RESET)
   begin
      if (RESET = '1') then
         read_nextgray <= conv_std_logic_vector(2**(FADDR), FADDR+1);
      elsif (RD_CLK'event and RD_CLK = '1') then
         if(DRE='1') then 
            -- binary to gray convertor
            read_nextgray(FADDR) <= read_cnt(FADDR);
            for i in FADDR-1 downto 0 loop
               read_nextgray(i) <= read_cnt(i+1) xor read_cnt(i);
            end loop;
         end if;
      end if;
   end process;


read_proc: process(RD_CLK,RESET,DRE)
begin
   if(RESET='1') then 
      read_gray <= conv_std_logic_vector(2**(FADDR)+1, FADDR+1);
   elsif(RD_CLK'event and RD_CLK = '1') then
      if(DRE = '1') then
         read_gray <= read_nextgray;
      end if;
   end if;
end process;

read_last_proc: process(RD_CLK,RESET,DRE)
begin
   if(RESET='1') then 
       read_lastgray <= conv_std_logic_vector(2**(FADDR)+3, FADDR+1);
   elsif (RD_CLK'event and RD_CLK='1') then 
      if(DRE = '1') then 
         read_lastgray <= read_gray;
      end if;
   end if;
end process;

--empty and full signal generation
   DRE <= (RD and not emp);

   full_allow <= (fl or WR);
   empty_allow <= (emp or RD);

empty1_gen_proc: process (RD_CLK, RESET, empty_allow)
   begin
      if (RESET = '1') then
         emp1 <= '1';
      elsif (RD_CLK'event and RD_CLK = '1') then
         if (empty_allow = '1') then
            emp1 <= emptyg;
         end if;
      end if;
   end process;

empty_gen_proc: process(RD_CLK,RESET,DRE,emp1)
begin
   if(RESET='1') then 
      emp<='1';
   elsif(RD_CLK'event and RD_CLK='1') then
      --if(RD='1') then
      if(Stat = "00") then
         emp <= emp1;
      elsif(Stat = "01") then
         emp <= emp2;
      elsif(Stat = "10") then
         emp <=emp3;
      else
         emp <= emp4;
      end if;
      -- end if;
   end if;
end process;

full_gen_proc: process (WR_CLK, RESET, full_allow)
   begin
     if (RESET = '1') then
        fl<= '1';
     elsif (WR_CLK'event and WR_CLK = '1') then
        if (full_allow = '1') then
           if(Stat = "00") then
              fl <= fullg;
           elsif(Stat = "01") then
              fl <= fullg2;
           elsif(Stat = "10") then
              fl <= fullg3;
           else fl <= fullg4;
           end if;
        end if;
     end if;
   end process;
 -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  ECOMP_GEN : for i in 0 to FADDR generate
     ecomp(i) <= (not (write_gray(i) xor read_gray(i)) and emp) or
                 (not (write_gray(i) xor read_nextgray(i)) and not emp);
  end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   emuxcyo(0)  <= '1';
   emptyg      <= emuxcyo(FADDR+1);
 
   EMUXCY_GEN : for i in 0 to FADDR generate
      emuxcyX: MUXCY_L
      port map (
         DI => '0',
         CI => emuxcyo(i),
         S  => ecomp(i),
         LO => emuxcyo(i+1)
      );
   end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   FCOMP_GEN : for i in 0 to FADDR generate
      fcomp(i) <= (not (read_lastgray(i) xor write_gray(i)) and fl) or
                  (not (read_lastgray(i) xor write_nextgray(i)) and not fl);
   end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   fmuxcyo(0)  <= '1';
   fullg       <= fmuxcyo(FADDR+1);

   FMUXCY_GEN : for i in 0 to FADDR generate
      fmuxcyX: MUXCY_L
      port map (
         DI => '0',
         CI => fmuxcyo(i),
         S  => fcomp(i),
         LO => fmuxcyo(i+1)
      );
   end generate;






   DataMemory: entity work.FIFO_MEM 
      generic map (
         mem_type => mem_type,
	 latency => latency,
	 items => items,
	 item_width => item_width
      )
      port map(
         DI => DI,
         CLKW => WR_CLK,
	 CLKR => RD_CLK,
	 DO =>DO,
	 DO_DV => Valid,
         WRITE_EN =>DWE,
     PIPE_EN => '1',
	 WRITE_ADDR => write_cnt(FADDR downto 0),
	 READ_EN => DRE1,
	 RE_ADDR => read_cnt(FADDR downto 0),
	 RESET => RESET
      );
------------------------------------------------------------------
   --STATUS generation
------------------------------------------------------------------

-- graycode read address generation
   read_truegray_p: process (RD_CLK, RESET)
   begin
      if (RESET='1') then
         read_truegray <= (others=>'0');
      elsif (RD_CLK'event and RD_CLK='1') then
         ----------------------------------------------------
         read_truegray(FADDR) <= read_cnt(FADDR);
         read_truegray_gen : for i in FADDR-1 downto 0 loop
            read_truegray(i) <= read_cnt(i+1) xor read_cnt(i);
         end loop;
      end if;
   end process;

   -- synchronization with WR_CLK
   reg_read_truegray_p: process (WR_CLK, RESET)
   begin
      if (RESET='1') then
         reg_read_truegray <= (others=>'0');
      elsif (WR_CLK'event and WR_CLK='1') then
         reg_read_truegray <= read_truegray;
      end if;
   end process;

   -- transformation to binary format
   read_bin(FADDR) <= reg_read_truegray(FADDR);
   read_bin_gen : for i in FADDR-1 downto 0 generate
      read_bin(i) <= read_bin(i+1) xor reg_read_truegray(i);
   end generate;

   -- registering of cnt_write_addr
   reg_cnt_write_addr_p: process (WR_CLK, RESET)
   begin
      if (RESET='1') then
         reg_cnt_write_addr <= (others=>'0');
      elsif (WR_CLK'event and WR_CLK='1') then
         reg_cnt_write_addr <= write_cnt;
      end if;
   end process;

   -- status computing
   reg_status_p: process (WR_CLK, RESET)
   begin
      if (RESET='1') then
         reg_status <= (others=>'0');
      elsif (WR_CLK'event and WR_CLK='1') then
         --if (regasync_full='0') then
            reg_status <= (reg_cnt_write_addr - read_bin);
         --end if;
      end if;
   end process;
------------------------------------------------------------------------------
--  BlockEnd generation
------------------------------------------------------------------------------ 
VARSIZE:
   if(Block_type = variable_size) generate
      EndBlockW <= Blk_End;
   end generate;

EndBlockMemory: entity work.fifo_async_ord
      generic map (
         items => Items,
	 item_width =>log2(Items),
	 latency =>1,    --Latency must be 1 for discard aplication, latency of block finish must be done separately
	 mem_type => mem_type,
	 prefetch => true 
     )
      port map (
         WR_CLK => wr_clk,
         WR => AWE ,
	 DI => write_cnt1,

	 RD_CLK =>rd_clk,
	 RD => ARE,
	 DO => EndAdr,
	 DO_DV => EndAdrValid,

	 EMPTY => EmptyAdr,
	 FULL => open,
	 STATUS => open,

	 RESET => Reset
   );
NONEDISCARDBLOCK:
if(Discard = NoDiscard) generate
AWE <= DWE and EndBlockW;

   DWE <= (WR and not fl);
WrDiscardStatus <= '0';
RdDiscardStatus <= '0';
RdDiscardStatusReg <= '0';
ARE <= (blfin and not blFinReg) and DRE;
end generate;

AditionalDISCARDREAD:
if(Discard = ReadDiscard) generate
WrDiscardStatus <= '0';
end generate;

AditionalDISCARDWRITE:
if(Discard = WriteDiscard) generate
RdDiscardStatus <= '0';
RdDiscardStatusReg <='0';
end generate;

EndBlockGen_proc: process(EndAdrValid, EndAdr,read_cnt, RD_CLK, Reset)
begin
   if(Reset = '1') then 
      blfin <= '0';
   elsif(RD_CLK'event and RD_CLK='1') then
      if((EndAdr = read_cnt) and EndAdrValid = '1') then
         blfin <= '1';
      else blfin <='0';
      end if;
   end if;
end process;

BlFinRegGen_proc: process(DRE,blfin,RD_CLK,Reset)
begin
   if(Reset='1') then
      blFinReg <='0';
   elsif(RD_CLK'event and RD_CLK='1') then
      if(DRE='1') then
         blFinReg <= BlFin;
      end if;
   end if;
end process;

BlReadygen_proc: process(RD_CLK,DRE,Reset)
begin
   if(Reset='1') then
      blReady <= '0';
   end if;
--   elsif(RD_CLK'event and RD_CLK='1') then
   --   if(DRE = '1') then
   --   end if;
   --end if;
end process;

BLK_FINISH <= blfin;

BLK_READY <= (BlfinReg and (not EmptyAdr and not blfin)); 

----------------------------------------------------------
-- WRITE_Discard generation
----------------------------------------------------------
WRITEDISCARDBLOCK: if(DISCARD = WriteDiscard or DISCARD=WriteReadDiscard) generate-- or Discard = WriteReadDiscard) generate

--------------------------------------
--Full&empty for discard
--------------------------------------
empty1_gen_proc: process (RD_CLK, RESET, empty_allow)
   begin
      if (RESET = '1') then
         emp2 <= '1';
      elsif (RD_CLK'event and RD_CLK = '1') then
         if (empty_allow = '1') then
            emp2 <= emptyg2;
         end if;
      end if;
   end process;

  -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  ECOMP_GEN2 : for i in 0 to FADDR generate
     ecomp2(i) <= (not (write_dis_gray(i) xor read_gray(i)) and emp) or
                 (not (write_dis_gray(i) xor read_nextgray(i)) and not emp);
  end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   emuxcyo2(0)  <= '1';
   emptyg2      <= emuxcyo2(FADDR+1);
 
   EMUXCY_GEN2 : for i in 0 to FADDR generate
      emuxcyX: MUXCY_L
      port map (
         DI => '0',
         CI => emuxcyo2(i),
         S  => ecomp2(i),
         LO => emuxcyo2(i+1)
      );
   end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   FCOMP_GEN2 : for i in 0 to FADDR generate
      fcomp2(i) <= (not (read_lastgray(i) xor write_dis_gray(i)) and fl) or
                  (not (read_lastgray(i) xor write_dis_nextgray(i)) and not fl);
   end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   fmuxcyo2(0)  <= '1';
   fullg2       <= fmuxcyo2(FADDR+1);

   FMUXCY_GEN2 : for i in 0 to FADDR generate
      fmuxcyX: MUXCY_L
      port map (
         DI => '0',
         CI => fmuxcyo2(i),
         S  => fcomp2(i),
         LO => fmuxcyo2(i+1)
      );
   end generate;



WrDiscardGen_Proc: process(WR_DISCARD,WR_CLK,Reset,EndBlockW)
begin
   if(reset='1') then
      WrDiscardStatus <= '0';
   elsif (WR_CLK'event and WR_CLK='1') then
      if(WR_DISCARD = '1') then
         WrDiscardStatus <= '1';
      elsif(EndBlockW = '1') then
         WrDiscardStatus <= '0';
      end if;
   end if;
end process;

LastAdressReg_proc: process(EndBlockW,WR_CLK,Reset,WrDiscardStatus)
begin
   if(reset = '1') then
      lastwritedblock <= (others => '0');
   elsif(WR_CLK'event and WR_CLK='1') then
      if(EndBlockW = '1' and WrDiscardStatus = '0') then
         lastwritedblock <= write_cnt1;
      end if;
   end if;
end process;

write_dis_next_proc: process(EndBlockW,WR_CLK,Reset,WrDiscardStatus)
begin
   if(Reset='1') then 
      write_dis_nextgray <= write_nextgray;
   elsif(WR_CLK'event and WR_CLK='1') then
      if(EndBlockW='1' and WrDiscardStatus = '0') then
         write_dis_nextgray <= write_nextgray;
      end if;
   end if;
end process;

write_dis_gray_proc: process(EndBlockW,WR_CLK,Reset,WrDiscardStatus)
begin
   if(reset='1') then 
      write_dis_gray <= write_gray;
   elsif (WR_CLK'event and WR_CLK='1') then
      if(EndBlockW='1' and WrDiscardStatus='0') then
         write_dis_gray <=write_gray;
      end if;
   end if;
end process;
 

AWE <= DWE and EndBlockW;
DWE <= (WR and not fl) and not WrDiscardStatus;
ARE <= (blfin and not blFinReg) and DRE;

end generate;

-----------------------------------------------------------------------
--Read Discard generation
-----------------------------------------------------------------------

ReadDiscardBlock: if(DISCARD = ReadDiscard or DISCARD=WriteReadDiscard) generate
---------------------------------
--full&Empty for read discard
---------------------------------
empty_gen_proc3: process (RD_CLK, RESET, empty_allow)
   begin
      if (RESET = '1') then
         emp3 <= '1';
      elsif (RD_CLK'event and RD_CLK = '1') then
         if (empty_allow = '1') then
            emp3 <= emptyg3;
         end if;
      end if;
   end process;

 -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  ECOMP_GEN3 : for i in 0 to FADDR generate
     ecomp3(i) <= (not (write_gray(i) xor read_dis_gray(i)) and emp) or
                 (not (write_gray(i) xor read_dis_nextgray(i)) and not emp);
  end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   emuxcyo3(0)  <= '1';
   emptyg3      <= emuxcyo3(FADDR+1);
 
   EMUXCY_GEN3 : for i in 0 to FADDR generate
      emuxcyX: MUXCY_L
      port map (
         DI => '0',
         CI => emuxcyo3(i),
         S  => ecomp3(i),
         LO => emuxcyo3(i+1)
      );
   end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   FCOMP_GEN3 : for i in 0 to FADDR generate
      fcomp3(i) <= (not (read_dis_lastgray(i) xor write_gray(i)) and fl) or
                  (not (read_dis_lastgray(i) xor write_nextgray(i)) and not fl);
   end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   fmuxcyo3(0)  <= '1';
   fullg3       <= fmuxcyo3(FADDR+1);

   FMUXCY_GEN3 : for i in 0 to FADDR generate
      fmuxcyX: MUXCY_L
      port map (
         DI => '0',
         CI => fmuxcyo3(i),
         S  => fcomp3(i),
         LO => fmuxcyo3(i+1)
      );
   end generate;




RdDiscardStatus_proc: process(Reset,RD_CLK,RD_DISCARD)
begin
   if(Reset = '1') then
      RdDiscardStatus <='0';
   elsif(RD_CLK'event and RD_CLK='1') then
      if(RD_DISCARD = '1') then RdDiscardStatus <= not RdDiscardStatus;
      end if;
   end if;
end process;

RdDiscardStatusReg_proc: process(Reset,RD_CLK,RdDiscardStatus)
begin
   if(Reset='1') then
      RdDiscardStatusReg <= '0';
   elsif(RD_CLK'event and RD_CLK='1') then
      RdDiscardStatusReg <= RdDiscardStatus;
   end if;
end process;

cnt_read_dis_proc: process(reset, RD_CLK)
begin
   if(Reset='1') then 
      read_dis <= (others => '0');
   elsif (RD_CLK'event and RD_CLK='1') then
      read_dis <= EndAdr-1;
   end if;
end process;

cnt_read_dis_last_proc: process(reset,RD_CLK)
begin
   if(Reset='1') then
      read_dis_last <= (others => '0');
   elsif(RD_CLK'event and RD_CLK='1') then
      read_dis_last <= EndAdr-2;
   end if;
end process;

read_dis_nextgray_proc: process(RD_CLK,Reset)
begin
   if(reset='1') then
      read_dis_nextgray <= conv_std_logic_vector(2**(FADDR), FADDR+1);
   elsif(RD_CLK'event and RD_CLK='1') then
      read_dis_nextgray(FADDR) <= EndAdr(FADDR);
      for i in FADDR-1 downto 0 loop
         read_dis_nextgray(i) <= EndAdr(i+1) xor EndAdr(i);
      end loop;
   end if;
end process;

read_dis_gray_proc: process(RD_CLK,Reset)
begin
   if(reset='1') then
      read_dis_gray <= conv_std_logic_vector(2**(FADDR)+1, FADDR+1);
   elsif(RD_CLK'event and RD_CLK='1') then
      read_dis_gray(FADDR) <= read_dis(FADDR);
      for i in FADDR-1 downto 0 loop
         read_dis_gray(i) <= read_dis(i+1) xor read_dis(i);
      end loop;
   end if;
end process;

read_dis_lastgray_proc: process(RD_CLK,Reset)
begin
   if(reset='1') then
      read_dis_lastgray <= conv_std_logic_vector(2**(FADDR)+3, FADDR+1);
   elsif(RD_CLK'event and RD_CLK='1') then
      read_dis_lastgray(FADDR) <= read_dis_last(FADDR);
      for i in FADDR-1 downto 0 loop
         read_dis_lastgray(i) <= read_dis_last(i+1) xor read_dis_last(i);
      end loop;
   end if;
end process;


DWE <=(WR and not fl);
ARE <=((blfin and not blFinReg) and DRE) or (RdDiscardStatus  xor RdDiscardStatusReg);
AWE <= DWE and EndBlockW;
end generate;


ReadWriteDiscardBlock: if(DISCARD=WriteReadDiscard) generate
empty_gen_proc4: process (RD_CLK, RESET, empty_allow)
   begin
      if (RESET = '1') then
         emp4 <= '1';
      elsif (RD_CLK'event and RD_CLK = '1') then
         if (empty_allow = '1') then
            emp4 <= emptyg4;
         end if;
      end if;
   end process;

 -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  ECOMP_GEN4 : for i in 0 to FADDR generate
     ecomp4(i) <= (not (write_dis_gray(i) xor read_dis_gray(i)) and emp) or
                 (not (write_dis_gray(i) xor read_dis_nextgray(i)) and not emp);
  end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   emuxcyo4(0)  <= '1';
   emptyg4      <= emuxcyo4(FADDR+1);
 
   EMUXCY_GEN4 : for i in 0 to FADDR generate
      emuxcyX: MUXCY_L
      port map (
         DI => '0',
         CI => emuxcyo4(i),
         S  => ecomp4(i),
         LO => emuxcyo4(i+1)
      );
   end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   FCOMP_GEN4 : for i in 0 to FADDR generate
      fcomp4(i) <= (not (read_dis_lastgray(i) xor write_dis_gray(i)) and fl) or
                  (not (read_dis_lastgray(i) xor write_dis_nextgray(i)) and not fl);
   end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   fmuxcyo4(0)  <= '1';
   fullg4       <= fmuxcyo4(FADDR+1);

   FMUXCY_GEN4 : for i in 0 to FADDR generate
      fmuxcyX: MUXCY_L
      port map (
         DI => '0',
         CI => fmuxcyo4(i),
         S  => fcomp4(i),
         LO => fmuxcyo4(i+1)
      );
   end generate;


end generate;

FULL <= fl;
EMPTY <= emp;
DO_DV <= Valid; 
Status <= reg_status;
end architecture;
