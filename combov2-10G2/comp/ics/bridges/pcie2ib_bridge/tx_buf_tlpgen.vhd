--
-- tx_buf_tlpgen.vhd : Transaction Layer Packet Generator
-- Copyright (C) 2007 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
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
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--           ENTITY DECLARATION -- Transaction Layer Packet Generator        -- 
-- ----------------------------------------------------------------------------

entity TLP_GEN is
   port(
      -- Common Interface
      CLK               : in std_logic;                           
      RSTN              : in std_logic;                           
      
      -- TLP TX Interface
      TLPTXDATA         : out std_logic_vector(63 downto 0);      
      TLPTXDWE          : out std_logic_vector(1 downto 0);       
      TLPTXREQ          : out std_logic;                          
      TLPTXDISCARD      : out std_logic;                          
      TLPTXACK          : in std_logic;                           
      TLPTXWAIT         : in std_logic;                           
      TLPTXFMTERR       : in std_logic;                           
      
      -- Application Interface
      TXSTART           : in std_logic;
      TXCOMMAND         : in std_logic_vector(6 downto 0);        
      TXSRCDEVID        : in std_logic_vector(15 downto 0);       
      TXDSTDEVID        : in std_logic_vector(15 downto 0);       
      TXTC              : in std_logic_vector(2 downto 0);        
      TXTAG             : in std_logic_vector(7 downto 0);        
      TXRELAXORDERATTR  : in std_logic;                           
      TXNOSNOOPATTR     : in std_logic;                           
      TXADDRESS         : in std_logic_vector(63 downto 0);       
      TXLENGTH          : in std_logic_vector(10 downto 0);        
      TXDWENA1ST        : in std_logic_vector(3 downto 0);        
      TXDWENALAST       : in std_logic_vector(3 downto 0);        
      TXCPLSTATUS       : in std_logic_vector(2 downto 0);        
      TXCPLBCOUNT       : in std_logic_vector(12 downto 0);       
      TXDATADW0         : in std_logic_vector(31 downto 0);       
      TXDATADW1         : in std_logic_vector(31 downto 0);       
      TXREADY           : out std_logic;                          
      TXDONE            : out std_logic;                          
      TXDWRD0           : out std_logic;                          
      TXDWRD1           : out std_logic                           
   ); 
end TLP_GEN;

-- ----------------------------------------------------------------------------
--       ARCHITECTURE DECLARATION  --  Transaction Layer Packet Generator    --
-- ----------------------------------------------------------------------------

architecture tlp_gen_arch of TLP_GEN is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal hdr_dw0       : std_logic_vector(31 downto 0);       
   signal hdr_dw1       : std_logic_vector(31 downto 0);       
   signal hdr_dw2       : std_logic_vector(31 downto 0);       
   signal hdr_dw3       : std_logic_vector(31 downto 0);       
   signal tlp_dw0       : std_logic_vector(31 downto 0);       
   signal tlp_dw1       : std_logic_vector(31 downto 0);       
   signal tlp_dw0_r     : std_logic_vector(31 downto 0) := (others => '0');       
   signal tlp_dw1_r     : std_logic_vector(31 downto 0) := (others => '0');       
   signal tlptxdwe_nxt  : std_logic_vector(1 downto 0);
   signal tlptxdwe_r    : std_logic_vector(1 downto 0);
   signal tlptxreq_nxt  : std_logic;
   signal tlptxreq_r    : std_logic;
   signal tlpwdata      : std_logic;         
   signal tlp4dwh       : std_logic;        
   signal txattr        : std_logic_vector(1 downto 0);    
   signal dwrd0i        : std_logic;        
   signal dwrd1i        : std_logic;       
   signal hdrd_r        : std_logic;      
   signal dwrdcnt_r     : std_logic_vector(9 downto 0);     
   signal dwtxcnt_r     : std_logic_vector(9 downto 0);    
   signal hdr_length    : std_logic_vector(9 downto 0);   
   signal txlength_aux  : std_logic_vector(9 downto 0);   
   signal txcplbcount_aux  : std_logic_vector(11 downto 0);      
   signal tlptxready_r  : std_logic;        
   signal tlptxdone_r   : std_logic;       
   signal datadw0_swap  : std_logic_vector(31 downto 0);      
   signal datadw1_swap  : std_logic_vector(31 downto 0);     
   signal tlptxcmd      : std_logic_vector(6 downto 0);
   type tfsmstate is (TPG_IDLE,TPG_TXH1,TPG_TXH2,TPG_TXDATA); 
   signal tpg_state_nxt : tfsmstate;  
   signal tpg_state_r   : tfsmstate; 
   signal txmsgcode  : std_logic_vector(7 downto 0);
   signal txmsgroute : std_logic_vector(2 downto 0);  
   signal txmsgdw2   : std_logic_vector(31 downto 0);
   signal txmsgdw3   : std_logic_vector(31 downto 0);      

   -- -------------------------------------------------------------------------
   --                           Constant declaration                         --
   -- -------------------------------------------------------------------------

   constant c_txmsgcode  : std_logic_vector(7 downto 0)  := "00000000";
   constant c_txmsgroute : std_logic_vector(2 downto 0)  := "000";  
   constant c_txmsgdw2   : std_logic_vector(31 downto 0) := X"00000000";
   constant c_txmsgdw3   : std_logic_vector(31 downto 0) := X"00000000";   
   constant rstsync      : std_logic  := '0';
   constant NO_TAG       : std_logic_vector(7 downto 0)  := (others => '0');
   constant CNT_ZERO     : std_logic_vector(9 downto 0)  := (others => '0');   

   constant TLPFMT_3DWH_ND : std_logic_vector(1 downto 0) := "00";     
   constant TLPFMT_4DWH_ND : std_logic_vector(1 downto 0) := "01";     
   constant TLPFMT_3DWH_WD : std_logic_vector(1 downto 0) := "10";     
   constant TLPFMT_4DWH_WD : std_logic_vector(1 downto 0) := "11";     
 
   constant TLPTYPE_MEM    : std_logic_vector(4 downto 0) := "00000";
   constant TLPTYPE_MEMLK  : std_logic_vector(4 downto 0) := "00001";
   constant TLPTYPE_IO     : std_logic_vector(4 downto 0) := "00010";
   constant TLPTYPE_CFG0   : std_logic_vector(4 downto 0) := "00100";
   constant TLPTYPE_CFG1   : std_logic_vector(4 downto 0) := "00101";
   constant TLPTYPE_MSG    : std_logic_vector(4 downto 0) := "10000";
   constant TLPTYPE_CPL    : std_logic_vector(4 downto 0) := "01010";
   constant TLPTYPE_CPLLK  : std_logic_vector(4 downto 0) := "01011";

   constant TLPCMD_MRD32   : std_logic_vector(6 downto 0) := TLPFMT_3DWH_ND & TLPTYPE_MEM;
   constant TLPCMD_MRD64   : std_logic_vector(6 downto 0) := TLPFMT_4DWH_ND & TLPTYPE_MEM;
   constant TLPCMD_MRDLK32 : std_logic_vector(6 downto 0) := TLPFMT_3DWH_ND & TLPTYPE_MEMLK;
   constant TLPCMD_MRDLK64 : std_logic_vector(6 downto 0) := TLPFMT_4DWH_ND & TLPTYPE_MEMLK;
   constant TLPCMD_MWR32   : std_logic_vector(6 downto 0) := TLPFMT_3DWH_WD & TLPTYPE_MEM;
   constant TLPCMD_MWR64   : std_logic_vector(6 downto 0) := TLPFMT_4DWH_WD & TLPTYPE_MEM;
   constant TLPCMD_IORD    : std_logic_vector(6 downto 0) := TLPFMT_3DWH_ND & TLPTYPE_IO;
   constant TLPCMD_IOWR    : std_logic_vector(6 downto 0) := TLPFMT_3DWH_WD & TLPTYPE_IO;
   constant TLPCMD_CFGRD0  : std_logic_vector(6 downto 0) := TLPFMT_3DWH_ND & TLPTYPE_CFG0;
   constant TLPCMD_CFGWR0  : std_logic_vector(6 downto 0) := TLPFMT_3DWH_WD & TLPTYPE_CFG0;
   constant TLPCMD_CFGRD1  : std_logic_vector(6 downto 0) := TLPFMT_3DWH_ND & TLPTYPE_CFG1;
   constant TLPCMD_CFGWR1  : std_logic_vector(6 downto 0) := TLPFMT_3DWH_WD & TLPTYPE_CFG1;
   constant TLPCMD_MSG     : std_logic_vector(6 downto 0) := TLPFMT_4DWH_ND & TLPTYPE_MSG;
   constant TLPCMD_MSGD    : std_logic_vector(6 downto 0) := TLPFMT_4DWH_WD & TLPTYPE_MSG;
   constant TLPCMD_CPL     : std_logic_vector(6 downto 0) := TLPFMT_3DWH_ND & TLPTYPE_CPL;
   constant TLPCMD_CPLD    : std_logic_vector(6 downto 0) := TLPFMT_3DWH_WD & TLPTYPE_CPL;
   constant TLPCMD_CPLLK   : std_logic_vector(6 downto 0) := TLPFMT_3DWH_ND & TLPTYPE_CPLLK;
   constant TLPCMD_CPLDLK  : std_logic_vector(6 downto 0) := TLPFMT_3DWH_WD & TLPTYPE_CPLLK;   
   
begin
   
   -- -------------------------------------------------------------------------
   --                            Architecture Body                           --
   -- -------------------------------------------------------------------------

   txmsgcode    <= c_txmsgcode; 
   txmsgroute   <= c_txmsgroute;
   txmsgdw2     <= c_txmsgdw2;  
   txmsgdw3     <= c_txmsgdw3;   
   tlptxdata    <= tlp_dw0_r & tlp_dw1_r;
   tlptxdwe     <= tlptxdwe_r;
   tlptxreq     <= tlptxreq_r;
   txdone       <= tlptxdone_r;
   txready      <= tlptxready_r;
   tlptxdiscard <= '0';
   txdwrd0      <= dwrd0i;
   txdwrd1      <= dwrd1i;   
   datadw0_swap <= txdatadw0(7 downto 0) & txdatadw0(15 downto 8) & txdatadw0(23 downto 16) & txdatadw0(31 downto 24) ;
   datadw1_swap <= txdatadw1(7 downto 0) & txdatadw1(15 downto 8) & txdatadw1(23 downto 16) & txdatadw1(31 downto 24) ;
   tlpwdata <= txcommand(6);
   tlp4dwh  <= txcommand(5);
   txattr <= txrelaxorderattr & txnosnoopattr;
   
   -- TLP lenght --------------------------------------------------------------
   txlengthp: process(txlength)
   begin
      if (txlength(10) = '1') then
         txlength_aux <= "0000000000";
      else
         txlength_aux <= txlength(9 downto 0);
      end if;
   end process;   

   pTLPLEN: process(txcommand,txlength_aux)
   begin
      case txcommand is
         when TLPCMD_CPL | TLPCMD_CPLLK | TLPCMD_MSG =>     -- Completions & Messages without data
               hdr_length <= (others=>'0');

         when TLPCMD_IORD | TLPCMD_IOWR |
              TLPCMD_CFGRD0 | TLPCMD_CFGWR0 |
              TLPCMD_CFGRD1 | TLPCMD_CFGWR1  =>             -- I/O and Configuration commands
               hdr_length <= (0=>'1',others=>'0');

         when TLPCMD_MRD32 | TLPCMD_MRD64 | TLPCMD_MWR32 | TLPCMD_MWR64|
              TLPCMD_MRDLK32 | TLPCMD_MRDLK64 | TLPCMD_CPLD | TLPCMD_CPLDLK=>  -- memory read commands
               hdr_length <= txlength_aux;
         when others =>                                     -- message commands
               hdr_length <= txlength_aux;
       end case;
   end process;
   
   -- add routing info to message commands ------------------------------------
   process(txcommand,txmsgroute)
   begin
      if (txcommand(6 downto 3) = TLPCMD_MSG(6 downto 3)) or (txcommand(6 downto 3) = TLPCMD_MSGD(6 downto 3)) then
         tlptxcmd <= txcommand(6 downto 3) & txmsgroute;
      else
         tlptxcmd <= txcommand;
      end if;
   end process;
   
   -- TLP Header DW0 ----------------------------------------------------------
   hdr_dw0 <= '0' & tlptxcmd & '0' & txtc & "0000" & '0' & '0' & txattr & "00" & hdr_length;
   
   -- TLP Header DW1 ----------------------------------------------------------
   txcplbcountp: process(txcplbcount)
   begin
      if (txcplbcount(12) = '1') then
         txcplbcount_aux <= "000000000000";
      else
         txcplbcount_aux <= txcplbcount(11 downto 0);
      end if;
   end process;   
   
   pTLPHDW1: process(txcommand,txsrcdevid,txcplstatus,txcplbcount_aux,txtag,txdwena1st,txdwenalast,txmsgcode)
   begin
      case txcommand is
         when TLPCMD_CPL | TLPCMD_CPLD |                    -- Completions
              TLPCMD_CPLLK | TLPCMD_CPLDLK   =>
               hdr_dw1 <= txsrcdevid & txcplstatus & '0' & txcplbcount_aux;

         when TLPCMD_IORD | TLPCMD_IOWR |
              TLPCMD_CFGRD0 | TLPCMD_CFGWR0 |
              TLPCMD_CFGRD1 | TLPCMD_CFGWR1  =>             -- I/O and Configuration commands
               hdr_dw1 <= txsrcdevid & txtag & "0000" & txdwena1st;

         when TLPCMD_MRD32 | TLPCMD_MRD64 |
              TLPCMD_MRDLK32 | TLPCMD_MRDLK64 =>            -- memory read commands
               hdr_dw1 <= txsrcdevid & txtag & txdwenalast & txdwena1st;
         when TLPCMD_MWR32 | TLPCMD_MWR64    =>             -- memory write commands
               hdr_dw1 <= txsrcdevid & txtag & txdwenalast & txdwena1st;
         when others =>                                     -- message commands
               hdr_dw1 <= txsrcdevid & NO_TAG & txmsgcode;
       end case;
   end process;
   
   -- TLP Header DW2 ----------------------------------------------------------
   pTLPHDW2: process(txcommand,txdstdevid,txtag,txaddress,txmsgdw2)
   begin
      case txcommand is
         when TLPCMD_CPL | TLPCMD_CPLD |                    -- Completions
              TLPCMD_CPLLK | TLPCMD_CPLDLK   =>
               hdr_dw2 <= txdstdevid & txtag & '0' & txaddress(6 downto 0);
         when TLPCMD_CFGRD0 | TLPCMD_CFGWR0 |
              TLPCMD_CFGRD1 | TLPCMD_CFGWR1  =>
              hdr_dw2 <= txdstdevid &  "0000" & txaddress(11 downto 2) & "00";

         when TLPCMD_IORD | TLPCMD_IOWR |
              TLPCMD_MRDLK32 | TLPCMD_MRD32 | TLPCMD_MWR32  =>    -- 32-bit txaddress commands
               hdr_dw2 <= txaddress(31 downto 2) & "00";

         when  TLPCMD_MRD64 | TLPCMD_MRDLK64 | TLPCMD_MWR64 =>    -- 64-bit txaddress memory commands
               hdr_dw2 <= txaddress(63 downto 32);

         when others =>                                     -- message commands
               hdr_dw2 <= txmsgdw2;
       end case;
   end process;
   
   -- TLP Header DW3 ----------------------------------------------------------
   pTLPHDW3: process(txcommand,txaddress,txmsgdw3,datadw0_swap)
   begin
      case txcommand is
         when TLPCMD_IORD | TLPCMD_CPL |                          -- TLP 3DW header, no data
              TLPCMD_CFGRD0 | TLPCMD_CPLLK |
              TLPCMD_CFGRD1 | TLPCMD_MRDLK32 | TLPCMD_MRD32=>
               hdr_dw3 <= (others => '0');

         when  TLPCMD_CPLD | TLPCMD_CPLDLK | TLPCMD_IOWR |
               TLPCMD_CFGWR0 | TLPCMD_CFGWR1 | TLPCMD_MWR32  =>    -- TLP 3DW header, with data
               hdr_dw3 <= datadw0_swap;

         when  TLPCMD_MRD64 | TLPCMD_MRDLK64 | TLPCMD_MWR64 =>    -- 64-bit txaddress memory commands
               hdr_dw3 <= txaddress(31 downto 2) & "00";

         when others =>                                     -- message commands
               hdr_dw3 <= txmsgdw3;
       end case;
   end process;
   
   -- data read counter -------------------------------------------------------
   pDWRDCNTREG: process(clk,rstn)
   begin
      if rstn = '0' then
         dwrdcnt_r <= (others => '0');
      elsif clk'event and clk = '1' then
         if rstsync = '1' then
            dwrdcnt_r <= (others => '0');
         elsif txstart = '1' then
            if tlpwdata = '1' then
               dwrdcnt_r <= hdr_length;
            else
               dwrdcnt_r <= (others => '0');
            end if;
         elsif dwrd0i = '1' and  dwrd1i = '1' then
            dwrdcnt_r <= dwrdcnt_r - 2;            -- read 64-bit data
         elsif (dwrd0i = '1' and  dwrd1i = '0')or(dwrd0i = '0' and  dwrd1i = '1') then
            dwrdcnt_r <= dwrdcnt_r - 1;            -- read 32-bit data
         end if;
      end if;
   end process;
   
   -- data transmit counter ---------------------------------------------------
   pDWTXCNTREG: process(clk,rstn)
   begin
      if rstn = '0' then
         dwtxcnt_r <= (others => '0');
      elsif clk'event and clk = '1' then
         if rstsync = '1' then
            dwtxcnt_r <= (others => '0');
         elsif txstart = '1' and tpg_state_r = TPG_IDLE then
            if tlpwdata = '1' then
               dwtxcnt_r <= hdr_length;
            else
               dwtxcnt_r <= (others => '0');
            end if;
         elsif (tpg_state_nxt = TPG_TXDATA and (dwtxcnt_r > 1) and tlptxwait = '0') then
            dwtxcnt_r <= dwtxcnt_r - 2;
         elsif ((tpg_state_nxt = TPG_TXDATA or (tpg_state_nxt = TPG_TXH2 and tlp4dwh = '0' and tlpwdata = '1')) and tlptxwait = '0') then
            dwtxcnt_r <= dwtxcnt_r - 1;
         end if;
      end if;
   end process;
   
   -- Data multiplexor --------------------------------------------------------
   process(tpg_state_r,tlp4dwh,hdr_dw0,hdr_dw1,hdr_dw2,hdr_dw3,datadw0_swap,datadw1_swap)
   begin
      case tpg_state_r is
         when TPG_IDLE     =>
            tlp_dw0 <= hdr_dw0;
            tlp_dw1 <= hdr_dw1;
         when TPG_TXH1     =>
            tlp_dw0 <= hdr_dw2;
            tlp_dw1 <= hdr_dw3;
         when others     =>
            if tlp4dwh = '1' then   -- 4DW header, normal order
               tlp_dw0 <= datadw0_swap;
               tlp_dw1 <= datadw1_swap;
            else                    -- 3DW header, DW swapped
               tlp_dw0 <= datadw1_swap;
               tlp_dw1 <= datadw0_swap;
            end if;
      end case;
   end process;
   
   -- TLP Data output register ------------------------------------------------
   pTLPDOREG: process(clk)
   begin
      if clk'event and clk = '1' then
         if txstart = '1' or (tlptxack = '1' and tlptxwait = '0') then
            tlp_dw0_r <= tlp_dw0;
            tlp_dw1_r <= tlp_dw1;
         end if;
      end if;
   end process;
 
   -- Data buffer read --------------------------------------------------------
   pHDRDREG: process(clk,rstn)
   begin
      if rstn = '0' then
         hdrd_r <= '0';
      elsif clk'event and clk = '1' then
         if rstsync = '1' then
            hdrd_r <= '0';
         elsif txstart = '1' and tpg_state_r = TPG_IDLE  and tlpwdata = '1' and tlp4dwh = '0' then
            hdrd_r <= '1';
         else
            hdrd_r <= '0';
         end if;
      end if;
   end process;
   
   -- dwrd0 -------------------------------------------------------------------
   pDWRD0:process(tpg_state_r,tpg_state_nxt,hdrd_r,dwrdcnt_r,tlp4dwh,tlptxwait)
   begin
      if hdrd_r = '1' or
         (tpg_state_r = TPG_TXH1 and tpg_state_nxt = TPG_TXH2 and tlptxwait = '0' and
         ((dwrdcnt_r > 1 and tlp4dwh = '0') or (dwrdcnt_r /= 0 and tlp4dwh = '1'))) or
         ((tpg_state_r = TPG_TXH2 or tpg_state_r = TPG_TXDATA) and tlptxwait = '0' and
         ((dwrdcnt_r > 1 and tlp4dwh = '0') or (dwrdcnt_r /= 0 and tlp4dwh = '1'))) then
         dwrd0i <= '1';
      else
         dwrd0i <= '0';
      end if;
   end process;
   
   -- dwrd1 -------------------------------------------------------------------   
   pDWRD1:process(tpg_state_r,tpg_state_nxt,dwrdcnt_r,tlp4dwh,tlptxwait)
   begin
      if (tpg_state_r = TPG_TXH1 and tpg_state_nxt = TPG_TXH2 and
         ((dwrdcnt_r > 1 and tlp4dwh = '1') or (dwrdcnt_r /= CNT_ZERO and tlp4dwh = '0'))) or
         ((tpg_state_r = TPG_TXH2 or tpg_state_r = TPG_TXDATA) and tlptxwait = '0' and
         ((dwrdcnt_r > 1 and tlp4dwh = '1') or (dwrdcnt_r /= 0 and tlp4dwh = '0'))) then
         dwrd1i <= '1';
      else
         dwrd1i <= '0';
      end if;
   end process;
   
   -- TLP Transfer request ----------------------------------------------------
   process(tpg_state_r,txstart,tlpwdata,tlp4dwh,dwtxcnt_r,dwrdcnt_r)
   begin
      case tpg_state_r is
         when TPG_IDLE     =>
            if txstart = '1' then
               tlptxreq_nxt <= '1';
            else
               tlptxreq_nxt <= '0';
            end if;
         when TPG_TXH1     =>
            if tlpwdata = '1' and (dwtxcnt_r /= 1 or tlp4dwh = '1') then
               tlptxreq_nxt <= '1';
            else
               tlptxreq_nxt <= '0';
            end if;
         when others     =>
            if dwrdcnt_r > 0 then
               tlptxreq_nxt <= '1';
            else
               tlptxreq_nxt <= '0';
            end if;
      end case;
   end process;
 
   pTLPTXREQREG: process(clk,rstn)
   begin
      if rstn = '0' then
         tlptxreq_r <= '0';
      elsif clk'event and clk = '1' then
         if rstsync = '1' then
            tlptxreq_r <= '0';
         elsif txstart = '1' or (tlptxack = '1' and tlptxwait = '0') then
            tlptxreq_r <= tlptxreq_nxt;
         end if;
      end if;
   end process;

   -- TLP Data output register next value -------------------------------------
   process(tpg_state_r,txstart,tlpwdata,tlp4dwh,tlptxdwe_r,dwtxcnt_r)
   begin
      case tpg_state_r is
         when TPG_IDLE     =>
            if txstart = '1' then
               tlptxdwe_nxt <= "11";
            else
               tlptxdwe_nxt <= "00";
            end if;
         when TPG_TXH1     =>
            if tlpwdata = '1' or tlp4dwh = '1' then
               tlptxdwe_nxt <= "11";
            else
               tlptxdwe_nxt <= "10";
            end if;
         when others     =>
            if tlptxdwe_r = "10" or tlpwdata = '0' or dwtxcnt_r = CNT_ZERO then
               tlptxdwe_nxt <= "00";
            elsif dwtxcnt_r = (CNT_ZERO + 1) then
               tlptxdwe_nxt <= "10";
            else
               tlptxdwe_nxt <= "11";
            end if;
      end case;
   end process;
 
   -- TLP DW enable output ----------------------------------------------------
   pTLPDWEREG: process(clk,rstn)
   begin
      if rstn = '0' then
         tlptxdwe_r <= (others => '0');
      elsif clk'event and clk = '1' then
         if rstsync = '1' then
            tlptxdwe_r <= (others => '0');
         elsif (tpg_state_r = TPG_IDLE and txstart = '1') or (tlptxack = '1' and tlptxwait = '0') then
            tlptxdwe_r <= tlptxdwe_nxt;
         end if;
      end if;
   end process;

   -- Tx ready register -------------------------------------------------------
   pTLPTXREADYREG: process(clk,rstn)
   begin
      if rstn = '0' then
         tlptxready_r <= '1';
      elsif clk'event and clk = '1' then
         if rstsync = '1' then
            tlptxready_r <= '0';
         elsif tpg_state_nxt /= TPG_IDLE then
            tlptxready_r <= '0';
         else
            tlptxready_r <= '1';
         end if;
      end if;
   end process;
   
   -- Tx Done register --------------------------------------------------------
   pTLPTXDONEREG: process(clk,rstn)
   begin
      if rstn = '0' then
         tlptxdone_r <= '0';
      elsif clk'event and clk = '1' then
         if rstsync = '1' then
            tlptxdone_r <= '1';
         elsif tpg_state_r /= TPG_IDLE and tpg_state_nxt = TPG_IDLE then
            tlptxdone_r <= '1';
         else
            tlptxdone_r <= '0';
         end if;
      end if;
   end process;
 
   -- Control State Machine ---------------------------------------------------
   pFSMREG: process(clk,rstn)
   begin
      if rstn = '0' then
         tpg_state_r <= TPG_IDLE;
      elsif clk'event and clk = '1' then
         if rstsync = '1' then
            tpg_state_r <= TPG_IDLE;
         else
            tpg_state_r <= tpg_state_nxt;
         end if;
      end if;
   end process;
   --
   pFSMNXT:process(tpg_state_r,txstart,tlptxack,tlpwdata,dwtxcnt_r,tlptxwait)
   begin
      case tpg_state_r is
         when TPG_IDLE     =>
            if txstart = '1' then
               tpg_state_nxt <= TPG_TXH1;
            else
               tpg_state_nxt <= TPG_IDLE;
            end if;
         when TPG_TXH1     =>
            if tlptxack = '1' and tlptxwait = '0'then
               tpg_state_nxt <= TPG_TXH2;
            else
               tpg_state_nxt <= TPG_TXH1;
            end if;
         when TPG_TXH2     =>
            if (tlpwdata = '0' or dwtxcnt_r = CNT_ZERO) and tlptxwait = '0' then
               tpg_state_nxt <= TPG_IDLE;
            elsif tlptxwait = '0' then
               tpg_state_nxt <= TPG_TXDATA;
            else
               tpg_state_nxt <= TPG_TXH2;
            end if;
         when TPG_TXDATA   =>
            if dwtxcnt_r = CNT_ZERO and tlptxwait = '0' then
               tpg_state_nxt <= TPG_IDLE;
            else
               tpg_state_nxt <= TPG_TXDATA;
            end if;
      end case;
   end process;
end tlp_gen_arch;



