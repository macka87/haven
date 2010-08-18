--
-- rx_buf_tlpdec.vhd : Transaction Layer Packet Decoder
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
--           ENTITY DECLARATION -- Transaction Layer Packet Decoder          -- 
-- ----------------------------------------------------------------------------
 
entity TLP_DEC is
port(
   -- Common Interface
   clk               : in std_logic;                           
   rstn              : in std_logic;                           
   
   -- TLP RX interface
   TLPRXREQ          : in std_logic;                           
   TLPRXDATA         : in std_logic_vector(63 downto 0);       
   TLPRXDWE          : in std_logic_vector(1 downto 0);        
   TLPRXCORE         : in std_logic; -- '1' = Xilinx PCIe core block plus, '0' = CAST core
   TLPRXACK          : out std_logic;                          
   TLPRXWAIT         : out std_logic;                          
   TLPRXREADY        : out std_logic;                          
   TLPRXIDLE         : in  std_logic;
   TLPRXREADBACK     : in  std_logic;
   TLPRXBARBASE      : in  std_logic_vector(31 downto 0);
   TLPRXBARMASK      : in  std_logic_vector(31 downto 0);   
   TLPRXFULL         : out std_logic; 
   
   -- Application Interface 
   RXREADY           : in std_logic;                           
   RXDONE            : in std_logic;
   RXVALID           : out std_logic;
   RXREADBACK        : out std_logic;
   RXFULL            : in std_logic;
   RXBARBASE         : out std_logic_vector(31 downto 0);
   RXBARMASK         : out std_logic_vector(31 downto 0);   
   RXCOMMAND         : out std_logic_vector(6 downto 0);
   RXIDLE            : out std_logic;                          
   RXSTART           : out std_logic;                          
   RXLAST            : out std_logic;                          
   RXPTYPEREQ        : out std_logic;                          
   RXPTYPECPL        : out std_logic;                          
   RXSRCDEVID        : out std_logic_vector(15 downto 0);      
   RXTC              : out std_logic_vector(2 downto 0);       
   RXTAG             : out std_logic_vector(7 downto 0);       
   RXATTR            : out std_logic_vector(1 downto 0);       
   RXADDRESS         : out std_logic_vector(63 downto 0);      
   RXLENGTH          : out std_logic_vector(10 downto 0);       
   RXDWENA1ST        : out std_logic_vector(3 downto 0);       
   RXDWENALAST       : out std_logic_vector(3 downto 0);       
   RXCPLSTATUS       : out std_logic_vector(2 downto 0);       
   RXCPLBCOUNT       : out std_logic_vector(12 downto 0);      
   RXDWWR0           : out std_logic;                          
   RXDWWR1           : out std_logic;                          
   RXDATADW0         : out std_logic_vector(31 downto 0);      
   RXDATADW1         : out std_logic_vector(31 downto 0)
   );
end TLP_DEC;

-- ----------------------------------------------------------------------------
--       ARCHITECTURE DECLARATION  --  Transaction Layer Packet Decoder      --
-- ----------------------------------------------------------------------------
 
architecture tlp_dec_arch of TLP_DEC is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- ------------------------------------------------------------------------- 

   signal hdr_dw0_r     : std_logic_vector(31 downto 0);
   signal hdr_dw1_r     : std_logic_vector(31 downto 0);
   signal hdr_dw2_r     : std_logic_vector(31 downto 0);
   signal hdr_dw3_r     : std_logic_vector(31 downto 0);
   signal datadw0_r     : std_logic_vector(31 downto 0);
   signal datadw1_r     : std_logic_vector(31 downto 0);
   signal dbuf_r        : std_logic_vector(31 downto 0);
   signal dbufvalid_r   : std_logic;                        
   signal dwwr0_r       : std_logic;                        
   signal dwwr1_r       : std_logic;                        
   signal rxlast_r      : std_logic_vector(1 downto 0);     
   signal tlprxack_r    : std_logic;         
   signal tlprxwaiti    : std_logic;         
   signal rxstart_r     : std_logic;         
   signal tlpwdata      : std_logic;         
   signal tlp4dwh       : std_logic;         
   signal tlpcommandi   : std_logic_vector(6 downto 0);
   signal ptypereq32_nxt: std_logic;                        
   signal ptypereq64_nxt: std_logic;                        
   signal ptypecpl_nxt  : std_logic;                        
   signal ptypemsg_nxt  : std_logic;                        
   signal ptypereq32_r  : std_logic;                        
   signal ptypereq64_r  : std_logic;                        
   signal ptypecpl_r    : std_logic;                        
   signal ptypemsg_r    : std_logic;                        
   signal rxtag_r       : std_logic_vector(7 downto 0);                         
   signal rxcount_r     : std_logic_vector(9 downto 0);
   type tTLPDECFSM_STATE is (TPD_IDLE,TPD_RXH1,TPD_RXH2,TPD_RXACK,TPD_RXDATA, 
                             TPD_RXH2_RXACK, TPD_RXACK_RXDATA, TPD_RXDATA_AUX, TPD_DONE);
   signal tpd_state_r   : tTLPDECFSM_STATE;              
   signal hdr_dw0       : std_logic_vector(31 downto 0); 
   signal hdr_dw1       : std_logic_vector(31 downto 0); 
   signal hdr_dw2       : std_logic_vector(31 downto 0); 
   signal hdr_dw3       : std_logic_vector(31 downto 0);
   signal rxmsgcode     : std_logic_vector(7 downto 0);                  
   signal rxmsgdw2      : std_logic_vector(31 downto 0);
   signal rxmsgdw3      : std_logic_vector(31 downto 0);
   signal rxpoisoned    : std_logic;          
   signal rxdstdevid    : std_logic_vector(15 downto 0);        
   signal rxptypemsg    : std_logic;
   signal data_in_tmp_regs : std_logic;

   -- -------------------------------------------------------------------------
   --                           Constant declaration                         --
   -- -------------------------------------------------------------------------
 
   constant NO_TAG      : std_logic_vector(7 downto 0) := (others => '0');
   constant CNT_ZERO    : std_logic_vector(9 downto 0) := (others => '0');
   constant ZERO_V64    : std_logic_vector(63 downto 0) := (others => '0');
   constant rstsync     : std_logic  := '0';    

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
   
   -- DECODED SIGNAL assignment -----------------------------------------------
   RXREADBACK <= TLPRXREADBACK;
   RXBARBASE  <= TLPRXBARBASE;
   RXBARMASK  <= TLPRXBARMASK;   
   TLPRXFULL  <= RXFULL;
   
   hdr_dw0 <= hdr_dw0_r;
   hdr_dw1 <= hdr_dw1_r;
   hdr_dw2 <= hdr_dw2_r;
   hdr_dw3 <= hdr_dw3_r;   
   rxcommand   <= hdr_dw0_r(30 downto 24);
   tlpcommandi <= hdr_dw0_r(30 downto 24);
   rxsrcdevid  <= hdr_dw1_r(31 downto 16);
   rxdstdevid  <= hdr_dw2_r(31 downto 16);
   rxtc        <= hdr_dw0_r(22 downto 20);
   rxpoisoned  <= hdr_dw0_r(14);
   rxattr      <= hdr_dw0_r(13 downto 12);
   rxdwena1st  <= hdr_dw1_r(3 downto 0);
   rxdwenalast <= hdr_dw1_r(7 downto 4);
   rxmsgcode   <= hdr_dw1_r(7 downto 0);
   rxcplstatus <= hdr_dw1_r(15 downto 13);
   rxmsgdw2    <= hdr_dw2_r;
   rxmsgdw3    <= hdr_dw3_r;
   rxdatadw0   <= datadw0_r(7 downto 0) & datadw0_r(15 downto 8) & datadw0_r(23 downto 16) & datadw0_r(31 downto 24) ;
   rxdatadw1   <= datadw1_r(7 downto 0) & datadw1_r(15 downto 8) & datadw1_r(23 downto 16) & datadw1_r(31 downto 24) ;
   rxdwwr0     <= dwwr0_r and RXREADY;
   rxdwwr1     <= dwwr1_r and RXREADY;
   rxidle      <= '1' when tpd_state_r = TPD_IDLE else
                  '0';
   tlprxready  <= '1' when tpd_state_r = TPD_IDLE else
                  '0';
   rxstart     <= rxstart_r;
   rxlast      <= rxlast_r(1);
   tlpwdata    <= hdr_dw0_r(30);
   tlp4dwh     <= hdr_dw0_r(29); 
   rxtag       <= rxtag_r;   

   -- RXLENGTH logic ----------------------------------------------------------
   rxlengthp: process(hdr_dw0_r(9 downto 0))
   begin
      if (hdr_dw0_r(9 downto 0) = 0) then
         rxlength <= "10000000000";
      else
         rxlength <= '0'&hdr_dw0_r(9 downto 0);
      end if;
   end process;   

   -- RXCPLBCOUNT logic -------------------------------------------------------
   rxcplbcountp: process(hdr_dw1_r(11 downto 0))
   begin
      if (hdr_dw1_r(11 downto 0) = 0) then
         rxcplbcount <= "1000000000000";
      else
         rxcplbcount <= '0'&hdr_dw1_r(11 downto 0);
      end if;
   end process;      

   -- RXADDRESS logic ---------------------------------------------------------
   pADDRASGN: process(ptypecpl_r,ptypereq32_r,ptypereq64_r,hdr_dw2_r,hdr_dw3_r)
   begin
      if (ptypecpl_r = '1') then                               -- Completions
         rxaddress <= ZERO_V64(63 downto 7) & hdr_dw2_r(6 downto 0);
      elsif (ptypereq32_r = '1') then                          -- 32-bit address commands
         rxaddress <= ZERO_V64(63 downto 32) & hdr_dw2_r(31 downto 2) & "00";
      elsif (ptypereq64_r = '1') then                          -- 64-bit address memory commands
         rxaddress <= hdr_dw2_r & hdr_dw3_r(31 downto 2) & "00";
      else                                                     -- message commands
         rxaddress <= ZERO_V64;
      end if;
   end process;

   -- TLP COMMAND decoder -----------------------------------------------------
   pTYPEDEC: process(tlpcommandi)
   begin
      case tlpcommandi is
         when TLPCMD_CPL | TLPCMD_CPLD |                    -- Completions
              TLPCMD_CPLLK | TLPCMD_CPLDLK   =>
            ptypereq32_nxt <= '0';
            ptypereq64_nxt <= '0';
            ptypecpl_nxt <= '1';
            ptypemsg_nxt <= '0';
         when TLPCMD_IORD | TLPCMD_IOWR |                   -- 32-bit address requests
              TLPCMD_CFGRD0 | TLPCMD_CFGWR0 |
              TLPCMD_CFGRD1 | TLPCMD_CFGWR1 |
              TLPCMD_MRDLK32 | TLPCMD_MRD32 | TLPCMD_MWR32 =>
            ptypereq32_nxt <= '1';
            ptypereq64_nxt <= '0';
            ptypecpl_nxt <= '0';
            ptypemsg_nxt <= '0';
         when TLPCMD_MRD64 | TLPCMD_MRDLK64 | TLPCMD_MWR64 => -- 64-bit address requests
            ptypereq32_nxt <= '0';
            ptypereq64_nxt <= '1';
            ptypecpl_nxt <= '0';
            ptypemsg_nxt <= '0';
         when others =>                                     -- message commands
            ptypereq32_nxt <= '0';
            ptypereq64_nxt <= '0';
            ptypecpl_nxt <= '0';
            ptypemsg_nxt <= '1';
      end case;
   end process;
   
   pTYPEDEC_R: process(clk)
   begin
      if clk'event and clk = '1' then
         if rstsync = '1' then
            ptypereq32_r <= '0';
            ptypereq64_r <= '0';
            ptypecpl_r <= '0';
            ptypemsg_r <= '0';
         else
            ptypereq32_r <= ptypereq32_nxt;
            ptypereq64_r <= ptypereq64_nxt;
            ptypecpl_r <= ptypecpl_nxt;
            ptypemsg_r <= ptypemsg_nxt;
         end if;
      end if;
   end process;

   rxptypecpl <= ptypecpl_r;
   rxptypereq <= ptypereq32_r or ptypereq64_r;
   rxptypemsg <= ptypemsg_r;

   -- TLPRXWAIT and TLPRXACK logic --------------------------------------------
   pRXWAIT:process(tpd_state_r,RXREADY,tlprxack_r)
   begin
      if tpd_state_r = TPD_RXDATA and RXREADY = '0' and tlprxack_r = '1' then
         tlprxwaiti <= '1';
      else
         tlprxwaiti <= '0';
      end if;
   end process;

   tlprxack    <= tlprxack_r;
   tlprxwait   <= tlprxwaiti;      

   data_in_tmp_regsp: process(rstn, CLK, tpd_state_r)
   begin
     if (rstn = '0' or tpd_state_r = TPD_IDLE) then
        data_in_tmp_regs  <= '0';
     elsif (CLK'event AND CLK = '1') then
        if (tlprxreq = '0' and tlprxack_r = '1' and tlprxwaiti = '0') then
           data_in_tmp_regs  <= '1';
        end if;
     end if;
   end process;      

   -- CONTROL STATE MACHINE ---------------------------------------------------
   pFSMREG: process(clk,rstn)
   begin
      if rstn = '0' then
         tpd_state_r <= TPD_IDLE;
         
         tlprxack_r  <= '0';
         rxvalid     <= '0';
         
         rxstart_r   <= '0';
         rxlast_r    <= "00";
         rxcount_r   <= (others => '0');
         dwwr0_r     <= '0';
         dwwr1_r     <= '0';
         dbufvalid_r <= '0';
         rxtag_r     <= (others => '0');
      elsif clk'event and clk = '1' then
         if rstsync = '1' then
            tpd_state_r <= TPD_IDLE;
            tlprxack_r  <= '0';
            rxvalid     <= '0';
            rxstart_r   <= '0';
            rxlast_r    <= "00";
            rxcount_r   <= (others => '0');
            dwwr0_r     <= '0';
            dwwr1_r     <= '0';
            dbufvalid_r <= '0';
            dbuf_r      <= (others => '0');
         else
         
            -- STATE DECODER --------------------------------------------------
            case tpd_state_r is
            
               -- Receiver IDLE - waiting for TLP request ---------------------
               when TPD_IDLE     =>
                  rxstart_r   <= '0';
                  rxvalid     <= '0';
                  tlprxack_r  <= '0';
                  rxlast_r    <= "00";
                  rxcount_r   <= (others => '0');
                  -- if TLP transfer requested then proceed to TPD_RXH1 state
                  if tlprxreq = '1' then
                     tlprxack_r <= '1';
                     hdr_dw0_r <= tlprxdata(63 downto 32);
                     hdr_dw1_r <= tlprxdata(31 downto 0);
                     tpd_state_r <= TPD_RXH1;
                  end if;
   
               -- Receive Header DW0 & DW1 ------------------------------------
               when TPD_RXH1     =>

                  if (tlprxcore = '1') then
                     tlprxack_r <= tlprxreq;                                        --#
                  end if;
               
                  -- if TLP with data then init data counter
                  if tlpwdata = '1' then
                     rxcount_r <= hdr_dw0_r(9 downto 0);
                  end if;
                  -- if REQ, next state is TPD_RXH2                              --#
                  if (tlprxreq = '1' or tlprxcore = '0') then                    --#
                     tpd_state_r <= TPD_RXH2;                                    --#
                  else                                                           --#
                     tpd_state_r <= TPD_RXH1;                                    --#
                  end if;
                                                                                   
               -- Receive Header DW2 & DW3 (Data DW0) -------------------------
               when TPD_RXH2     =>

                  tlprxack_r <= tlprxreq;                                        --#
               
                  -- request processing by application
                  rxstart_r <=  '1';
                  -- store header DW2 and DW3
                  hdr_dw2_r <= tlprxdata(63 downto 32);
                  hdr_dw3_r <= tlprxdata(31 downto 0);
                  -- store RX tag
                  if (ptypecpl_nxt = '1') then
                     rxtag_r <= tlprxdata(47 downto 40);
                  else
                     rxtag_r <= hdr_dw1_r(15 downto 8);
                  end if;
                  -- End of TLP data receiving                                   --#
                  --if tlprxreq = '0' then                                       --#
                  --   tlprxack_r <= '0';                                        --#
                  --end if;                                                      --#
                  -- last transfer if no data payload
                  if tlpwdata = '0' then
                     rxlast_r    <= "11";
                  end if;
                  -- Store first data (3DW Header + Data)
                  if tlpwdata = '1' and tlp4dwh = '0' then
                     dbuf_r      <= tlprxdata(31 downto 0);
                     dbufvalid_r <= tlprxdwe(0);
                  end if;
                  -- State transition
                  if (tlprxreq = '1' or (tlpwdata = '1' and tlp4dwh = '0' and rxcount_r = 1) or tlprxcore = '0') then   --#
                     tpd_state_r <= TPD_RXACK;                                   --#
                  else                                                           --#
                     tpd_state_r <= TPD_RXH2_RXACK;                              --#                  
                  end if;

               -- between RXH2 and RXACK --------------------------------------
               when TPD_RXH2_RXACK    =>                                         --#
                                                                                 --#
                  tlprxack_r <= tlprxreq;                                        --#
                                                                                 --#
                  -- Transaction accepted by application, clear rxstart request  --#
                  if RXREADY ='1' then                                           --#
                     rxstart_r <=  '0';                                          --#
                  end if;                                                        --#
                                                                                 --#
                  if tlpwdata = '0' then                                         --#
                     if RXREADY = '1' then                                       --#
                        tpd_state_r <= TPD_IDLE;                                 --#
                        rxlast_r    <= "00";                                     --#
                     end if;                                                     --#
                  elsif (tlprxreq = '1') then                                    --#
                     tpd_state_r <= TPD_RXACK;                                   --#
                  else                                                           --#
                     tpd_state_r <= TPD_RXH2_RXACK;                              --#                   
                  end if;           

               -- receive acknowledge -----------------------------------------
               when TPD_RXACK    =>

                  tlprxack_r <= tlprxreq;                                        --#
               
                  -- Transaction accepted by application, clear rxstart request
                  if RXREADY ='1' then
                     rxstart_r <=  '0';
                  end if;
                  -- End of TLP data receiving                                   --#
                  --if tlprxreq = '0' then                                       --#
                  --   tlprxack_r <= '0';                                        --#
                  --end if;                                                      --#
                  -- state transition and rxlast control
                  if tlpwdata = '1' then
                     if tlp4dwh = '1' then
                        datadw0_r <= tlprxdata(63 downto 32);
                        datadw1_r <= tlprxdata(31 downto 0);
                        dwwr0_r   <= tlprxdwe(1);
                        dwwr1_r   <= tlprxdwe(0);
                     else
                        dbuf_r      <= tlprxdata(31 downto 0);
                        dbufvalid_r <= tlprxdwe(0);
                        datadw0_r   <= dbuf_r;
                        datadw1_r   <= tlprxdata(63 downto 32);
                        dwwr0_r     <= dbufvalid_r;
                        dwwr1_r     <= tlprxdwe(1);
                     end if;
                     -- Last
                     if (rxcount_r = 2) or (rxcount_r = 1) then
                        rxlast_r    <= "11";
                     end if;
                     -- next state
                     if (tlprxreq = '1') or ((rxcount_r = 3) and tlp4dwh = '0') or TLPRXCORE = '0' then  --#    
                        tpd_state_r <= TPD_RXDATA;                                   --#    
                        rxvalid     <= '1';                                          --#
                     else                                                            --#   
                        tpd_state_r <= TPD_RXACK_RXDATA;                             --#                                                                  
                        if (rxcount_r = 2) or (rxcount_r = 1) then                   --#
                           rxvalid <= '1';                                           --#
                        end if;                                                      --#
                     end if;                                                         --#
                  elsif RXREADY = '1' then                                           
                     tpd_state_r <= TPD_IDLE;                                        --#
                     rxlast_r    <= "00";                                            --#
                  end if;

               -- between RXACK and RXDATA ------------------------------------
               when TPD_RXACK_RXDATA    =>                                       --#
                                                                                 --#
                  tlprxack_r <= tlprxreq;                                        --#
                                                                                 --#
                  -- Transaction accepted by application, clear rxstart request  --#
                  if RXREADY ='1' then                                           --#
                     rxstart_r <=  '0';                                          --#
                  end if;                                                        --#
                                                                                 --#
                  if rxlast_r(1) = '1' then                                      --#
                     if RXREADY = '1' then                                       --#
                        if (RXDONE = '1') then                                  --#
                           tpd_state_r <= TPD_IDLE;                              --#
                           rxlast_r    <= "00";                                  --#
                           dwwr0_r     <= '0';                                   --#
                           dwwr1_r     <= '0';                                   --#
                        else                                                     --#
                           tpd_state_r <= TPD_DONE;                              --#
                           rxlast_r    <= "11";                                  --#
                        end if;
                     end if;                                                     --#
                  elsif (tlprxreq = '1') then                                    --#
                     tpd_state_r <= TPD_RXDATA;                                  --#
                     rxvalid     <= '1';                                         --#
                  else                                                           --#
                     tpd_state_r <= TPD_RXACK_RXDATA;                            --#
                  end if;                                                        --#

               -- Receive data ------------------------------------------------
               when TPD_RXDATA   =>
                  
                  if TLPRXCORE = '1' and RXREADY = '1' then                      --#
                     tlprxack_r <= tlprxreq;                                     --#
                  end if;                                                        --#
               
                  -- Transaction accepted by application, clear rxstart request
                  if RXREADY ='1' then
                     rxstart_r <=  '0';
                     if tlp4dwh = '1' then
                        datadw0_r <= tlprxdata(63 downto 32);
                        datadw1_r <= tlprxdata(31 downto 0);
                     else
                        dbuf_r      <= tlprxdata(31 downto 0);
                        dbufvalid_r <= tlprxdwe(0);
                        datadw0_r   <= dbuf_r;
                        datadw1_r   <= tlprxdata(63 downto 32);
                     end if;
                  end if;
                  -- End of TLP data receiving
                  if TLPRXCORE = '0' then                                        --#
                     if tlprxreq = '0' and RXREADY = '1' then                    --#
                        tlprxack_r <= '0';                                       --#
                     end if;                                                     --#
                  end if;                                                        --#
                  -- rxlast assertion and deassertion                            
                  case rxcount_r is
                     when "0000000100" =>
                        if RXREADY = '1' then
                           dwwr0_r     <= '1';
                           dwwr1_r     <= '1';
                           rxlast_r    <= "11";
                        end if;
                     when "0000000011" =>
                        if RXREADY = '1' then
                           dwwr0_r     <= '1';
                           dwwr1_r     <= '0';
                           dbufvalid_r <= '0';
                           rxlast_r    <= "10";
                        end if;
                     when "0000000001"|"0000000010" =>
                        if RXREADY = '1' then
                           dwwr0_r     <= '0';
                           dwwr1_r     <= '0';
                           dbufvalid_r <= '0';
                           rxlast_r    <= "00";
                        end if;
                     when others =>
                        rxlast_r    <= "00";
                  end case;
                  -- rxcount control
                  if RXREADY ='1' then
                     if dwwr0_r = '1' and dwwr1_r = '1' then -- two DW write
                        rxcount_r <= rxcount_r - 2;
                     elsif dwwr0_r = '1' or dwwr1_r = '1' then -- single DW write
                        rxcount_r <= rxcount_r - 1;
                     end if;
                  end if;
                  -- State transition                                                  --#
                  if rxlast_r(1) = '1' then                                            --#
                     if RXREADY = '1' then                                             --#
                        if (RXDONE = '1') then                                        --#
                           tpd_state_r <= TPD_IDLE;                                    --#
                           rxlast_r    <= "00";                                        --#
                        else                                                           --#
                           tpd_state_r <= TPD_DONE;                                    --#
                           rxlast_r    <= "11";                                        --#
                        end if;
                     end if;                                                           --#
                  elsif (tlprxreq = '1') or (RXREADY = '0') or TLPRXCORE = '0' then    --#                
                     tpd_state_r <= TPD_RXDATA;                                        --#
                  else                                                                 --#
                     tpd_state_r <= TPD_RXDATA_AUX;                                    --#                                  
                     if (rxcount_r = "0000000011") or (rxcount_r = "0000000100") then  --#
                        rxvalid <= '1';                                                --#
                     else                                                             --# 
                        rxvalid <= '0';                                                --#
                     end if;                                                           --#
                  end if;

               -- Auxiliary 'Receive data' ------------------------------------------------
               when TPD_RXDATA_AUX   =>                                          --#
                                                                                 --#
                  tlprxack_r <= tlprxreq;                                        --#
                                                                                 --#
                  -- Transaction accepted by application, clear rxstart request  --#
                  if RXREADY ='1' then                                           --#
                     rxstart_r <=  '0';                                          --#
                  end if;                                                        --#
                                                                                 --#
                  if rxlast_r(1) = '1' then                                      --#
                     if RXREADY = '1' then                                       --#
                        if (RXDONE = '1') then                                   --#
                           tpd_state_r <= TPD_IDLE;                              --#
                           rxlast_r    <= "00";                                  --#
                        else                                                     --#
                           tpd_state_r <= TPD_DONE;                              --#
                           rxlast_r    <= "11";                                  --#
                        end if;
                     end if;                                                     --#
                  elsif (tlprxreq = '1' or TLPRXIDLE = '1') then                 --#
                     tpd_state_r <= TPD_RXDATA;                                  --#
                     rxvalid     <= '1';                                         --#
                  else                                                           --#
                     tpd_state_r <= TPD_RXDATA_AUX;                              --#                   
                  end if;                                                        --#

               -- Waiting for DONE from RX buffer ----------------------------------------
               when TPD_DONE   =>                                                --#                  

                  if (RXDONE = '1') then                                         --#
                     tpd_state_r <= TPD_IDLE;                                    --#
                     rxlast_r    <= "00";                                        --#
                     dwwr0_r     <= '0';                                         --#
                     dwwr1_r     <= '0';                                         --#
                  end if;                                                        --#
                 
            end case;
         end if;
      end if;
   end process;
end tlp_dec_arch;



