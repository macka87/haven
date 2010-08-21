--
-- rx_buf.vhd : RX buffer for PCIe to IB Bridge
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

library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use WORK.math_pack.all;
use WORK.bmem_func.all;

use work.ib_pkg.all; 

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--           ENTITY DECLARATION -- RX buffer for PCI Express Bridge          -- 
-- ----------------------------------------------------------------------------

entity RX_BUF is 
   generic(
      IB_BASE_ADDR  : std_logic_vector(31 downto 0) := X"FF000000"; -- IB Base Address
      LTAG_WIDTH    : integer   :=  5; -- 'Local Read' Buffer tag width
      GTAG_WIDTH    : integer   :=  5  -- 'Global Read' Buffer tag width       
   ); 
   port (
      -- clock & reset --------------------------------------------------------
      CLK          : in std_logic;  -- FPGA clock
      RESET        : in std_logic;  -- Reset active high

      -- PCI Express RX interface ---------------------------------------------
      TLPRX_REQ      : in std_logic;                     -- TLP data ready - receive requested
      TLPRX_ACK      : out std_logic;                    -- TLP data acknowledge - application acceppts data
      TLPRX_WAIT     : out std_logic;                    -- Pause TLP data
      TLPRX_READY    : out std_logic;                    -- TLP decoder ready
      TLPRX_IDLE     : in  std_logic;                    -- TransBuffer is idle (XILINX only)
      TLPRX_CORE     : in  std_logic;                    -- PCIe CORE (CAST=0/XILINX=1)            
      TLPRX_READBACK : in std_logic;                     -- Read-Back Write detected
      TLPRX_BARBASE  : in std_logic_vector(31 downto 0); -- Bar base address for IB transaction translation   
      TLPRX_BARMASK  : in std_logic_vector(31 downto 0); -- Bar mask for IB transaction translation         
      TLPRX_FULL     : out std_logic;                    -- Local Read Buffer full flag -> block next read

      TLPRX_DATA     : in std_logic_vector(63 downto 0); -- TLP receive data
      TLPRX_DWE      : in std_logic_vector(1 downto 0);  -- TLP transmit data DW enable            

      -- Internal Bus DOWN interface ------------------------------------------
      IB_DOWN_DATA      : out std_logic_vector(63 downto 0); -- IB data
      IB_DOWN_SOP_N     : out std_logic;                     -- start of packet
      IB_DOWN_EOP_N     : out std_logic;                     -- end of packet
      IB_DOWN_SRC_RDY_N : out std_logic;                     -- source ready
      IB_DOWN_DST_RDY_N : in  std_logic;                     -- destination ready

      -- Completion Buffer interface ------------------------------------------
      -- Write LR Buffer ifc --
      RXTC         : out std_logic_vector( 2 downto 0); -- Traffic Class     
      RXATTR       : out std_logic_vector( 1 downto 0); -- Attributes     
      RXTAG        : out std_logic_vector( 7 downto 0); -- Transaction Tag     
      RXBUS_NUM    : out std_logic_vector( 7 downto 0); -- Bus number           
      RXDEVICE_NUM : out std_logic_vector( 4 downto 0); -- Device number     
      RXFUNC_NUM   : out std_logic_vector( 2 downto 0); -- Function number  
      RXBMADDR     : out std_logic_vector(63 downto 0); -- BM global address

      RXWE         : out std_logic; -- RX write enable
      RXWTAG       : out std_logic_vector(LTAG_WIDTH-1 downto 0); -- RX write address      

      RXFULL       :  in std_logic; -- Local Read Buffer full flag      

      -- Read GR Buffer ifc --(Global Read buffer
      RXGRADDR_IN  : out std_logic_vector(31 downto 0); -- Global READ address
      RXGRTAG_IN   : out std_logic_vector(15 downto 0); -- completion tag for IB packet      
      RXWRITE      : out std_logic;  -- RX write enable      
      
      RXGRADDR_OUT : in  std_logic_vector(31 downto 0); -- Global READ address      
      RXGRTAG_OUT  : in  std_logic_vector(15 downto 0); -- completion tag for IB packet            
      RXRD         : out std_logic;  -- RX read enable
      RXRTAG       : out std_logic_vector(GTAG_WIDTH-1 downto 0); -- RX read address
      RXVLD        : in std_logic;   -- RX valid data      

      RXLAST       : out std_logic;  -- last read from GR Buffer

      -- Bus Master Buffer interface ------------------------------------------
      BM_GLOBAL_ADDR : in std_logic_vector(63 downto 0);  -- Global Address 
      BM_LOCAL_ADDR  : in std_logic_vector(31 downto 0);  -- Local Address
      BM_LENGTH      : in std_logic_vector(11 downto 0);  -- Length
      BM_TAG         : in std_logic_vector(15 downto 0);  -- Operation TAG
      
      BM_REQ_W       : in std_logic;                      -- Write Request
      BM_ACK_W       : out std_logic;                     -- Write Request accepted
      BM_FULL_W      : out std_logic;                     -- LR buffer full flag      
      
      BM_OP_TAG_R    : out std_logic_vector(15 downto 0); -- Read operation TAG 
      BM_OP_DONE_R   : out std_logic                      -- Read operation DONE 
   );
end RX_BUF;

-- ----------------------------------------------------------------------------
--       ARCHITECTURE DECLARATION  --  RX buffer for PCI Express Bridge      --
-- ----------------------------------------------------------------------------

architecture rx_buf_arch of RX_BUF is


   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   constant ZERO_TAG    : std_logic_vector(15-LTAG_WIDTH downto 0) := (others => '0');
   constant ZERO_TAG_BM : std_logic_vector( 6-LTAG_WIDTH downto 0) := (others => '0');
  
   constant C_L2LW     : std_logic_vector(2 downto 0) := "000";                       
   constant C_L2LR     : std_logic_vector(2 downto 0) := "001";   
   constant C_COMPL_WD : std_logic_vector(2 downto 0) := "101";
    
   constant TLPFMT_3DWH_ND : std_logic_vector(1 downto 0) := "00";     
   constant TLPFMT_4DWH_ND : std_logic_vector(1 downto 0) := "01";     
   constant TLPFMT_3DWH_WD : std_logic_vector(1 downto 0) := "10";     
   constant TLPFMT_4DWH_WD : std_logic_vector(1 downto 0) := "11";     
 
   constant TLPTYPE_MEM    : std_logic_vector(4 downto 0) := "00000";
   constant TLPTYPE_CPL    : std_logic_vector(4 downto 0) := "01010";

   constant TLPCMD_MRD32   : std_logic_vector(6 downto 0) := TLPFMT_3DWH_ND & TLPTYPE_MEM;
   constant TLPCMD_MRD64   : std_logic_vector(6 downto 0) := TLPFMT_4DWH_ND & TLPTYPE_MEM;
   constant TLPCMD_MWR32   : std_logic_vector(6 downto 0) := TLPFMT_3DWH_WD & TLPTYPE_MEM;
   constant TLPCMD_MWR64   : std_logic_vector(6 downto 0) := TLPFMT_4DWH_WD & TLPTYPE_MEM;
   constant TLPCMD_CPLWD   : std_logic_vector(6 downto 0) := TLPFMT_3DWH_WD & TLPTYPE_CPL;    
   constant TLPCMD_CPLND   : std_logic_vector(6 downto 0) := TLPFMT_3DWH_ND & TLPTYPE_CPL;    
     
   -- FSM types and signals
   type   fsm_states is (S_IDLE, S_START, S_READ_H2, S_WRITE_H2, S_COMPL_WD_H1,
                         S_COMPL_WD_H2, S_DATA, S_COMPL_ND, S_DATA_AUX, S_BM_H2,
                         S_DISCARD);
   signal present_state, next_state : fsm_states;

   -- Auxiliary signals
   signal cnt_tag      : std_logic_vector(LTAG_WIDTH-1 downto 0);
   signal cnt_tag_aux  : std_logic_vector(LTAG_WIDTH-1 downto 0);   
   signal cnt_tag_en   : std_logic;
   signal ib_tag_cpl   : std_logic_vector(15 downto 0);
   
   signal compl_last   : std_logic;
   signal len_aux      : std_logic_vector(31 downto 0);   
   signal rstn         : std_logic;
   signal recount_len  : std_logic;
   signal ib_type_cpl  : std_logic_vector( 3 downto 0);
   signal op_tag_reg   : std_logic_vector(15 downto 0);
   signal bm_result    : std_logic;
   signal bm_turn      : std_logic;
   signal bm_turn_sel  : std_logic_vector( 2 downto 0);
   signal reg_history  : std_logic;
   signal reg_history_en: std_logic;
   signal rx_start_dly : std_logic;
   signal last_cplread : std_logic; -- last read from global read buffer

   signal length_B     : std_logic_vector(11 downto 0);
   signal length_B_aux : std_logic_vector(12 downto 0);  
   signal length_B_cpl : std_logic_vector(11 downto 0);  
   signal length_B_rw  : std_logic_vector(11 downto 0);  
   signal length_B_cpl_aux : std_logic_vector(12 downto 0);  
   signal len_aux2     : std_logic_vector(12 downto 0);  

   signal be           : std_logic_vector( 7 downto 0);
   signal be_dec       : std_logic_vector( 2 downto 0);
   signal rxaddr01     : std_logic_vector( 1 downto 0);   
   signal rxaddr01_rw  : std_logic_vector( 1 downto 0);      
   signal local_addr   : std_logic_vector(31 downto 0);    
   
   signal align_reg    : std_logic;
   signal align_en     : std_logic;
   signal align_aux    : std_logic;
   signal do_align     : std_logic;   
   signal rx_data_dly  : std_logic_vector(63 downto 0);
  
   signal mpx_ib_data  : std_logic_vector(63 downto 0);
   signal mx_ib        : std_logic_vector( 2 downto 0);
   signal ib_type      : std_logic_vector( 2 downto 0);

   -- TLP Decoder signals
   signal rx_barbase   : std_logic_vector(31 downto 0); -- BAR BASE for IB translation
   signal rx_barmask   : std_logic_vector(31 downto 0); -- BAR MASK for IB translation   
   signal rx_readback  : std_logic;                     -- Read-Back Write detected
   signal rx_ready     : std_logic;                     -- Application ready to receive data
   signal rx_valid     : std_logic;                     -- Data valid
   signal rx_done      : std_logic;                     -- RX buffer done data transaction   
   signal rx_command   : std_logic_vector(6 downto 0);  -- TLP command
   signal rx_idle      : std_logic;                     -- Receiver Idle
   signal rx_start     : std_logic;                     -- Receive Start - all params valid
   signal rx_last      : std_logic;                     -- Last transfer
   signal rx_ptypereq  : std_logic;                     -- packet type - request
   signal rx_ptypecpl  : std_logic;                     -- packet type - completion
   signal rx_srcdevid  : std_logic_vector(15 downto 0); -- Source ID
   signal rx_tc        : std_logic_vector( 2 downto 0); -- Traffic Class
   signal rx_tag       : std_logic_vector(7 downto 0);  -- Tag
   signal rx_attr      : std_logic_vector( 1 downto 0); -- Attributes
   signal rx_address   : std_logic_vector(63 downto 0); -- address
   signal rx_length    : std_logic_vector(10 downto 0); -- length
   signal rx_dwena1st  : std_logic_vector( 3 downto 0); -- 1st DW enables
   signal rx_dwenalast : std_logic_vector( 3 downto 0); -- Last DW enables
   signal rx_cplstatus : std_logic_vector( 2 downto 0); -- Completion Status
   signal rx_cplbcount : std_logic_vector(12 downto 0); -- Completion Byte count
   signal rx_dwwr0     : std_logic;                     -- Write DW0
   signal rx_dwwr1     : std_logic;                     -- Write DW1
   signal rx_datadw0   : std_logic_vector(31 downto 0); -- Data DW0
   signal rx_datadw1   : std_logic_vector(31 downto 0); -- Data DW1
   signal rxtlp_memory : std_logic;                     -- TLP target is memory
   signal rxtlp_compl  : std_logic;                     -- TLP is a completion
   signal rxtlp_wd     : std_logic;                     -- TLP contains data
   signal rxtlp_nd     : std_logic;                     -- TLP doesn't contain data
  
begin

   -- -------------------------------------------------------------------------
   --                             TLP DECODER                                --
   -- -------------------------------------------------------------------------

   U_TLPDEC : entity work.TLP_DEC
   port map(
      -- common interface
      clk            => CLK,                             -- system clock
      rstn           => rstn,                            -- asynchronous reset
      -- TLP RX interface
      tlprxreq       => TLPRX_REQ,                       -- TLP data ready - receive requested
      tlprxdata      => TLPRX_DATA,                      -- TLP receive data
      tlprxdwe       => TLPRX_DWE,                       -- TLP transmit data DW enable
      tlprxcore      => TLPRX_CORE,                      -- PCIe CORE (CAST=0/XILINX=1)
      tlprxack       => TLPRX_ACK,                       -- TLP data acknowledge - application acceppts data
      tlprxwait      => TLPRX_WAIT,                      -- Pause TLP data
      tlprxready     => TLPRX_READY,                     -- TLP decoder ready      
      tlprxidle      => TLPRX_IDLE,                      -- TransBuffer is idle (XILINX only)
      tlprxreadback  => TLPRX_READBACK,                  -- Read-Back Write detected
      tlprxbarbase   => TLPRX_BARBASE,                   -- Bar base address for IB transaction translation 
      tlprxbarmask   => TLPRX_BARMASK,                   -- Bar mask for IB transaction translation       
      tlprxfull      => TLPRX_FULL,                      -- Local Read buffer full flag      
      -- Decoded TLP interface         
      rxready        => rx_ready,                        -- Application ready to receive data                 
      rxdone         => rx_done,                         -- RX buffer done
      rxvalid        => rx_valid,                        -- Data valid
      rxreadback     => rx_readback,                     -- Read-Back Write detected
      rxbarbase      => rx_barbase,                      -- Bar base address for IB transaction translation      
      rxbarmask      => rx_barmask,                      -- Bar mask for IB transaction translation            
      rxfull         => RXFULL,                          -- Local Read Buffer full flag 
      rxcommand      => rx_command,                      -- TLP command
      rxidle         => rx_idle,                         -- Receiver Idle
      rxstart        => rx_start,                        -- Receive Start - all params valid
      rxlast         => rx_last,                         -- Last transfer
      rxptypereq     => rx_ptypereq,                     -- packet type - request
      rxptypecpl     => rx_ptypecpl,                     -- packet type - completion
      rxsrcdevid     => rx_srcdevid,                     -- Source ID
      rxtc           => rx_tc,                           -- Traffic Class
      rxtag          => rx_tag,                          -- Tag
      rxattr         => rx_attr,                         -- Attributes
      rxaddress      => rx_address,                      -- address
      rxlength       => rx_length,                       -- length
      rxdwena1st     => rx_dwena1st,                     -- 1st DW enables
      rxdwenalast    => rx_dwenalast,                    -- Last DW enables
      rxcplstatus    => rx_cplstatus,                    -- Completion Status
      rxcplbcount    => rx_cplbcount,                    -- Completion Byte count
      rxdwwr0        => rx_dwwr0,                        -- Write DW0
      rxdwwr1        => rx_dwwr1,                        -- Write DW1
      rxdatadw0      => rx_datadw0,                      -- Data DW0
      rxdatadw1      => rx_datadw1                       -- Data DW1
      
   );

   rstn <= not RESET;
      
   -- -------------------------------------------------------------------------
   --                          TRANSFORMATION LOGIC                          --
   -- -------------------------------------------------------------------------

   -- IB packet length in B calculation (R/W) ---------------------------------
   be <= rx_dwenalast&rx_dwena1st;   
   
   be_decp: process(CLK, be)
   begin
      be_dec <= "000";

      case be is
         -- length = 1
         when "00001111" => be_dec <= "000";          
         when "00001110" => be_dec <= "001";                   
         when "00001100" => be_dec <= "010";                            
         when "00001000" => be_dec <= "011";                            
         when "00000000" => be_dec <= "000";
         
         when "00000111" => be_dec <= "001"; 
         when "00000011" => be_dec <= "010";
         when "00000110" => be_dec <= "010";
         when "00000100" => be_dec <= "011";
         when "00000010" => be_dec <= "011";
         when "00000001" => be_dec <= "011"; 
         
         -- length > 1         
         when "11111111" => be_dec <= "000";         
         when "11111110" => be_dec <= "001";         
         when "11111100" => be_dec <= "010";         
         when "11111000" => be_dec <= "011";         

         when "01111111" => be_dec <= "001";         
         when "01111110" => be_dec <= "010";         
         when "01111100" => be_dec <= "011";         
         when "01111000" => be_dec <= "100";         

         when "00111111" => be_dec <= "010";         
         when "00111110" => be_dec <= "011";         
         when "00111100" => be_dec <= "100";         
         when "00111000" => be_dec <= "101";                  

         when "00011111" => be_dec <= "011";         
         when "00011110" => be_dec <= "100";         
         when "00011100" => be_dec <= "101";         
         when "00011000" => be_dec <= "110";                  
         
         when others => be_dec <= "000";
      end case;
   end process;      

   length_B_auxp: process(rx_length, be_dec)
   begin
      length_B_aux <= (rx_length&"00") - ("0000000000"&be_dec);
   end process;

   length_B_rwp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (recount_len = '1') then
           length_B_rw <= length_B_aux(11 downto 0);
        end if;
     end if;
   end process;     

   -- IB packet length in B calculation (COMPL) -------------------------------
   length_B_cpl_auxp: process(rx_cplbcount, compl_last, rx_length, rx_address(1 downto 0))
   begin
      if (compl_last = '1') then
         length_B_cpl_aux <= rx_cplbcount;
      else
         length_B_cpl_aux <= (rx_length&"00") - ("00000000000"&rx_address(1 downto 0));
      end if;
   end process;

   length_B_cplp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (recount_len = '1') then
           length_B_cpl <= length_B_cpl_aux(11 downto 0);
        end if;
     end if;
   end process;        

   -- length_B selection ------------------------------------------------------
   length_B <= length_B_cpl when (rx_command = TLPCMD_CPLWD) else
               length_B_rw;
               
   -- Last Completion transaction decoder -------------------------------------
   len_aux2p: process(rx_cplbcount, rx_address(1 downto 0))
   begin
      len_aux2 <= rx_cplbcount + ("00000000000"&rx_address(1 downto 0)) + 3;
   end process;
   
   compl_last <= '1' when (rx_length = len_aux2(12 downto 2)) else           
                 '0';
                 
   -- -------------------------------------------------------------------------
   --                          DATA ALIGNMENT LOGIC                          --
   -- -------------------------------------------------------------------------
  
   -- Alignment Enable --
   align_regp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (RXVLD = '1') then
           align_reg <= RXGRADDR_OUT(2);
        end if;
     end if;
   end process;  

   mpx_align_enp: process(rx_ptypereq, align_reg, rx_address(2))
   begin
      case rx_ptypereq is
         when '0' => align_en <= align_reg;
         when '1' => align_en <= rx_address(2);         
         when others => align_en <= '0';
      end case;
   end process;

   -- Alignment Body --
   rx_data_dlyp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (rx_ready = '1') then
           rx_data_dly <= rx_datadw1&rx_datadw0;
        end if;
     end if;
   end process;  

   do_align <= align_en or align_aux;
   mpx_ib_datap: process(do_align, rx_datadw1, rx_datadw0, rx_data_dly)
   begin
      case do_align is
         when '0' => mpx_ib_data <= rx_datadw1&rx_datadw0;
         when '1' => mpx_ib_data <= rx_datadw0&rx_data_dly(63 downto 32);         
         when others => mpx_ib_data <= (others => '0');
      end case;
   end process; 
                
   -- -------------------------------------------------------------------------
   --                      COMPLETION BUFFER INTERFACE                       --
   -- -------------------------------------------------------------------------   

   -- 'Local Read' Tag counter --
   cnt_tagp: process(CLK, RESET)
   begin
      if (RESET = '1') then
         cnt_tag_aux <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (cnt_tag_en = '1') then
            cnt_tag_aux <= cnt_tag_aux + 1;
         end if;
      end if;
   end process;
   
   cnt_tag <= cnt_tag_aux;  

   -- RXGRADDR_IN, RXGRTAG_IN calculation --
   len_aux <= X"00000"&length_B;
   rxgraddr_inp: process(RXGRADDR_OUT, len_aux)
   begin
      RXGRADDR_IN <= RXGRADDR_OUT + len_aux;
   end process;   

   RXGRTAG_IN <= RXGRTAG_OUT;

   -- Output signals assigment --
   RXTC         <= rx_tc;
   RXATTR       <= rx_attr;
   RXTAG        <= rx_tag;
   RXBUS_NUM    <= rx_srcdevid(15 downto 8);
   RXDEVICE_NUM <= rx_srcdevid( 7 downto 3);
   RXFUNC_NUM   <= rx_srcdevid( 2 downto 0);
   RXBMADDR     <= BM_GLOBAL_ADDR;

   RXWE         <= cnt_tag_en;
   RXWTAG       <= cnt_tag;                
   
   RXRTAG       <= rx_tag(GTAG_WIDTH-1 downto 0);    

   RXLAST       <= last_cplread;

   -- -------------------------------------------------------------------------
   --                          BUS MASTER LOGIC                              --
   -- -------------------------------------------------------------------------    

   -- Bus Master Result decoder --
   bm_result   <= '1' when (rx_command = TLPCMD_CPLWD) and (rx_tag(7) = '1') else
                  '0';                      

   -- IB type for header 1 : completion/write with BM result --
   ib_type_cpl <= '0'&C_L2LW when bm_result = '1' else
                  compl_last&ib_type;

   -- Info about BM result passed to BM interface --
   op_tag_regp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (RXVLD = '1') then
           op_tag_reg <= RXGRTAG_OUT;
        end if;
     end if;
   end process;     

   BM_OP_TAG_R  <= op_tag_reg;
   
   BM_OP_DONE_R <= bm_result and compl_last and rx_done;

   BM_FULL_W    <= RXFULL;

   -- BM request vs. PCIE request resolution logic --
   rx_start_dlyp: process(RESET, CLK)
   begin
     if (RESET = '1') then
        rx_start_dly <= '0';
     elsif (CLK'event AND CLK = '1') then
        rx_start_dly <= rx_start;
     end if;
   end process;
   
   bm_turn_sel <= reg_history&rx_start_dly&BM_REQ_W;

   bm_turnp: process(bm_turn_sel) 
   begin
      case bm_turn_sel is
         when "000" => bm_turn <= '0';
         when "001" => bm_turn <= '1';
         when "010" => bm_turn <= '0';
         when "011" => bm_turn <= '1';

         when "100" => bm_turn <= '0'; 
         when "101" => bm_turn <= '1';
         when "110" => bm_turn <= '0';
         when "111" => bm_turn <= '0';
         when others => bm_turn <= '0';
      end case;
   end process;      

   reg_historyp: process(RESET, CLK)
   begin
     if (RESET = '1') then
        reg_history <= '0';
     elsif (CLK'event AND CLK = '1') then
        if (reg_history_en = '1') then
           reg_history <= bm_turn;
        end if;
     end if;
   end process;     

   -- -------------------------------------------------------------------------
   --                        INTERNAL BUS INTERFACE                          --
   -- -------------------------------------------------------------------------   

   ib_tag_cpl <= "0000000"&compl_last&X"80" when bm_result = '1' else
                 RXGRTAG_OUT;

   local_addr <= (     rx_barmask  and (rx_address(31 downto 2)&rxaddr01_rw)) or 
                 ((not rx_barmask) and rx_barbase);

   rxaddr01   <= "00" when (rx_command = TLPCMD_CPLWD) else
                 rxaddr01_rw;
                 
   rxaddr01_rwp: process(rx_dwena1st) 
   begin
      case rx_dwena1st is
         when "1111" => rxaddr01_rw <= "00";
         when "1110" => rxaddr01_rw <= "01";
         when "1100" => rxaddr01_rw <= "10";
         when "1000" => rxaddr01_rw <= "11";

         when "0111" => rxaddr01_rw <= "00"; 
         when "0011" => rxaddr01_rw <= "00";
         when "0110" => rxaddr01_rw <= "01";
         when "0100" => rxaddr01_rw <= "10";
         when "0010" => rxaddr01_rw <= "01";
         when "0001" => rxaddr01_rw <= "00";
         
         when others => rxaddr01_rw <= "00";
      end case;
   end process;   

   mpx_ibp: process(mx_ib, mpx_ib_data, rx_address(31 downto 2),rxaddr01,cnt_tag, ib_type, length_B,BM_GLOBAL_ADDR,ib_tag_cpl,
                    RXGRADDR_OUT, ib_type_cpl, RXGRTAG_OUT, rx_readback, BM_TAG, BM_LENGTH, BM_LOCAL_ADDR, local_addr)          
   begin
      case mx_ib is
         when "000" => IB_DOWN_DATA <= local_addr&ZERO_TAG&cnt_tag&rx_readback&ib_type&length_B; -- W/R header 1
         when "001" => IB_DOWN_DATA <= RXGRADDR_OUT&ib_tag_cpl&ib_type_cpl&length_B;             -- COMPL/WRITE WITH BM RESULT header 1         
         when "010" => IB_DOWN_DATA <= X"00000000"&IB_BASE_ADDR(31 downto 2)&rxaddr01;           -- header2
         when "011" => IB_DOWN_DATA <= mpx_ib_data;                                              -- data
         
         when "100" => IB_DOWN_DATA <= (BM_LOCAL_ADDR)&BM_TAG(7 downto 0)&'1'&ZERO_TAG_BM&cnt_tag&"0"&ib_type&BM_LENGTH;           -- READ (for BM) header 1 
         when "101" => IB_DOWN_DATA <= X"00000000"&IB_BASE_ADDR(31 downto 12)&BM_TAG(15 downto 8)&"0"&BM_GLOBAL_ADDR(2 downto 0); -- READ (for BM) header 2         
         when others => IB_DOWN_DATA <= (others => '0');
      end case;
   end process;    
     
   -- -------------------------------------------------------------------------
   --                             CONTROL FSM                                --
   -- -------------------------------------------------------------------------

   -- FSM synchronize logic ---------------------------------------------------
   synchlogp : process(RESET, CLK)
   begin
      if (RESET = '1') then
         present_state <= S_IDLE;
      elsif (CLK'event and CLK = '1') then
         present_state <= next_state;
      end if;
   end process;
   
   rxtlp_memory <= '1' when rx_command(4 downto 0) = "00000" else '0';
   rxtlp_compl  <= '1' when rx_command(4 downto 0) = "01010" else '0';
   rxtlp_wd     <= rx_command(6);
   rxtlp_nd     <= not rx_command(6);

   -- FSM next state logic ----------------------------------------------------
   nextstatelogicp : process(present_state, IB_DOWN_DST_RDY_N, rx_start, rx_last, 
                             rx_command, rx_length(0), align_en, rx_valid, 
                             BM_REQ_W, bm_turn, rxtlp_memory, rxtlp_compl)
   begin
      next_state <= present_state;

      case (present_state) is

         when  S_IDLE => 
                  if    ((rx_start = '1' or BM_REQ_W = '1') and (IB_DOWN_DST_RDY_N = '0')) then
                     next_state <= S_START;
                  end if;

         -- START --
         when  S_START => 
                  if (bm_turn = '1' and IB_DOWN_DST_RDY_N = '0') then
                     next_state <= S_BM_H2;
                  elsif ((rx_start = '1') and (IB_DOWN_DST_RDY_N = '0')) then
                  
                     if (rxtlp_nd = '1') then -- TLP without data
                        if rxtlp_memory = '1' then
                           next_state <= S_READ_H2;
                        elsif rxtlp_compl = '1' then
                           next_state <= S_COMPL_ND;
                        else
                           next_state <= S_DISCARD;
                        end if;
                     else -- TLP with data
                        if rxtlp_memory = '1' then
                           next_state <= S_WRITE_H2;
                        elsif rxtlp_compl = '1' then
                           next_state <= S_COMPL_WD_H1;
                        else
                           next_state <= S_DISCARD;
                        end if;
                     end if;
                  end if;

         -- READ --
         when  S_READ_H2 =>                   
                  if (IB_DOWN_DST_RDY_N = '0') then
                     next_state <= S_IDLE;
                  end if;

         -- BM --
         when  S_BM_H2 =>                   
                  if (IB_DOWN_DST_RDY_N = '0') then
                     next_state <= S_IDLE;
                  end if;                  

         -- WRITE --
         when  S_WRITE_H2 =>                   
                  if (IB_DOWN_DST_RDY_N = '0') then
                     next_state <= S_DATA;
                  end if;         

         -- COMPLETION WITH DATA --
         when  S_COMPL_WD_H1 => 
                   if (IB_DOWN_DST_RDY_N = '0') then
                      next_state <= S_COMPL_WD_H2;
                   end if;                  
 
         when  S_COMPL_WD_H2 =>                   
                  if (IB_DOWN_DST_RDY_N = '0') then
                     next_state <= S_DATA;
                  end if;                  

         -- DATA --        
         when  S_DATA =>                   
                  if ((IB_DOWN_DST_RDY_N = '0') and rx_last = '1' and rx_valid = '1') then 
                     if (align_en = '0' or rx_length(0) = '1') then
                        next_state <= S_IDLE;
                     else
                        next_state <= S_DATA_AUX;
                     end if;                                                           
                  end if;

         when  S_DATA_AUX =>
                  if (IB_DOWN_DST_RDY_N = '0') then                                 
                     next_state <= S_IDLE;
                  end if;                                          

         -- COMPLETION NO DATA --
         when  S_COMPL_ND =>                            
                     next_state <= S_IDLE;
                     
         -- Discard unspopported packets (messages etc.)
         when  S_DISCARD =>                   
                  if (rx_last = '1') or (rx_valid = '0') then
                     next_state <= S_IDLE;
                  else
                     next_state <= S_DISCARD;
                  end if;                                                           
                 
      end case;       
   end process;   

   -- FSM output logic --------------------------------------------------------
   outputlogicp : process(present_state, IB_DOWN_DST_RDY_N, rx_start, rx_last, 
                          rx_command, rx_length(0), align_en, rx_valid, 
                          BM_REQ_W, bm_turn, compl_last)
   begin

      RXRD        <= '0';
      RXWRITE     <= '0';
      
      cnt_tag_en  <= '0';
      mx_ib       <= "000";
      ib_type     <= "000";
      align_aux   <= '0';
      recount_len <= '0';
      reg_history_en <= '0';
      last_cplread   <= '0';
      
      rx_done    <= '0';      
      rx_ready   <= '0';
      
      IB_DOWN_SOP_N <= '1';
      IB_DOWN_EOP_N <= '1';
      IB_DOWN_SRC_RDY_N <= '1';
      BM_ACK_W      <= '0';
 
      case (present_state) is   

         when  S_IDLE => 
                  --if (rx_start = '1' and IB_DOWN_DST_RDY_N = '0') then
                     recount_len <= '1';
                  --end if;

        -- START --
         when  S_START => 
                     recount_len <= '1';
                     
                  if    (bm_turn = '1' and IB_DOWN_DST_RDY_N = '0') then
                     reg_history_en <= '1';
                     cnt_tag_en <= '1';
                     mx_ib      <= "100";
                     ib_type    <= C_L2LR;
                     IB_DOWN_SOP_N <= '0';
                     IB_DOWN_SRC_RDY_N <= '0';
                  elsif ((rx_start = '1') and (IB_DOWN_DST_RDY_N = '0')) then
                     case rx_command is
                        when TLPCMD_MRD32 | TLPCMD_MRD64 =>
                           reg_history_en <= '1';
                           cnt_tag_en <= '1';
                           mx_ib      <= "000";
                           ib_type    <= C_L2LR;
                           IB_DOWN_SOP_N <= '0';
                           IB_DOWN_SRC_RDY_N <= '0';
                        when TLPCMD_MWR32 | TLPCMD_MWR64 =>
                           reg_history_en <= '1';
                           mx_ib      <= "000";
                           ib_type    <= C_L2LW;
                           IB_DOWN_SOP_N <= '0';  
                           IB_DOWN_SRC_RDY_N <= '0';
                        when TLPCMD_CPLWD =>
                           reg_history_en <= '1';
                           RXRD <= '1';          
                        when others => null;
                     end case;
                  end if;                  

         -- READ --
         when  S_READ_H2 =>              
                  IB_DOWN_SRC_RDY_N <= '0';
                  if (IB_DOWN_DST_RDY_N = '0') then         
                    mx_ib      <= "010";
                    rx_ready   <= '1';
                    IB_DOWN_EOP_N <= '0';                     
                  end if;

         -- BM --
         when  S_BM_H2 =>              
                  IB_DOWN_SRC_RDY_N <= '0';
                  if (IB_DOWN_DST_RDY_N = '0') then         
                    mx_ib      <= "101";
                    IB_DOWN_EOP_N <= '0'; 
                    BM_ACK_W   <= '1';
                  end if;                  

         -- WRITE --
         when  S_WRITE_H2 =>                             
                    mx_ib      <= "010";
                    IB_DOWN_SRC_RDY_N <= '0';                    
                                                              
         -- COMPLETION WITH DATA --                                              
         when  S_COMPL_WD_H1 =>           
                  IB_DOWN_SRC_RDY_N <= '0';
                  if (IB_DOWN_DST_RDY_N = '0') then         
                     mx_ib <= "001";
                     ib_type <= C_COMPL_WD;
                     RXWRITE <= '1';
                     IB_DOWN_SOP_N <= '0';   
                     last_cplread  <= compl_last;
                  else
                     RXRD <= '1';                   
                  end if;
                                                                                 
         when  S_COMPL_WD_H2 =>                                                  
                    mx_ib      <= "010";       
                    IB_DOWN_SRC_RDY_N <= '0';

         -- DATA --                    
         when  S_DATA =>     
                  if (rx_valid = '1') then
                     IB_DOWN_SRC_RDY_N <= '0';
                  
                     if (IB_DOWN_DST_RDY_N = '0') then               
                        mx_ib      <= "011";
                        rx_ready   <= '1';
                        if (rx_last = '1') then
                           if (align_en = '0' or rx_length(0) = '1') then
                              IB_DOWN_EOP_N <= '0';                                                               
                              rx_done       <= '1';
                           end if;
                        end if;                        
                     end if;                                                                                                                                
                  end if;

         when  S_DATA_AUX =>
                  IB_DOWN_SRC_RDY_N <= '0';         
                  if (IB_DOWN_DST_RDY_N = '0') then
                     align_aux     <= '1';
                     mx_ib         <= "011";
                     IB_DOWN_EOP_N <= '0';    
                     rx_done       <= '1';
                     rx_ready   <= '1';
                  end if;                        

         -- COMPLETION NO DATA --                                                
         when  S_COMPL_ND =>                                                     
                    rx_ready   <= '1';
                    
         when  S_DISCARD =>     
                    rx_ready   <= '1';
                    rx_done    <= '1';
                    
      end case;       
   end process;  
   
   -- -------------------------------------------------------------------------   
  
end rx_buf_arch;

