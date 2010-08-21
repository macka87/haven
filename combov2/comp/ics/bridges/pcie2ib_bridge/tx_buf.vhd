--
-- tx_buf.vhd : TX buffer for PCIe to IB Bridge
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
--           ENTITY DECLARATION -- TX buffer for PCIe to IB Bridge           -- 
-- ----------------------------------------------------------------------------

entity TX_BUF is 
   generic(
      LTAG_WIDTH     : integer :=   5; -- 'Local Read' Buffer tag width
      GTAG_WIDTH     : integer :=   5  -- 'Global Read' Buffer tag width       
   ); 
   port (
      -- clock & reset --------------------------------------------------------
      CLK            : in std_logic;  -- FPGA clock
      RESET          : in std_logic;  -- Reset active high

      -- PCI Express TX interface ---------------------------------------------
      TLPTX_REQ      : out std_logic;                     -- Request TLP transmission
      TLPTX_ACK      : in  std_logic;                     -- TLM ready to accept TLP
      TLPTX_WAIT     : in  std_logic;                     -- Pause TLP data

      TLPTX_DATA     : out std_logic_vector(63 downto 0); -- TLP transmit data
      TLPTX_DWE      : out std_logic_vector(1 downto 0);  -- TLP transmit data DW enable            

      -- Internal Bus UP interface --------------------------------------------
      IB_UP_DATA      : in std_logic_vector(63 downto 0); -- IB data
      IB_UP_SOP_N     : in std_logic;                     -- start of packet
      IB_UP_EOP_N     : in std_logic;                     -- end of packet
      IB_UP_SRC_RDY_N : in std_logic;                     -- source ready
      IB_UP_DST_RDY_N : out std_logic;                    -- destination ready 
      
      -- Completion Buffer interface ------------------------------------------
      -- Read LR Buffer ifc --
      TXTC         : in std_logic_vector( 2 downto 0); -- Traffic Class     
      TXATTR       : in std_logic_vector( 1 downto 0); -- Attributes     
      TXTAG        : in std_logic_vector( 7 downto 0); -- Transaction Tag     
      TXBUS_NUM    : in std_logic_vector( 7 downto 0); -- Bus number           
      TXDEVICE_NUM : in std_logic_vector( 4 downto 0); -- Device number     
      TXFUNC_NUM   : in std_logic_vector( 2 downto 0); -- Function number     
      TXBMADDR     : in std_logic_vector(63 downto 0); -- BM global address             

      TXRD         : out std_logic;  -- TX read enable
      TXRTAG       : out std_logic_vector(LTAG_WIDTH-1 downto 0); -- TX read address                  
      TXVLD        : in  std_logic;  -- TX valid data                                                 
                                                                                                      
      -- Write GR Buffer ifc --
      TXGRADDR     : out std_logic_vector(31 downto 0); -- Global READ address
      TXGRTAG      : out std_logic_vector(15 downto 0); -- completion tag for IB packet

      TXWE         : out std_logic; -- TX write enable
      TXWTAG       : out std_logic_vector(GTAG_WIDTH-1 downto 0);  -- TX write address     
      TXFULL       : in  std_logic; -- Global Read Buffer full flag   

      -- Bus Master Buffer interface ------------------------------------------
      BM_GLOBAL_ADDR : in std_logic_vector(63 downto 0);  -- Global Address 
      BM_LOCAL_ADDR  : in std_logic_vector(31 downto 0);  -- Local Address
      BM_LENGTH      : in std_logic_vector(11 downto 0);  -- Length
      BM_TAG         : in std_logic_vector(15 downto 0);   -- Operation TAG
      
      BM_REQ_R       : in std_logic;                      -- Read Request  
      BM_ACK_R       : out std_logic;                     -- Read Request accepted
      BM_FULL_R      : out std_logic;                     -- GR buffer full flag
      
      BM_OP_TAG_W    : out std_logic_vector(15 downto 0);  -- Write operation TAG
      BM_OP_DONE_W   : out std_logic;                     -- Write operation DONE
      
      -- Configuration interface ----------------------------------------------
      BUS_NUM          : in std_logic_vector(7 downto 0); -- Bus number           
      DEVICE_NUM       : in std_logic_vector(4 downto 0); -- Device number             
      FUNC_NUM         : in std_logic_vector(2 downto 0); -- Function number                   
      MAX_PAYLOAD_SIZE : in std_logic_vector(2 downto 0)  -- Maximum Payload TLP Size      
   );
end TX_BUF;

-- ----------------------------------------------------------------------------
--       ARCHITECTURE DECLARATION  --  TX buffer for PCIe to IB Bridge       --
-- ----------------------------------------------------------------------------

architecture tx_buf_arch of TX_BUF is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   constant ZERO_TAG   : std_logic_vector(8 - GTAG_WIDTH - 1 downto 0)      := (others => '0');
   constant ZERO_TAG_BM: std_logic_vector(8 - GTAG_WIDTH - 1 -1 downto 0)      := (others => '0');   

   -- Transaction constants
   constant T_L2LW     : std_logic_vector(2 downto 0) := "000";                       
   constant T_L2LR     : std_logic_vector(2 downto 0) := "001";   
   constant T_L2GW     : std_logic_vector(2 downto 0) := "010";
   constant T_G2LR     : std_logic_vector(2 downto 0) := "011";

   constant T_COMPL_WD : std_logic_vector(2 downto 0) := "101";
   constant T_COMPL_ND : std_logic_vector(2 downto 0) := "111";   

   -- TLP Generator Command constants
   constant CMD_COMPL  : std_logic_vector(6 downto 0) := "10"&"01010";   
   constant CMD_WRITE32: std_logic_vector(6 downto 0) := "10"&"00000";      
   constant CMD_WRITE64: std_logic_vector(6 downto 0) := "11"&"00000";         
   constant CMD_READ32 : std_logic_vector(6 downto 0) := "00"&"00000";      
   constant CMD_READ64 : std_logic_vector(6 downto 0) := "01"&"00000";          

   -- Transaction Traffic Types
   constant TTT_POSTED     : std_logic_vector(1 downto 0) := "00";   
   constant TTT_NONPOSTED  : std_logic_vector(1 downto 0) := "01";   
   constant TTT_COMPLETION : std_logic_vector(1 downto 0) := "10";   
     
   -- FSM types and signals
   type   fsm_states is (S_IDLE, S_READ, S_READ_START, S_READ_DONE, S_DATA_RECEIVE1, 
                         S_DATA_RECEIVE2, S_DATA_RECEIVE3, S_TRANSMIT_START, S_TRANSMIT_DONE,
                         S_RECOUNT1, S_RECOUNT2, S_HEADER1, S_DATA_RECEIVE_NEXT_FRAGMENTS, S_LOAD_FROM_REG,
                         S_BM_H1, S_BM, S_BM_START, S_BM_DONE, S_IDLE1, S_IDLE2);
                         
   signal present_state, next_state : fsm_states;

   -- Auxiliary signals
   signal data_payload        : std_logic_vector(63 downto 0);
   signal data_payload_vld    : std_logic;
   signal ibtype_dec          : std_logic_vector( 6 downto 0);
                          
   signal reg_bytecount       : std_logic_vector(12 downto 0);
   signal bytecount_aux       : std_logic_vector(12 downto 0);      
   signal reg_length          : std_logic_vector(12 downto 0);
   signal reg_length_DW       : std_logic_vector(10 downto 0);
   signal reg_length_DW_aux   : std_logic_vector(12 downto 0);
   signal reg_length_DW_minus1       : std_logic_vector(10 downto 0);
   signal reg_length_DW_minus1_aux   : std_logic_vector(12 downto 0);   
   signal reg_tc              : std_logic_vector( 2 downto 0);
   signal reg_tag             : std_logic_vector( 7 downto 0);
   signal reg_reqid           : std_logic_vector(15 downto 0);
   signal reg_command         : std_logic_vector( 6 downto 0);
   signal reg_command_hdr3    : std_logic;
   signal hdr3_dec            : std_logic;
   signal reg_attr            : std_logic_vector( 1 downto 0);
   
   signal reg_ibtag           : std_logic_vector(15 downto 0);
   signal reg_ibaddr_secundar : std_logic_vector(31 downto 0);
   signal reg_ibaddr_primar   : std_logic_vector(63 downto 0);
   signal reg_ibaddr_primar_l : std_logic_vector(31 downto 0);
   signal reg_ibaddr_primar_h : std_logic_vector(31 downto 0);

   signal reg_bmaddr              : std_logic_vector(63 downto 0);
   signal reg_bmtag               : std_logic_vector(15 downto 0);
   signal bm_result               : std_logic;
   signal bm_result_rst           : std_logic;
   signal bm_result_reg           : std_logic;   
   signal data_op_done            : std_logic;
   signal idle                    : std_logic;

   signal reg_ibtag_mpx           : std_logic_vector(15 downto 0);
   signal reg_ibaddr_secundar_mpx : std_logic_vector(31 downto 0);
   signal reg_ibaddr_primar_l_mpx : std_logic_vector(31 downto 0);
   signal reg_ibaddr_primar_h_mpx : std_logic_vector(31 downto 0);
   signal reg_ibtype_mpx          : std_logic_vector( 2 downto 0);
   signal bm_req                  : std_logic;
   
   signal reg_align           : std_logic_vector(12 downto 0);
   signal reg_align_en        : std_logic;
   signal reg_globaddr        : std_logic_vector(63 downto 0);
   signal reg_lowerbits       : std_logic_vector( 6 downto 0);
   signal reg_ibtype          : std_logic_vector( 2 downto 0);
   signal ib_up_data_dly      : std_logic_vector(31 downto 0);
   signal first_recount       : std_logic;
   signal do_firstparse       : std_logic;
   signal reg_do_firstparse   : std_logic;
   signal compare_condition   : std_logic;
                           
   signal sub_align           : std_logic_vector(12 downto 0);
   signal sub_bytecount       : std_logic_vector(12 downto 0);
   signal add_addr            : std_logic_vector(11 downto 0);
   signal mpx_A               : std_logic_vector(63 downto 0);
   signal mpx_B               : std_logic_vector(63 downto 0);
   signal sub_limit           : std_logic_vector(10 downto 0);
   signal be_result           : std_logic_vector( 1 downto 0);
   signal firstbe_sel         : std_logic_vector( 3 downto 0);   
                            
   signal first_rw            : std_logic;
   signal transmit_1st        : std_logic;
   signal dst_rdy_n           : std_logic;
   signal compl_rst           : std_logic;
   signal first_transfer      : std_logic;
   signal last_transfer       : std_logic;   
   signal end_of_align        : std_logic;
   signal ib_header0          : std_logic;
   signal ib_header1          : std_logic;
   signal ib_header1_dly      : std_logic;
   signal reg_eop_n             : std_logic;

   signal first_fragment     : std_logic;
   signal first_fragment_reg : std_logic;
   signal first_fragment_rst : std_logic;   
                              
   signal cnt_tag             : std_logic_vector(GTAG_WIDTH-1 downto 0);
   signal cnt_tag_en          : std_logic;
   signal cnt_tag_aux         : std_logic_vector(GTAG_WIDTH-1 downto 0);
   signal cnt_data            : std_logic_vector(9 downto 0);
   signal cnt_data_aux        : std_logic_vector(9 downto 0);
   signal cnt_data_rst        : std_logic;
                             
   signal recount_len           : std_logic;
   signal recount_len_dly       : std_logic;
   signal recount_addr          : std_logic;
   signal recount_bc            : std_logic;
   signal recount_first_len_odd : std_logic;
                              
   signal first_len_odd       : std_logic;
   signal tx_read             : std_logic;
   signal data_read           : std_logic;
   signal data_write          : std_logic;

   signal bm_turn        : std_logic;
   signal bm_turn_sel    : std_logic_vector( 2 downto 0);
   signal reg_history    : std_logic := '0';
   signal reg_history_en : std_logic;   
                               
   signal mpx_address         : std_logic_vector(63 downto 0);
   signal mpx_length          : std_logic_vector(12 downto 0);
   signal mpx_rlen            : std_logic_vector(12 downto 0);
   signal mpx_bytecount       : std_logic_vector(12 downto 0);
   signal mpx_minus           : std_logic_vector( 6 downto 0);
   signal mpx_minus_aux       : std_logic_vector(12 downto 0);
   signal mpx_ib_up_data      : std_logic_vector(63 downto 0);
   signal mpx_ib_up_data_low  : std_logic_vector(31 downto 0);
   signal mpx_ib_up_data_high : std_logic_vector(31 downto 0);   
   signal mpx_3HD_1st_odd     : std_logic_vector(31 downto 0);   
   signal switch_3HD_1st_odd  : std_logic;
   signal ib_up_data_switch   : std_logic;
   signal mpx_tag             : std_logic_vector( 7 downto 0);
   signal rstn                : std_logic;   
   signal limit               : std_logic_vector( 8 downto 0);
   signal tlptx_srcrdy        : std_logic;

   signal mpx_data_payload        : std_logic_vector(63 downto 0);
   signal data_payload1_dly       : std_logic_vector(31 downto 0);
   signal tx_datadw1_aligned      : std_logic_vector(31 downto 0);
   signal tx_datadw0_aligned      : std_logic_vector(31 downto 0);
   signal data_payload_switch     : std_logic;
   signal data_payload_switch_aux : std_logic;

   -- TLP generator  signals
   signal tx_start     : std_logic;
   signal tx_command   : std_logic_vector(6 downto 0);
   signal tx_srcdevid  : std_logic_vector(15 downto 0);
   signal tx_dstdevid  : std_logic_vector(15 downto 0);
   signal tx_tag       : std_logic_vector(7 downto 0);
   signal tx_tc        : std_logic_vector(2 downto 0);
   signal tx_address   : std_logic_vector(63 downto 0);
   signal tx_length    : std_logic_vector(10 downto 0);
   signal tx_dwena1st  : std_logic_vector( 3 downto 0);
   signal tx_dwenafirst: std_logic_vector( 3 downto 0);
   signal tx_dwenalast : std_logic_vector( 3 downto 0); 
   signal tx_bytecount : std_logic_vector(12 downto 0);
   signal tx_datadw0   : std_logic_vector(31 downto 0);
   signal tx_datadw1   : std_logic_vector(31 downto 0);
   signal tx_ready     : std_logic;
   signal tx_done      : std_logic;
   signal tx_dwrd0     : std_logic;
   signal tx_dwrd1     : std_logic;

   -- constants derived from MAX_PAYLOAD_SIZE
   signal TLP_MAX_LEN_13 : std_logic_vector(12 downto 0); -- TLP_MAX_LEN
   signal TLP_MAX_LEN_13_MINUS_1 : std_logic_vector(12 downto 0); -- TLP_MAX_LEN-1
   signal TLP_MAX_LEN_13_MINUS_2 : std_logic_vector(12 downto 0); -- TLP_MAX_LEN-2
   signal REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN : std_logic_vector(12 downto 0); -- reg_bytecount(12 downto log2(TLP_MAX_LEN)
   signal REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0 : std_logic_vector(12 downto 0); -- reg_bytecount(log2(TLP_MAX_LEN)-1 downto 0)

   -- data alignment block signals
   signal UP_DATA      : std_logic_vector(63 downto 0);
   signal UP_SOP_N     : std_logic;                    
   signal UP_EOP_N     : std_logic;                    
   signal UP_SRC_RDY_N : std_logic;                    
   signal UP_DST_RDY_N : std_logic;                   
                                                 
begin

   -- -------------------------------------------------------------------------
   --                CONSTANTS DERIVED FROM MAX_PAYLOAD_SIZE                 --
   -- -------------------------------------------------------------------------

   U_CONST : entity work.TX_BUF_CONST 
   port map (
      -- clock & reset --------------------------------------------------------
      CLK              => CLK,  
      RESET            => RESET,

      -- input signals --------------------------------------------------------
      MAX_PAYLOAD_SIZE => MAX_PAYLOAD_SIZE,
      REG_BYTECOUNT    => reg_bytecount,   

      -- output derived signals -----------------------------------------------
      TLP_MAX_LEN_13 => TLP_MAX_LEN_13,
      TLP_MAX_LEN_13_MINUS_1 => TLP_MAX_LEN_13_MINUS_1,  
      TLP_MAX_LEN_13_MINUS_2 => TLP_MAX_LEN_13_MINUS_2,
      REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN => REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN,
      REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0 => REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0  
   );

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

   -- FSM next state logic ----------------------------------------------------
   nextstatelogicp : process(present_state,tx_done,reg_bytecount, reg_length, cnt_data, limit, 
                             UP_SRC_RDY_N, reg_eop_n, ibtype_dec, UP_SOP_N, BM_REQ_R, UP_DATA, bm_turn)   
   begin                                               
      next_state <= present_state;                      

      case (present_state) is

         -- MAIN branch -------------------------------------------------------      

         when  S_IDLE => 
                  if (bm_turn = '1') then
                     next_state <= S_BM_H1;                                     -- type = COMPLETION & BM result flag (tag[7])
                  elsif (UP_SOP_N = '0' and UP_SRC_RDY_N = '0' and UP_DATA(14 downto 12)=T_COMPL_WD and UP_DATA(23)='1') then       
                     next_state <= S_IDLE1; 
                  elsif (UP_SOP_N = '0' and UP_SRC_RDY_N = '0') then       
                     next_state <= S_HEADER1;
                  end if;

         when S_IDLE1 => 
                     next_state <= S_IDLE2;

         when S_IDLE2 => 
                  if (UP_SOP_N = '0' and UP_SRC_RDY_N = '0') then       
                     next_state <= S_HEADER1;
                  end if;         

         when  S_HEADER1 =>                   
                  if    ((ibtype_dec = CMD_READ32 or ibtype_dec = CMD_READ64) and UP_SRC_RDY_N = '0') then
                     next_state <= S_READ;
                  elsif ((ibtype_dec = CMD_WRITE32 or ibtype_dec = CMD_WRITE64) and UP_SRC_RDY_N = '0') then
                     next_state <= S_DATA_RECEIVE1; 
                  elsif ((ibtype_dec = CMD_COMPL) and UP_SRC_RDY_N = '0') then
                     next_state <= S_DATA_RECEIVE1;    
                  end if;

         -- READ branch -------------------------------------------------------
         
         when S_READ => 
                  next_state <= S_READ_START;         
         
         when S_READ_START => 
                  next_state <= S_READ_DONE;

         when S_READ_DONE => 
                  if (tx_done = '1') then
                     next_state <= S_IDLE;
                  end if;

         -- BUS MASTER branch -------------------------------------------------
         when S_BM_H1 =>
                  next_state <= S_BM;
           
         when S_BM => 
                  next_state <= S_BM_START;         
         
         when S_BM_START => 
                  next_state <= S_BM_DONE;

         when S_BM_DONE => 
                  if (tx_done = '1') then
                     next_state <= S_IDLE;
                  end if;         

         -- DATA RECEIVE branch -----------------------------------------------

         -- First fragment reception --
         when S_DATA_RECEIVE1 => 
                     next_state <= S_DATA_RECEIVE2;

         when S_DATA_RECEIVE2 =>                  
                     next_state <= S_DATA_RECEIVE3;

         when S_DATA_RECEIVE3 =>                          
                  if ((cnt_data(8 downto 0) = limit and UP_SRC_RDY_N = '0')) then 
                     next_state <= S_LOAD_FROM_REG;
                  end if;                  

         -- Next fragment reception --
         when S_DATA_RECEIVE_NEXT_FRAGMENTS =>
                 if ((cnt_data(8 downto 0) = limit and UP_SRC_RDY_N = '0') or reg_eop_n = '0') then 
                     next_state <= S_LOAD_FROM_REG;
                  end if;                           

         -- Supplemental load from ib_up_data_reg --
         when S_LOAD_FROM_REG =>
                  next_state <= S_TRANSMIT_START;

         -- DATA TRANSMIT branch ----------------------------------------------

         when S_TRANSMIT_START =>
                  next_state <= S_TRANSMIT_DONE;               

         when S_TRANSMIT_DONE =>
                  if (tx_done = '1') then
                     if (reg_bytecount = reg_length) then
                        next_state <= S_IDLE;
                     else
                        next_state <= S_RECOUNT1;
                     end if;
                  end if;

         when S_RECOUNT1 =>
                        next_state <= S_RECOUNT2;

         when S_RECOUNT2 =>
                        next_state <= S_DATA_RECEIVE_NEXT_FRAGMENTS;
                 
      end case;       
   end process;   

   -- FSM output logic --------------------------------------------------------
   outputlogicp : process(present_state,tx_done, UP_SOP_N, UP_SRC_RDY_N, ibtype_dec, reg_eop_n, limit, reg_bytecount,bm_turn, 
                                        reg_length_DW, first_len_odd, cnt_data, first_fragment_reg, reg_command, BM_REQ_R, UP_DATA, reg_length)
   begin

      dst_rdy_n       <= '0';
      tx_read         <= '0'; 
      data_write      <= '0'; 
      compl_rst       <= '0'; 
      first_rw        <= '0';
      first_transfer  <= '0';   
      last_transfer   <= '0';
      recount_bc      <= '0';
      recount_len     <= '0';            
      recount_addr    <= '0';      
      recount_first_len_odd <= '0';
      reg_align_en    <= '0';  
      cnt_tag_en      <= '0';
      cnt_data_rst    <= '0';
      ib_header0      <= '0';
      ib_header1      <= '0';
      tx_start        <= '0';
      first_fragment  <= '0';
      first_fragment_rst <= '0';
      switch_3HD_1st_odd <= '0';
      first_recount      <= '0';
      bm_req          <= '0';
      BM_ACK_R        <= '0';
      bm_result       <= '0';
      bm_result_rst   <= '0';
      data_op_done    <= '0';
      reg_history_en  <= '0';
      idle            <= '0';
 
      case (present_state) is   

         -- MAIN branch -------------------------------------------------------

         when  S_IDLE => 
                  cnt_data_rst  <= '1';
                  bm_result_rst <= '1';
                  idle          <= '1';

                  if (bm_turn = '1') then
                     reg_history_en <= '1';
                     ib_header0 <= '1';               
                     bm_req     <= '1';    
                     dst_rdy_n  <= '1';                                                  -- type = COMPLETION & BM result flag (tag[7])
                  elsif (UP_SOP_N = '0' and UP_SRC_RDY_N = '0' and UP_DATA(14 downto 12)=T_COMPL_WD and UP_DATA(23)='1') then       
                     reg_history_en <= '1';
                     tx_read    <= '1';
                     bm_result  <= '1';
                     bm_result_rst   <= '0';
                     dst_rdy_n  <= '1';
                  elsif (UP_SOP_N = '0' and UP_SRC_RDY_N = '0') then       
                     reg_history_en <= '1';
                     ib_header0 <= '1';
                  end if;

         when S_IDLE1 => 
                  dst_rdy_n  <= '1';

         when S_IDLE2 => 
                  if (UP_SOP_N = '0' and UP_SRC_RDY_N = '0') then       
                     ib_header0 <= '1';
                  end if;                           

         when  S_HEADER1 =>                            
                  if ((ibtype_dec = CMD_READ32 or ibtype_dec = CMD_READ64) and UP_SRC_RDY_N = '0') then                                         
                    ib_header1 <= '1'; 
                    first_rw <= '1'; 
                    recount_addr <= '1';                    
                  elsif ((ibtype_dec = CMD_WRITE32 or ibtype_dec = CMD_WRITE64) and UP_SRC_RDY_N = '0') then                                                          
                    ib_header1 <= '1';                                                                                           
                  elsif ((ibtype_dec = CMD_COMPL) and UP_SRC_RDY_N = '0') then                                                
                     tx_read <= '1';
                     ib_header1 <= '1';                                                                                          
                  end if;                                                                                                        
                                                                                                                                 
         -- READ branch -------------------------------------------------------                                                  

         when S_READ =>
                  recount_len <= '1'; 
                  first_rw <= '1'; 
                  recount_addr <= '1';                                    
                  cnt_tag_en <= '1';
                  dst_rdy_n    <= '1';
                  
         when S_READ_START =>                                                                                                                                                                                                                   
                  tx_start   <= '1';                                                                                             
                  dst_rdy_n  <= '1';
                                                                                                                                 
         when S_READ_DONE => 
                  dst_rdy_n  <= '1';

         -- BUS MASTER branch -------------------------------------------------
         when S_BM_H1 =>
                  ib_header1  <= '1'; 
                  first_rw     <= '1'; 
                  recount_addr <= '1';                    
                  bm_req      <= '1';
                  dst_rdy_n   <= '1';
                  
         when S_BM => 
                  cnt_tag_en   <= '1';
                  recount_len <= '1';        
                  first_rw <= '1'; 
                  recount_addr <= '1';                                    
                  bm_req       <= '1';                  
                  dst_rdy_n    <= '1';
         
         when S_BM_START => 
                  tx_start   <= '1'; 
                  bm_req     <= '1';
                  dst_rdy_n  <= '1';

         when S_BM_DONE => 
                  bm_req     <= '1';
                  dst_rdy_n  <= '1';
                  
                  if (tx_done = '1') then
                     BM_ACK_R <= '1';
                  end if;                           
                                                                                                                                                                  
         -- DATA RECEIVE branch -----------------------------------------------                                                  
                                      
         -- First fragment reception --                                      
         when S_DATA_RECEIVE1 =>                                                                                                                  
                  dst_rdy_n       <= '1';
                  reg_align_en <= '1';
                  first_rw <= '1'; 
                  recount_addr <= '1';
                                                                                                                                 
         when S_DATA_RECEIVE2 =>                                                                                                 
                  dst_rdy_n       <= '1';
                  recount_len <= '1';
                  first_recount      <= '1';
                  recount_first_len_odd <= '1';
                  
         when S_DATA_RECEIVE3 =>                                                                                                    
                  if (UP_SRC_RDY_N = '0') then                                                                                     
                     data_write <= '1';                                                                                               
                  end if;                                                                                                               

                  if (UP_SRC_RDY_N = '0' and cnt_data=conv_std_logic_vector(0, 10)) then
                     first_transfer <= '1';                     
                  end if;

                  if ((cnt_data(8 downto 0) = limit)) then 
                     last_transfer <= '1';
                  end if;                                

                  first_fragment <= '1';

         -- Next fragment reception --
         when S_DATA_RECEIVE_NEXT_FRAGMENTS =>
                  if (UP_SRC_RDY_N = '0' and reg_eop_n = '1') then            
                     data_write <= '1';                                                                                               
                  end if;                                                                                                               

                  if (reg_eop_n = '0') then
                     dst_rdy_n       <= '1';
                  end if;         

                  if (reg_eop_n = '1' and UP_SRC_RDY_N = '0' and cnt_data=conv_std_logic_vector(0, 10)) then
                     first_transfer <= '1';                     
                  end if;                                    

         -- Supplemental load from ib_up_data_reg --
         when S_LOAD_FROM_REG =>
                  dst_rdy_n       <= '1';
              
                  --   1st fragment length = even        &       3 header transaction
                  if (first_len_odd = '0' and (reg_command = CMD_WRITE32 or reg_command = CMD_COMPL) and reg_length_DW(0) = '0') then
                     data_write <= '1';
                  end if;         

         -- DATA TRANSMIT branch ----------------------------------------------

         when S_TRANSMIT_START =>
                  dst_rdy_n <= '1';
                  tx_start  <= '1';       

                  cnt_data_rst <= '1';
                  
         when S_TRANSMIT_DONE =>
                  dst_rdy_n       <= '1';
                  
                  if (tx_done = '1') then
                     compl_rst <= '1';
                     
                     if (reg_bytecount = reg_length) then
                        data_op_done    <= '1';
                     end if;
                  end if;                  

         when S_RECOUNT1 =>
                  dst_rdy_n       <= '1';
                  recount_addr <= '1';                        
                  recount_bc   <= '1';                        

                  cnt_data_rst <= '1';
                  first_fragment_rst <= '1';

         when S_RECOUNT2 =>
                  dst_rdy_n       <= '1';
                  recount_len  <= '1';                                          

                  --  1st fragment length = odd        &          3 header transaction
                  if (first_len_odd = '1' and (reg_command = CMD_WRITE32 or reg_command = CMD_COMPL)) then
                     data_write <= '1';
                     switch_3HD_1st_odd <= '1';
                  end if;                  
                                 
      end case;       
   end process;  

   UP_DST_RDY_N <= dst_rdy_n;

   -- ADITIONAL logic ---------------------------------------------------------
   -- End of packet (EOP_N) mark --
   reg_eop_np: process(RESET, CLK, UP_SOP_N, DST_RDY_N, UP_SRC_RDY_N)
   begin
     if (RESET = '1' or (UP_SOP_N = '0' and DST_RDY_N = '0' and UP_SRC_RDY_N = '0')) then
        reg_eop_n <= '1';
     elsif (CLK'event AND CLK = '1') then
        if (UP_EOP_N = '0' and DST_RDY_N = '0' and UP_SRC_RDY_N = '0') then
           reg_eop_n <= '0';
        end if;
     end if;
   end process;         

   -- CNT_DATA limit for packet reception --   
--   sub_limitp: process(reg_length_DW)
--   begin
--      sub_limit <= reg_length_DW - "0000000001";
--   end process;   
   
   limit <= reg_length_DW(9 downto 1) when reg_length_DW(0) = '1' else  
            reg_length_DW(9 downto 1) when first_len_odd = '1' and reg_command_hdr3 = '1' and first_fragment = '0' else
            reg_length_DW_minus1(9 downto 1); --sub_limit(9 downto 1);                

   -- IB_HEADER1_DLY auxiliary delay register --
   ib_header1_dlyp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        ib_header1_dly <= ib_header1;
     end if;
   end process;            

   -- First fragment length mark --
   first_len_oddp: process(RESET, CLK, present_state)
   begin
     if (RESET = '1' or present_state = S_IDLE) then
        first_len_odd <= '0';
     elsif (CLK'event AND CLK = '1') then
        if (recount_first_len_odd = '1') then
           first_len_odd <= reg_length_DW_aux(2);
        end if;
     end if;
   end process;               

   -- First fragment indication mark --
   first_fragment_regp: process(RESET, CLK, first_fragment_rst)
   begin
     if (RESET = '1' or first_fragment_rst = '1') then
        first_fragment_reg <= '0';
     elsif (CLK'event AND CLK = '1') then
        if (first_fragment = '1') then
           first_fragment_reg <= first_fragment;
        end if;
     end if;
   end process;         
      
   -- -------------------------------------------------------------------------   
   --                             HEADER BUFFER                              --
   -- -------------------------------------------------------------------------   

   -- -------------------------------------------------------------------------
   -- Registers for storing information from IB packet header/BM ifc ----------

   -- Transaction Type ------------------------------------
   reg_ibtype_mpx <= T_G2LR when bm_req = '1' else          -- READ trans. initiated via BM ifc
                     T_L2GW when bm_result_reg = '1' else   -- BM result completion -> WRITE trans.
                     UP_DATA(14 downto 12);              -- common trans.
   
   reg_ibtypep: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (ib_header0 = '1') then
           reg_ibtype <= reg_ibtype_mpx;
        end if;
     end if;
   end process;      
   
   -- Transaction Tag -------------------------------------
   reg_ibtag_mpx <= BM_TAG when bm_req = '1' else
                    UP_DATA(31 downto 16);
   
   reg_ibtagp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (ib_header0 = '1') then
           reg_ibtag <= reg_ibtag_mpx;
        end if;
     end if;
   end process;      

   -- Primar Address (32-b Local Dst/Src or 64-b Global Dst/Src) --
   reg_ibaddr_primar_l_mpx <= BM_GLOBAL_ADDR(31 downto 0) when bm_req = '1' else
                              reg_bmaddr(31 downto 0) when bm_result_reg = '1' else
                              UP_DATA(63 downto 32);
   
   reg_ibaddr_primar_lp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (ib_header0 = '1') then
           reg_ibaddr_primar_l <= reg_ibaddr_primar_l_mpx;
        end if;
     end if;
   end process;         

   reg_ibaddr_primar_h_mpx <= BM_GLOBAL_ADDR(63 downto 32) when bm_req = '1' else
                              reg_bmaddr(63 downto 32) when bm_result_reg = '1' else   
                              UP_DATA(63 downto 32);   

   reg_ibaddr_primar_hp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (ib_header1 = '1') then
           reg_ibaddr_primar_h <= reg_ibaddr_primar_h_mpx;
        end if;
     end if;
   end process;   

   reg_ibaddr_primar <= reg_ibaddr_primar_h&reg_ibaddr_primar_l;

   -- Secundar Address (32-b Local Dst/Src) ---------------
   reg_ibaddr_secundar_mpx <= BM_LOCAL_ADDR when bm_req = '1' else
                              UP_DATA(31 downto 0);
   
   reg_ibaddr_secundarp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (ib_header1 = '1') then
           reg_ibaddr_secundar <= reg_ibaddr_secundar_mpx;
        end if;
     end if;
   end process;            
  
   -- -------------------------------------------------------------------------  
   -- IB type -> Command LOGIC + REGISTER -------------------------------------
   
   ibtype_decp: process(reg_ibtype, reg_ibaddr_primar_h)
   begin
     if (reg_ibtype = T_COMPL_WD) then
        ibtype_dec <= CMD_COMPL;                      -- Completion
        
     elsif (reg_ibtype = T_L2GW) then                 -- Write
        if (reg_ibaddr_primar_h = X"00000000") then
           ibtype_dec <= CMD_WRITE32;                       -- 32-bit Write
        else
           ibtype_dec <= CMD_WRITE64;                       -- 64-bit Write
        end if;

     elsif (reg_ibtype = T_G2LR) then                 -- Read
        if (reg_ibaddr_primar_h = X"00000000") then
           ibtype_dec <= CMD_READ32;                        -- 32-bit Read
        else
           ibtype_dec <= CMD_READ64;                        -- 64-bit Read
        end if;        

     else
        ibtype_dec <= (others => '0');     
     end if;
   end process;            

   hdr3_dec <= '1' when (ibtype_dec = CMD_WRITE32 or ibtype_dec = CMD_COMPL) else
               '0';

   reg_commandp: process(RESET, CLK)
   begin
     if (CLK'event AND CLK = '1') then
        reg_command      <= ibtype_dec;
        reg_command_hdr3 <= hdr3_dec;  
     end if;
   end process;                  

   -- -------------------------------------------------------------------------
   -- Requester ID, Traffic Class, Attributes LOGIC + REGISTERS ---------------
   
   reg_reqidp: process(CLK, reg_command)
   begin
     if (reg_command /= CMD_COMPL) then
        reg_reqid <= (others => '0');
        reg_tc    <= (others => '0');
        reg_attr  <= (others => '0');
     elsif (CLK'event AND CLK = '1') then
        if (TXVLD = '1') then
           reg_reqid <= TXBUS_NUM&TXDEVICE_NUM&TXFUNC_NUM;
           reg_tc    <= TXTC;
           reg_attr  <= TXATTR;
        end if;
     end if;
   end process;               

   -- -------------------------------------------------------------------------
   -- Transaction Tag LOGIC + REGISTER ----------------------------------------
   
   mpx_tag <= bm_req&ZERO_TAG_BM&cnt_tag when cnt_tag_en = '1' else
              "10000000" when bm_result = '1' else
              TXTAG;             

   reg_tagp: process(CLK, bm_result_rst)
   begin
     if (bm_result_rst = '1') then
        reg_tag <= (others => '0');
     elsif (CLK'event AND CLK = '1') then
        if (cnt_tag_en = '1' or (TXVLD = '1' and bm_result_reg='0') or bm_result = '1') then
           reg_tag <= mpx_tag;
        end if;
     end if;
   end process;               

   -- -------------------------------------------------------------------------
   -- Completion Byte Count LOGIC + REGISTER ----------------------------------
   sub_bytecountp: process(reg_bytecount, reg_length)
   begin
      sub_bytecount <= reg_bytecount - reg_length;
   end process;   
       
   mpx_bytecount <= '0'&BM_LENGTH when bm_req = '1' else
                    '0'&UP_DATA(11 downto 0) when ib_header0 = '1' else
                    sub_bytecount;

   bytecount_aux <= '1'&X"000" when mpx_bytecount = 0 else
                    mpx_bytecount;
   
   reg_bytecountp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (ib_header0 = '1' or recount_bc = '1') then
           reg_bytecount <= bytecount_aux;
        end if;
     end if;
   end process;                  

   -- -------------------------------------------------------------------------
   -- Length LOGIC + REGISTER -------------------------------------------------

   -- Compare condition for LENGTH IN B determination --
   firstcomparep: process(mpx_minus(1 downto 0),REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN,
                          REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0, TLP_MAX_LEN_13_MINUS_2, TLP_MAX_LEN_13_MINUS_1)
   begin
      if (REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN = 0) then
      
         if ((REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0 = TLP_MAX_LEN_13_MINUS_2) and (mpx_minus(1 downto 0) = "11")) or
            ((REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0 = TLP_MAX_LEN_13_MINUS_1) and (mpx_minus(1 downto 0) = "10")) or
            ((REG_BYTECOUNT_LOG2_TLP_MAX_LEN_MINUS_1_DOWNTO_0 = TLP_MAX_LEN_13_MINUS_1) and (mpx_minus(1 downto 0) = "11")) then
               do_firstparse <= '1';
         else
               do_firstparse <= '0';
         end if;
         
      else
         do_firstparse <= '1';
      end if;
   end process;

   reg_do_firstparsep: process(RESET, CLK)
   begin
     if (RESET = '1') then
        reg_do_firstparse <= '0';
     elsif (CLK'event AND CLK = '1') then
        if (reg_align_en = '1') then
           reg_do_firstparse <= do_firstparse;
        end if;
     end if;
   end process;           
  
   compare_condition <= not reg_do_firstparse when first_recount = '1' else
                        '1' when (REG_BYTECOUNT_12_DOWNTO_LOG2_TLP_MAX_LEN = 0) else
                        '0';
                        
                          
   -- LENGTH IN B --
   mpx_rlen   <=  reg_bytecount when (ibtype_dec = CMD_READ32 or ibtype_dec = CMD_READ64) else
                  reg_align;
   
   mpx_length <=  reg_bytecount when compare_condition = '1' else
                  mpx_rlen;
                    
   reg_lengthp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (recount_len = '1') then
           reg_length <= mpx_length;
        end if;
     end if;
   end process;                           

   -- LENGTH IN DW --
   reg_length_DW_auxp: process(mpx_length, mpx_address(1 downto 0))
   begin
      reg_length_DW_aux <= mpx_length + (X"00"&"00"&mpx_address(1 downto 0))  + X"003";
   end process;      

   reg_length_DW_minus1_auxp: process(mpx_length, mpx_address(1 downto 0))
   begin
      reg_length_DW_minus1_aux <= mpx_length + (X"00"&"00"&mpx_address(1 downto 0))  + X"002";
   end process;         

   reg_length_DWp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (recount_len = '1') then
           reg_length_DW <= reg_length_DW_aux(12 downto 2);
        end if;
     end if;
   end process;                              

   reg_length_DW_minus1p: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (recount_len = '1') then
           reg_length_DW_minus1 <= reg_length_DW_minus1_aux(12 downto 2);
        end if;
     end if;
   end process;                                 

   -- -------------------------------------------------------------------------
   -- Global Address / lower bits LOGIC + REGISTER ----------------------------

   -- Lower bits LOGIC ------------------------------------
   reg_lowerbitsp: process(CLK, compl_rst)
   begin
     if (compl_rst = '1') then
        reg_lowerbits <= (others => '0');
     elsif (CLK'event AND CLK = '1') then
        if (ib_header1_dly = '1') then
           reg_lowerbits <= reg_ibaddr_secundar(6 downto 0);
        end if;
     end if;
   end process;                                    

   -- Global Address LOGIC --------------------------------
   mpx_A <=  reg_ibaddr_primar when first_rw = '1' else
             reg_globaddr;                  

   mpx_B <=  X"0000000000000000" when first_rw = '1' else
             X"000000000000"&"000"&reg_length;         

   add_addrp: process(mpx_A(11 downto 0), mpx_B(11 downto 0))
   begin
      add_addr <= mpx_A(11 downto 0) + mpx_B(11 downto 0);
   end process;   

   reg_globaddrp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (recount_addr = '1') then
           reg_globaddr <= mpx_A(63 downto 12)&add_addr;
        end if;
     end if;
   end process;                           
   
   -- Output MULTIPLEXOR => TX_ADDR -----------------------
   mpx_address <=  X"00000000000000"&"0"&reg_lowerbits when reg_command = CMD_COMPL else
                   reg_globaddr;               

   -- -------------------------------------------------------------------------
   -- auxiliary register for alignment purposes -------------------------------      
  
   mpx_minus <=  reg_ibaddr_secundar(6 downto 0) when reg_command = CMD_COMPL else
                 reg_ibaddr_primar(6 downto 0); --"0000000";               

   mpx_minus_aux <= "000000"&mpx_minus;
   sub_alignp: process(TLP_MAX_LEN_13,mpx_minus_aux)
   begin
      sub_align <= TLP_MAX_LEN_13 - mpx_minus_aux;   
   end process;                                                                          

   reg_alignp: process(CLK, recount_len_dly, TLP_MAX_LEN_13)
   begin
     if (recount_len_dly = '1') then
        reg_align <= TLP_MAX_LEN_13;
     elsif (CLK'event AND CLK = '1') then
        if (reg_align_en = '1') then
           reg_align <= sub_align;
        end if;
     end if;
   end process;        

   -- delay register for reg_align reset
   recount_len_dlyp: process(RESET, CLK)
   begin
     if (RESET = '1') then
        recount_len_dly <= '0';
     elsif (CLK'event AND CLK = '1') then
        recount_len_dly <= recount_len;
     end if;
   end process;           
     
   -- -------------------------------------------------------------------------   
   --                              DATA BUFFER                               --
   -- -------------------------------------------------------------------------      

   -- data buffer -------------------------------------------------------------
   U_data_buf: entity work.DP_BMEM  
      generic map(
         DATA_WIDTH => 64,
         ITEMS      => 1024,     
         BRAM_TYPE  => 36, 
         OUTPUT_REG => false,
         DEBUG      => false     
      )
      port map(
         RESET      => RESET,

         -- write port
         CLKA       => CLK,
         PIPE_ENA   => '1',
         REA        => '0',
         WEA        => data_write,  
         ADDRA      => cnt_data,
         DIA        => mpx_ib_up_data,
         DOA_DV     => open,
         DOA        => open,
                                                         
         -- read port                                    
         CLKB       => CLK,                              
         PIPE_ENB   => '1',                              
         REB        => data_read,                             
         WEB        => '0',       
         ADDRB      => cnt_data,
         DIB        => X"0000000000000000",
         DOB_DV     => data_payload_vld, 
         DOB        => data_payload
      );      

   data_read <= tx_dwrd0 or tx_dwrd1;

   -- data buffer address counter ---------------------------------------------
   cnt_datap: process(CLK, RESET, cnt_data_rst)
   begin
      if (RESET = '1' or cnt_data_rst = '1') then
         cnt_data_aux <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if ((data_write = '1') or (data_read = '1')) then
            cnt_data_aux <= cnt_data_aux + 1;
         end if;
      end if;
   end process;
   
   cnt_data <= cnt_data_aux;        
   
   -- Data alignment logic for packet RECEPTION -------------------------------   
   -- IB UP DATA HIGH (63:32) register -- 
   ib_up_data_dlyp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (data_write = '1') then
           ib_up_data_dly <= UP_DATA(63 downto 32);
        end if;
     end if;
   end process;           

   -- multiplexor system for data alignment --
   ib_up_data_switch <= '0' when ( reg_command = CMD_WRITE64) else                                                                             -- 4 headers   
                                                                                      
                        '1' when ((reg_command = CMD_COMPL or reg_command = CMD_WRITE32) and first_len_odd = '0') or                            -- 3 headers, 1st length even
                                 ((reg_command = CMD_COMPL or reg_command = CMD_WRITE32) and first_len_odd = '1' and first_fragment = '1') else -- 3 headers, 1st length odd
                        '0';

   mpx_ib_up_data_high <= UP_DATA(31 downto 0) when ib_up_data_switch = '0' else
                          ib_up_data_dly;

   mpx_ib_up_data_low  <= UP_DATA(63 downto 32) when ib_up_data_switch = '0' else
                          UP_DATA(31 downto  0);                        

   mpx_3HD_1st_odd     <= mpx_ib_up_data_low when switch_3HD_1st_odd = '0' else
                          ib_up_data_dly;

   mpx_ib_up_data      <= mpx_ib_up_data_high&mpx_3HD_1st_odd;                  


   -- Data alignment logic for packet TRANSMITION -----------------------------
   tx_datadw1_aligned   <= data_payload(63 downto 32) when reg_command /= CMD_WRITE64 else
                           data_payload(31 downto  0);
 
   tx_datadw0_aligned   <= data_payload(31 downto  0) when reg_command /= CMD_WRITE64 else
                           data_payload(63 downto 32);   
 
   -- -------------------------------------------------------------------------
   --                      BUS MASTER RESULT PROCESSING                      --
   -- ------------------------------------------------------------------------- 
 
   -- BM result flag --
   bm_result_regp: process(RESET, CLK, bm_result_rst)
   begin
     if (RESET = '1' or bm_result_rst = '1') then
        bm_result_reg <= '0';
     elsif (CLK'event AND CLK = '1') then
        if (bm_result = '1') then
           bm_result_reg <= '1';
        end if;
     end if;
   end process;            

   -- Global address for WRITE (~ completion with bm result flag) --
   reg_bmaddrp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (TXVLD = '1') then
           reg_bmaddr <= TXBMADDR;
        end if;
     end if;
   end process;

   -- 'Operation Done' + full flags --
   reg_bmtagp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (ib_header0 = '1') then
           reg_bmtag <= UP_DATA(43 downto 36)&UP_DATA(31 downto 24);
        end if;
     end if;
   end process;
   
   BM_OP_TAG_W  <= reg_bmtag;
   
   BM_OP_DONE_W <= data_op_done and bm_result_reg;

   BM_FULL_R    <= TXFULL;
 
   -- BM request vs. IB request resolution logic --
   bm_turn_sel <= reg_history&(not UP_SOP_N and not UP_SRC_RDY_N)&BM_REQ_R;

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

   reg_historyp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (reg_history_en = '1') then
           reg_history <= bm_turn;
        end if;
     end if;
   end process;     
 
   -- -------------------------------------------------------------------------
   --                      COMPLETION BUFFER INTERFACE                       --
   -- -------------------------------------------------------------------------   
                                                                                  
   -- 'Global Read' Tag counter --                                                
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
                                                                                        
   -- Output signals assigment --
   
   TXRTAG   <= UP_DATA(16 + LTAG_WIDTH-1 downto 16) when bm_result = '1' else
               reg_ibtag(LTAG_WIDTH-1 downto 0);
   
   TXRD     <= tx_read;
   
   TXWE     <= cnt_tag_en;
   TXWTAG   <= cnt_tag;
   TXGRADDR <= reg_ibaddr_secundar;
   TXGRTAG  <= reg_ibtag;
                   
   -- -------------------------------------------------------------------------
   --                            TLP GENERATOR                               --
   -- -------------------------------------------------------------------------

   -- TLP generator ---------------------------------------
   U_TLPGEN : entity work.TLP_GEN
   port map(
      -- Common interface
      CLK              => CLK,
      RSTN             => rstn,
      -- TLP TX interface 
      TLPTXDATA        => TLPTX_DATA,          
      TLPTXDWE         => TLPTX_DWE ,          
      TLPTXREQ         => TLPTX_REQ,          
      TLPTXDISCARD     => open,                
      TLPTXACK         => TLPTX_ACK ,         
      TLPTXWAIT        => TLPTX_WAIT,         
      TLPTXFMTERR      => '0',
      -- Application interface
      TXSTART          => tx_start,
      TXCOMMAND        => tx_command,
      TXSRCDEVID       => tx_srcdevid,
      TXDSTDEVID       => tx_dstdevid,
      TXTC             => tx_tc,
      TXTAG            => tx_tag,
      TXRELAXORDERATTR => reg_attr(1),
      TXNOSNOOPATTR    => reg_attr(0),
      TXADDRESS        => tx_address,
      TXLENGTH         => tx_length,
      TXDWENA1ST       => tx_dwenafirst,
      TXDWENALAST      => tx_dwenalast,
      TXCPLSTATUS      => "000",
      TXCPLBCOUNT      => tx_bytecount,
      TXDATADW0        => tx_datadw0,
      TXDATADW1        => tx_datadw1,
      TXREADY          => tx_ready,
      TXDONE           => tx_done,
      TXDWRD0          => tx_dwrd0,
      TXDWRD1          => tx_dwrd1     
   );   

   rstn <= not RESET;    

   tx_command   <= reg_command;
   tx_srcdevid  <= BUS_NUM&DEVICE_NUM&FUNC_NUM;
   tx_dstdevid  <= reg_reqid;  
   tx_tag       <= reg_tag;                   
   tx_address   <= mpx_address;                    
   tx_length    <= reg_length_DW;
   tx_tc        <= reg_tc;   
   
   tx_bytecount <= reg_bytecount;      
   
   tx_datadw1   <= tx_datadw1_aligned;                      
   tx_datadw0   <= tx_datadw0_aligned;
   
   -- byte enables ----------------------------------------
   firstbe_sel <= tx_address(1 downto 0)&reg_length(1 downto 0);
   
   firstbep: process(firstbe_sel,tx_address(1 downto 0),reg_length_DW) 
   begin
      if (reg_length_DW = "0000000001") then
         case firstbe_sel is
            when "0000" => tx_dwenafirst <= "1111";
            when "0001" => tx_dwenafirst <= "0001";
            when "0010" => tx_dwenafirst <= "0011";
            when "0011" => tx_dwenafirst <= "0111";

            when "0101" => tx_dwenafirst <= "0010";
            when "0110" => tx_dwenafirst <= "0110";
            when "0111" => tx_dwenafirst <= "1110";            

            when "1001" => tx_dwenafirst <= "0100";
            when "1010" => tx_dwenafirst <= "1100";            
            
            when "1101" => tx_dwenafirst <= "1000";
            when others => tx_dwenafirst <= "1111";
         end case;
      else   
         case tx_address(1 downto 0) is
            when "00" => tx_dwenafirst <= "1111";
            when "01" => tx_dwenafirst <= "1110";
            when "10" => tx_dwenafirst <= "1100";
            when "11" => tx_dwenafirst <= "1000";
            when others => tx_dwenafirst <= "1111";
         end case;
      end if;
   end process;   
 
   be_resultp: process(tx_address(1 downto 0),reg_length(1 downto 0))
   begin
      be_result <= tx_address(1 downto 0)+reg_length(1 downto 0);
   end process;   
 
   lastbep: process(be_result, reg_length_DW) 
   begin
      if (reg_length_DW = "0000000001") then
         tx_dwenalast <= "0000";
      else
         case be_result is
            when "00" => tx_dwenalast <= "1111";
            when "01" => tx_dwenalast <= "0001";
            when "10" => tx_dwenalast <= "0011";
            when "11" => tx_dwenalast <= "0111";
            when others => tx_dwenalast <= "1111";
         end case;
      end if;
   end process;   

   -- -------------------------------------------------------------------------
   --                           DATA ALIGNMENT BLOCK                         --
   -- -------------------------------------------------------------------------

--   U_TX_BUF_ALIGN : entity work.TX_BUF_ALIGN
--   port map(
--      CLK              => CLK, 
--      RESET            => RESET,

--      IB_IN_DATA       => IB_UP_DATA,
--      IB_IN_SOP_N      => IB_UP_SOP_N,     
--      IB_IN_EOP_N      => IB_UP_EOP_N,     
--      IB_IN_SRC_RDY_N  => IB_UP_SRC_RDY_N, 
--      IB_IN_DST_RDY_N  => IB_UP_DST_RDY_N,  

--      END_OF_ALIGN     => end_of_align,
--      LOCK_READ        => TXFULL,

--      IB_OUT_DATA      => UP_DATA, 
--      IB_OUT_SOP_N     => UP_SOP_N,     
--      IB_OUT_EOP_N     => UP_EOP_N,     
--      IB_OUT_SRC_RDY_N => UP_SRC_RDY_N, 
--      IB_OUT_DST_RDY_N => UP_DST_RDY_N
--   );     
--
--   end_of_align <= '1' when last_transfer = '1' and reg_command = CMD_WRITE64 and 
--                            (not (reg_bytecount = reg_length)) else
--                   '0';
               
   -- -------------------------------------------------------------------------      

   UP_DATA         <= IB_UP_DATA;
   UP_SOP_N        <= IB_UP_SOP_N;   
   UP_EOP_N        <= IB_UP_EOP_N;   
   UP_SRC_RDY_N    <= IB_UP_SRC_RDY_N;

   IB_UP_DST_RDY_N <= UP_DST_RDY_N; 
  
end tx_buf_arch;



