--
-- pcie2ib_bridge_norec.vhd: PCIE2IB_BRIDGE VHDL wrapper without records
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

use work.ib_pkg.all; 
use work.pcie_pkg.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity PCIE2IB_BRIDGE_NOREC is 
   generic(
      IB_BASE_ADDR     : std_logic_vector(31 downto 0) := X"0F000000"; -- IB Base Address
      LTAG_WIDTH       : integer :=   5;                               -- 'Local Read' Buffer tag width (max. 7)
      GTAG_WIDTH       : integer :=   5;                               -- 'Global Read' Buffer tag width (max. 7)       
      BAR_HIT_MASK     : std_logic_vector( 6 downto 0) :=   "1111111"; -- Base Address Register hit mask
      -- BAR base addresses
      BAR0_BASE        : std_logic_vector(31 downto 0) := X"01000000"; -- BAR0 base address for PCIE->IB transalation
      BAR1_BASE        : std_logic_vector(31 downto 0) := X"02000000"; -- BAR1 base address for PCIE->IB transalation
      BAR2_BASE        : std_logic_vector(31 downto 0) := X"03000000"; -- BAR2 base address for PCIE->IB transalation
      BAR3_BASE        : std_logic_vector(31 downto 0) := X"04000000"; -- BAR3 base address for PCIE->IB transalation
      BAR4_BASE        : std_logic_vector(31 downto 0) := X"06000000"; -- BAR4 base address for PCIE->IB transalation
      BAR5_BASE        : std_logic_vector(31 downto 0) := X"08000000"; -- BAR5 base address for PCIE->IB transalation       
      BAR6_BASE        : std_logic_vector(31 downto 0) := X"0A000000"; -- ROM  base address for PCIE->IB transalation
      -- BAR base addresses masks
      BAR0_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR0 mask for PCIE->IB transalation
      BAR1_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR1 mask for PCIE->IB transalation
      BAR2_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR2 mask for PCIE->IB transalation
      BAR3_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR3 mask for PCIE->IB transalation
      BAR4_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR4 mask for PCIE->IB transalation
      BAR5_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR5 mask for PCIE->IB transalation       
      BAR6_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"  -- ROM  mask for PCIE->IB transalation               
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK              : in std_logic;  -- FPGA clock
      RESET            : in std_logic;  -- Reset active high
      
      -- PCI Express Transaction Layer interface ------------------------------
      -- RX link --
      PCIERX_SOF_N     : in std_logic;                      -- signals the start of a packet
      PCIERX_EOF_N     : in std_logic;                      -- signals the end of a packet
             
      PCIERX_DATA      : in std_logic_vector(63 downto 0);  -- packet data to be transmitted
      PCIERX_REM_N     : in std_logic_vector( 7 downto 0);  -- packet data validity (legal values: 00000000/00001111)
             
      PCIERX_SRC_RDY_N : in std_logic;                      -- source ready
      PCIERX_DST_RDY_N : out std_logic;                     -- destination ready 
                                                                                                                                         
      PCIERX_SRC_DSC_N : in std_logic;                      -- source discontinue, asserted when the physical link is going into reset.
      PCIERX_ERR_FWD_N : in std_logic;                      -- error forward, marks the packet in progress as error poisoned
      PCIERX_NP_OK_N   : out std_logic;                     -- Non-Posted OK, ready to accept a Non-Posted Request packet
                                                                                                                                         
      PCIERX_BAR_HIT_N : in std_logic_vector( 6 downto 0);  -- Indicates BAR(s) targeted by the current receive transaction      
                                                                                                                                         
      PCIERX_FC_PH_AV  : in std_logic_vector( 7 downto 0);  -- The number of Posted Header FC credits available to the remote link partner.
      PCIERX_FC_PD_AV  : in std_logic_vector(11 downto 0);  -- The number of Posted Data FC credits available to the remote link partner
      PCIERX_FC_NPH_AV : in std_logic_vector( 7 downto 0);  -- Number of Non-Posted Header FC credits available to the remote link partner
      PCIERX_FC_NPD_AV : in std_logic_vector(11 downto 0);  -- Number of Non-Posted Data FC credits available to the remote link partner

      -- TX link --
      PCIETX_SOF_N     : out std_logic;                     -- signals the start of a packet
      PCIETX_EOF_N     : out std_logic;                     -- signals the end of a packet
             
      PCIETX_DATA      : out std_logic_vector(63 downto 0); -- packet data to be transmitted
      PCIETX_REM_N     : out std_logic_vector( 7 downto 0); -- packet data validity (legal values: 00000000/00001111)
             
      PCIETX_SRC_RDY_N : out std_logic;                     -- source ready
      PCIETX_DST_RDY_N : in std_logic;                      -- destination ready 
                                                                                                                                                                 
      PCIETX_SRC_DSC_N : out std_logic;                     -- source discontinue, may be asserted any time starting on the first cycle after SOF to EOF, inclusive
      PCIETX_DST_DCS_N : in std_logic;                      -- destination discontinue: Asserted when the physical link is going into reset.
                                                                                                                                                                 
      PCIETX_BUF_AV    : in std_logic_vector( 2 downto 0);  -- Indicates transmit buffer availability in the core (0:Non-Posted,1:Posted,2:Completion)

      -- Internal Bus interface -----------------------------------------------
      -- DOWNSTREAM
      IB_DOWN_DATA        : out std_logic_vector(63 downto 0);
      IB_DOWN_SOP_N       : out std_logic;
      IB_DOWN_EOP_N       : out std_logic;
      IB_DOWN_SRC_RDY_N   : out std_logic;
      IB_DOWN_DST_RDY_N   : in  std_logic;
        -- UPSTREAM
      IB_UP_DATA          : in  std_logic_vector(63 downto 0);
      IB_UP_SOP_N         : in  std_logic;
      IB_UP_EOP_N         : in  std_logic;
      IB_UP_SRC_RDY_N     : in  std_logic;
      IB_UP_DST_RDY_N     : out std_logic;

      -- Bus Master interface -------------------------------------------------
      -- Master Interface Input
      BM_GLOBAL_ADDR   : in  std_logic_vector(63 downto 0);   -- Global Address 
      BM_LOCAL_ADDR    : in  std_logic_vector(31 downto 0);   -- Local Address
      BM_LENGTH        : in  std_logic_vector(11 downto 0);   -- Length
      BM_TAG           : in  std_logic_vector(15 downto 0);   -- Operation TAG
      BM_TRANS_TYPE    : in  std_logic_vector(1 downto 0);    -- Transaction type
      BM_REQ           : in  std_logic;                       -- Request
      BM_ACK           : out std_logic;                       -- Ack

      -- Master Output interface
      BM_OP_TAG        : out std_logic_vector(15 downto 0);   -- Operation TAG
      BM_OP_DONE       : out std_logic;                       -- Acknowledge

      -- Configuration interface ----------------------------------------------
      CFG_BUS_NUM          : in std_logic_vector( 7 downto 0); -- Bus number           
      CFG_DEVICE_NUM       : in std_logic_vector( 4 downto 0); -- Device number  
      CFG_FUNC_NUM         : in std_logic_vector( 2 downto 0); -- Function number            
      CFG_MAX_PAYLOAD_SIZE : in std_logic_vector( 2 downto 0)  -- Maximum Payload TLP Size
   );
end PCIE2IB_BRIDGE_NOREC;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of PCIE2IB_BRIDGE_NOREC is

   signal reset_pipe   : std_logic;
   signal PCIE         : t_pcie_trn;
   signal IB           : t_internal_bus64;
   signal BM           : t_ibbm_64;
   signal CFG          : t_pcie_bridge_config;
   signal bla : std_logic_vector(2 downto 0);

begin

-- ----------------------------------------------------------------------------
RESET_PIPE_P : process(RESET, CLK)
   begin
      if CLK'event and CLK = '1' then
         reset_pipe  <= RESET;
      end if;
end process;

-- -----------------------Portmaping of tested component-----------------------
PCIE2IB_BRIDGE_U: entity work.PCIE2IB_BRIDGE 
   generic map(
      IB_BASE_ADDR     => IB_BASE_ADDR,
      LTAG_WIDTH       => LTAG_WIDTH,
      GTAG_WIDTH       => GTAG_WIDTH,
      BAR_HIT_MASK     => BAR_HIT_MASK,
      BAR0_BASE        => BAR0_BASE,
      BAR1_BASE        => BAR1_BASE,
      BAR2_BASE        => BAR2_BASE,
      BAR3_BASE        => BAR3_BASE,
      BAR4_BASE        => BAR4_BASE,
      BAR5_BASE        => BAR5_BASE,
      BAR6_BASE        => BAR6_BASE,      
      BAR0_MASK        => BAR0_MASK,
      BAR1_MASK        => BAR1_MASK,
      BAR2_MASK        => BAR2_MASK,
      BAR3_MASK        => BAR3_MASK,
      BAR4_MASK        => BAR4_MASK,
      BAR5_MASK        => BAR5_MASK,
      BAR6_MASK        => BAR6_MASK      
   ) 
   port map (
      -- Common interface -----------------------------------------------------
      CLK              => CLK,
      RESET            => RESET,
      
      -- PCI Express Transaction Layer interface ------------------------------      
      PCIE             => PCIE,

      -- Internal Bus interface -----------------------------------------------
      IB               => IB,

      -- Bus Master interface -------------------------------------------------
      BM               => BM,

      -- Configuration interface ----------------------------------------------
      CFG              => CFG
      
   );

   -- PCI Express Transaction Layer interface
   -- RX link --
   PCIE.RX.SOF_N     <= PCIERX_SOF_N;
   PCIE.RX.EOF_N     <= PCIERX_EOF_N;
             
   PCIE.RX.DATA      <= PCIERX_DATA;
   PCIE.RX.REM_N     <= PCIERX_REM_N;
             
   PCIE.RX.SRC_RDY_N <= PCIERX_SRC_RDY_N;
   PCIERX_DST_RDY_N  <= PCIE.RX.DST_RDY_N;
                                                                                                                                         
   PCIE.RX.SRC_DSC_N <= PCIERX_SRC_DSC_N;
   PCIE.RX.ERR_FWD_N <= PCIERX_ERR_FWD_N;
   PCIERX_NP_OK_N    <= PCIE.RX.NP_OK_N;
                                                                                                                                         
   PCIE.RX.BAR_HIT_N <= PCIERX_BAR_HIT_N;
                                                                                                                                        
   PCIE.RX.FC_PH_AV  <= PCIERX_FC_PH_AV;
   PCIE.RX.FC_PD_AV  <= PCIERX_FC_PD_AV;
   PCIE.RX.FC_NPH_AV <= PCIERX_FC_NPH_AV;
   PCIE.RX.FC_NPD_AV <= PCIERX_FC_NPD_AV;

   -- TX link --
   PCIETX_SOF_N      <= PCIE.TX.SOF_N;
   PCIETX_EOF_N      <= PCIE.TX.EOF_N;
            
   PCIETX_DATA       <= PCIE.TX.DATA;
   PCIETX_REM_N      <= PCIE.TX.REM_N;
             
   PCIETX_SRC_RDY_N  <= PCIE.TX.SRC_RDY_N;
   PCIE.TX.DST_RDY_N <= PCIETX_DST_RDY_N;
                                                                                                                                                                 
   PCIETX_SRC_DSC_N  <= PCIE.TX.SRC_DSC_N;
   PCIE.TX.DST_DCS_N <= PCIETX_DST_DCS_N;
                                                                                                                                                                 
   PCIE.TX.BUF_AV    <= PCIETX_BUF_AV;

   -- Internal Bus Interface
   -- DOWNSTREAM
   IB_DOWN_DATA       <= IB.DOWN.DATA;
   IB_DOWN_SOP_N      <= IB.DOWN.SOP_N;
   IB_DOWN_EOP_N      <= IB.DOWN.EOP_N;
   IB_DOWN_SRC_RDY_N  <= IB.DOWN.SRC_RDY_N;
   IB.DOWN.DST_RDY_N  <= IB_DOWN_DST_RDY_N;

   -- UPSTREAM
   IB.UP.DATA         <= IB_UP_DATA;
   IB.UP.SOP_N        <= IB_UP_SOP_N;
   IB.UP.EOP_N        <= IB_UP_EOP_N;
   IB.UP.SRC_RDY_N    <= IB_UP_SRC_RDY_N;
   IB_UP_DST_RDY_N    <= IB.UP.DST_RDY_N;

   -- Master Interface Input
   BM.GLOBAL_ADDR     <= BM_GLOBAL_ADDR; 
   BM.LOCAL_ADDR      <= BM_LOCAL_ADDR; 
   BM.LENGTH          <= BM_LENGTH;
   BM.TAG             <= BM_TAG;
   BM.TRANS_TYPE      <= BM_TRANS_TYPE;
   BM.REQ             <= BM_REQ;
   BM_ACK             <= BM.ACK;

   -- Master Output interface
   BM_OP_TAG          <= BM.OP_TAG;
   BM_OP_DONE         <= BM.OP_DONE;

   -- PCIe Bridge configuration interface
   CFG.BUS_NUM          <= CFG_BUS_NUM;
   CFG.DEVICE_NUM       <= CFG_DEVICE_NUM;
   CFG.FUNC_NUM         <= CFG_FUNC_NUM;
   CFG.MAX_PAYLOAD_SIZE <= CFG_MAX_PAYLOAD_SIZE;

end architecture FULL;



