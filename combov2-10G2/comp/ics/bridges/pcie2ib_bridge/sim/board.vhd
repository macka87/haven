--
-- board.vhd : TEST entity (endpoint_block_plus + PCIe2IB Bridge + user app.)
-- Copyright (C) 2007 CESNET
-- Author(s): Tomas Malek  <tomalek@liberouter.org> 
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

use WORK.math_pack.all;
use WORK.bmem_func.all; 

-- ----------------------------------------------------------------------------
--                          ENTITY DECLARATION                               --
-- ----------------------------------------------------------------------------

entity BOARD is 
   generic (
      FAST_SIMULATION   : std_logic := '0' -- Don't assert when using the core in HW!!!
   );
   port (
      -- SYS Inteface
      SYS_CLK_P         : in std_logic;
      SYS_CLK_N         : in std_logic;
      SYS_RESET_N       : in std_logic;
      -- PCI-Express Interface
      PCI_EXP_RXN       : in  std_logic_vector((4 - 1) downto 0);
      PCI_EXP_RXP       : in  std_logic_vector((4 - 1) downto 0);
      PCI_EXP_TXN       : out std_logic_vector((4 - 1) downto 0);
      PCI_EXP_TXP       : out std_logic_vector((4 - 1) downto 0)
   ); 
end BOARD;

-- ----------------------------------------------------------------------------
--                        ARCHITECTURE DECLARATION                           --
-- ----------------------------------------------------------------------------

architecture board_test_arch of BOARD is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal ib     : t_internal_bus64;
   signal ib_wr  : t_ibmi_write64;
   signal ib_rd  : t_ibmi_read64s;
   signal bm     : t_ibbm_64; 
   signal ibbm   : t_ibbm_64; 

   signal ib_clk : std_logic;
   signal ib_rst : std_logic;

   signal reg_bm_type    : std_logic;
   signal reg_bm_ifc_type: std_logic;
   signal reg_bm_length  : std_logic_vector(11 downto 0);
   signal reg_bm_req     : std_logic;
   signal cnt_bm_tag     : std_logic_vector(15 downto 0);
   signal cnt_bm_tag_aux : std_logic_vector(15 downto 0);   
   signal bm_decoded     : std_logic;
   signal bm_decoded_dly : std_logic;
   signal reg_bm_laddr   : std_logic_vector(31 downto 0);   
   signal reg_bm_gaddr   : std_logic_vector(63 downto 0);      
   signal ib_wr_data     : std_logic_vector(31 downto 0);   
   signal reg_bm_hd      : std_logic;
     
begin

   -- -------------------------------------------------------------------------
   --                         PCIE to IB TOP LEVEL                           --
   -- ------------------------------------------------------------------------- 

   PCIE2IB_TOP_U: entity work.PCIE2IB_TOP
   generic map(
      -- PCIe endpoint block plus generic interface ---------------------------
      FAST_TRAIN_SIMULATION_ONLY => FAST_SIMULATION,
      -- PCIe to IB bridge generic interface ----------------------------------
      IB_BASE_ADDR               => X"FF000000",
      LTAG_WIDTH                 => 5,         
      GTAG_WIDTH                 => 5,         
      BAR_HIT_MASK               => "1111111", 
      -- BAR base addresses
      BAR0_BASE                  => X"00000000",
      BAR1_BASE                  => X"00000000",
      BAR2_BASE                  => X"00000000",
      BAR3_BASE                  => X"00000000",
      BAR4_BASE                  => X"00000000",
      BAR5_BASE                  => X"00000000",
      BAR6_BASE                  => X"00000000",
      -- BAR base addresses masks
      BAR0_MASK                  => X"00FFFFFF",
      BAR1_MASK                  => X"00FFFFFF",
      BAR2_MASK                  => X"00FFFFFF",
      BAR3_MASK                  => X"00FFFFFF",
      BAR4_MASK                  => X"00FFFFFF",
      BAR5_MASK                  => X"00FFFFFF",
      BAR6_MASK                  => X"00FFFFFF"
   )
   port MAP (
      -- PCI Express interface ------------------------------------------------
      PCIE_RST_N                 => SYS_RESET_N,  
      PCIE_CLK                   => SYS_CLK_P,  
                                    
      PCI_EXP_RXN                => PCI_EXP_RXN,
      PCI_EXP_RXP                => PCI_EXP_RXP,
      PCI_EXP_TXN                => PCI_EXP_TXN,
      PCI_EXP_TXP                => PCI_EXP_TXP,
      
      -- Internal Bus interface -----------------------------------------------
      IB_RST                     => ib_rst,
      IB_CLK                     => ib_clk,
                                 
      IB                         => ib,
      BM                         => ibbm
   );                            
                                 
   -- ------------------------------------------------------------------------
   --                         INTERNAL BUS endpoint
   -- ------------------------------------------------------------------------

   IB_ENDPOINT_MASTER_I: entity work.IB_ENDPOINT_MASTER
   generic map(
      LIMIT               => conv_std_logic_vector(65536, 32),
      INPUT_BUFFER_SIZE   => 0,
      OUTPUT_BUFFER_SIZE  => 0,
      READ_REORDER_BUFFER => true,
      STRICT_EN           => false
   )
   port map(
      -- Common Interface
      IB_CLK        => ib_clk,
      IB_RESET      => ib_rst,
      -- Internal Bus Interface
      INTERNAL_BUS  => ib,
      -- User Component Interface 
      WR            => ib_wr,
      RD            => ib_rd,
      -- Busmaster
      BM            => bm      
   );  
  
   -----------------------------------------------------------------------------
   -- 64-bit MEMORY (DP_BMEM)
   -----------------------------------------------------------------------------

   U_test_mem: entity work.IBMI64MEM
      generic map(
         SIZE          => 65536,
         BRAM_DISTMEM  => 0
      )
      port map(
         -- Common Interface
         CLK           => ib_clk,
         RESET         => ib_rst,
         -- IBMI64 Interface
         IBMI_WRITE64  => ib_wr,
         IBMI_READ64   => ib_rd
   );

   -----------------------------------------------------------------------------
   -- BUS MASTER INTERFACE
   -----------------------------------------------------------------------------   
   bm.GLOBAL_ADDR <= reg_bm_gaddr;
   bm.LOCAL_ADDR  <= reg_bm_laddr;
   bm.LENGTH      <= reg_bm_length;
   bm.TRANS_TYPE  <= "0"&reg_bm_type;
   bm.TAG         <= cnt_bm_tag;
   bm.REQ         <= reg_bm_req and (not reg_bm_ifc_type);

   ibbm.GLOBAL_ADDR <= reg_bm_gaddr;
   ibbm.LOCAL_ADDR  <= reg_bm_laddr;
   ibbm.LENGTH      <= reg_bm_length;
   ibbm.TRANS_TYPE  <= "0"&reg_bm_type;
   ibbm.TAG         <= cnt_bm_tag;
   ibbm.REQ         <= reg_bm_req and reg_bm_ifc_type;   

   -- address decoder ---------------------------------------------------------
   bm_decoded     <= '1' when ib_wr.sof = '1' and ib_wr.addr(15) = '1' else
                     '0';

   bm_decoded_dlyp: process(ib_rst, ib_clk)
   begin
     if (ib_rst = '1') then
        bm_decoded_dly <= '0';
     elsif (ib_clk'event AND ib_clk = '1') then
        bm_decoded_dly <= bm_decoded;
     end if;
   end process;       

   -- BM.REQ register ---------------------------------------------------------
   reg_bm_reqp: process(ib_rst, ib_clk, bm.ACK, ibbm.ACK)
   begin
     if (ib_rst = '1' or bm.ACK = '1' or ibbm.ACK = '1') then
        reg_bm_req <= '0';
     elsif (ib_clk'event AND ib_clk = '1') then
        if (bm_decoded_dly = '1') then
           reg_bm_req <= '1';
        end if;
     end if;
   end process;       

   -- GLOBAL ADDRESS register --------------------------------------------------
   reg_bm_gaddrp: process(ib_rst, ib_clk)
   begin
     if (ib_rst = '1') then
        reg_bm_gaddr <= (others => '0');
     elsif (ib_clk'event AND ib_clk = '1') then
        if (bm_decoded = '1') then
           reg_bm_gaddr <= ib_wr.data;
        end if;
     end if;
   end process;      

   -- LOCAL ADDRESS register --------------------------------------------------
   reg_bm_laddrp: process(ib_rst, ib_clk)
   begin
     if (ib_rst = '1') then
        reg_bm_laddr <= (others => '0');
     elsif (ib_clk'event AND ib_clk = '1') then
        if (bm_decoded_dly = '1') then
           reg_bm_laddr <= X"0000"&ib_wr.data(15 downto 0);
        end if;
     end if;
   end process;      

   -- LENGTH register ---------------------------------------------------------
   reg_bm_lengthp: process(ib_rst, ib_clk)
   begin
     if (ib_rst = '1') then
        reg_bm_length <= (others => '0');
     elsif (ib_clk'event AND ib_clk = '1') then
        if (bm_decoded_dly = '1') then
           reg_bm_length <= ib_wr.data(27 downto 16);
        end if;
     end if;
   end process;      

   -- TRANSACTION TYPE register (R=0/W=1) -------------------------------------
   reg_bm_typep: process(ib_rst, ib_clk)
   begin
     if (ib_rst = '1') then
        reg_bm_type <= '0';
     elsif (ib_clk'event AND ib_clk = '1') then
        if (bm_decoded_dly = '1') then
           reg_bm_type <= ib_wr.data(28);
        end if;
     end if;
   end process;         

   -- BM IFC TYPE (0=endpoint_BM_ifc / 1=pcie2ib_bridge_BM_ifc) ---------------
   reg_bm_ifc_typep: process(ib_rst, ib_clk)
   begin
     if (ib_rst = '1') then
        reg_bm_ifc_type <= '0';
     elsif (ib_clk'event AND ib_clk = '1') then
        if (bm_decoded_dly = '1') then
           reg_bm_ifc_type <= ib_wr.data(31);
        end if;
     end if;
   end process;          
   
   -- TRANSACTION TAG counter -------------------------------------------------
   cnt_bm_tagp: process(ib_clk, ib_rst)                                                  
   begin                                                                          
      if (ib_rst = '1') then                                                       
         cnt_bm_tag_aux <= (others => '0');                                                      
      elsif (ib_clk'event AND ib_clk = '1') then                                              
         if (bm_decoded = '1') then                                                     
            cnt_bm_tag_aux <= cnt_bm_tag_aux + 1;                                              
         end if;                                                                              
      end if;                                                                      
   end process;  

   cnt_bm_tag <= cnt_bm_tag_aux;  
   
end board_test_arch;


 
