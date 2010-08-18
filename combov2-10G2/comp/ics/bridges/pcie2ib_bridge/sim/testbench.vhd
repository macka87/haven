--
-- testbench.vhd : Top level testbench for PCIe2IB bridge
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

-- IEEE
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_textio.all;
use ieee.numeric_std.all; 

-- STD
library STD;
use STD.textio.all;

-- PCIE Simulation Package
use work.pcie_sim_oper.all;  

-- ----------------------------------------------------------------------------
--                          ENTITY DECLARATION                               --
-- ----------------------------------------------------------------------------

entity testbench is 
end testbench;

-- ----------------------------------------------------------------------------
--                        ARCHITECTURE DECLARATION                           --
-- ----------------------------------------------------------------------------

architecture behavioral of testbench is

   -- -------------------------------------------------------------------------
   --                           Constant declaration                         --
   -- -------------------------------------------------------------------------

   constant SYS_CLK_PER     : time := 10 ns; -- 100 MHz
   constant DSPORT_CLK_PER  : time := 4 ns;  -- 250 MHz
   constant RESET_TIME      : time := 1 us;
   
   constant FAST_SIMULATION : std_logic := '1';
   
   -- -------------------------------------------------------------------------
   --                           Component declaration                        --
   -- -------------------------------------------------------------------------
   
   -- Xilinx DSPORT (PXP endpoint model + testbench) --------------------------
   component XILINX_PCI_EXP_4_LANE_DOWNSTREAM_PORT 
      port (
         -- SYS Inteface
         sys_clk_p   : in std_logic;
         sys_clk_n   : in std_logic;
         sys_reset_n : in std_logic;
         -- PCI-Express Interface
         pci_exp_txn : out std_logic_vector(3 downto 0);
         pci_exp_txp : out std_logic_vector(3 downto 0);
         pci_exp_rxn : in  std_logic_vector(3 downto 0);
         pci_exp_rxp : in  std_logic_vector(3 downto 0);
         -- PCIE SIM Interface
         CTRL        : in  t_pcie_ctrl;
         STROBE      : in  std_logic;
         BUSY        : out std_logic
      );
   end component;

   -- TEST entity (endpoint_block_plus + PCIe2IB Bridge + user app.) ----------
   component BOARD is 
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
   end component;

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
   signal sys_reset_n : std_logic;
   signal sys_clk_p   : std_logic;
   signal sys_clk_n   : std_logic;
   signal dsp_clk_p   : std_logic;
   signal dsp_clk_n   : std_logic;
   
   signal pci_exp_txn : std_logic_vector(3 downto 0);
   signal pci_exp_txp : std_logic_vector(3 downto 0);
   signal pci_exp_rxn : std_logic_vector(3 downto 0);
   signal pci_exp_rxp : std_logic_vector(3 downto 0);

   signal pcie_sim_ctrl   : t_pcie_ctrl;
   signal pcie_sim_strobe : std_logic;
   signal pcie_sim_busy   : std_logic; 
   
begin

   -- -------------------------------------------------------------------------
   --                           Clock generators                             --
   -- -------------------------------------------------------------------------

   SYSCLK_GEN : process
   begin
      sys_clk_p <= '1';
      wait for SYS_CLK_PER/2;
      sys_clk_p <= '0';
      wait for SYS_CLK_PER/2;
   end process;
     
   DSP_CLK_GEN : process
   begin
      dsp_clk_p <= '1';
      wait for DSPORT_CLK_PER/2;
      dsp_clk_p <= '0';
      wait for DSPORT_CLK_PER/2;
   end process;
   
   sys_clk_n   <= not sys_clk_p;
   dsp_clk_n   <= not dsp_clk_p;
   sys_reset_n <= '0', '1' after RESET_TIME;

   -- -------------------------------------------------------------------------
   --                   Xilinx SDPORT (PXP endpoint model)                   --
   -- -------------------------------------------------------------------------   

   PXP_SIM: XILINX_PCI_EXP_4_LANE_DOWNSTREAM_PORT 
   port map (
      -- SYS Inteface
      sys_clk_p   => dsp_clk_p,
      sys_clk_n   => dsp_clk_n,
      sys_reset_n => sys_reset_n,
      -- PCI-Express Interface
      pci_exp_txn => pci_exp_rxn,
      pci_exp_txp => pci_exp_rxp,      
      pci_exp_rxn => pci_exp_txn,
      pci_exp_rxp => pci_exp_txp,
      -- PCIE SIM interface
      CTRL        => pcie_sim_ctrl,
      STROBE      => pcie_sim_strobe,
      BUSY        => pcie_sim_busy       
   );

   -- -------------------------------------------------------------------------
   --                                UUT                                     --
   -- -------------------------------------------------------------------------

   UUT: BOARD 
   generic map (
      FAST_SIMULATION => FAST_SIMULATION 
   )
   port map (
      -- SYS Inteface
      SYS_CLK_P       => sys_clk_p,    
      SYS_CLK_N       => sys_clk_n,   
      SYS_RESET_N     => sys_reset_n,  
      -- PCI-Express Interface
      PCI_EXP_RXN     => pci_exp_rxn, 
      PCI_EXP_RXP     => pci_exp_rxp,      
      PCI_EXP_TXN     => pci_exp_txn,
      PCI_EXP_TXP     => pci_exp_txp
   ); 

   -- -------------------------------------------------------------------------
   --                               TESTBENCH                                --
   -- -------------------------------------------------------------------------   

   tb : process 
   
   -- Support for pcie_op -----------------------------------------------------
   procedure pcie_op(ctrl : in t_pcie_ctrl) is
   begin  
      wait until (dsp_clk_p'event and dsp_clk_p='1' and pcie_sim_busy = '0'); 
      pcie_sim_ctrl   <= ctrl;
      pcie_sim_strobe <= '1';
      wait for 20 ns; 
      pcie_sim_strobe <= '0';
   end pcie_op;
 
   -- Start testing -----------------------------------------------------------
   begin
      wait for RESET_TIME; 
      
      --                        board        local    len    file name with
      --                        offset      address  inW32  32-b hexa values
      pcie_op(pcie_write_file(X"20000000"&X"10000010", 1, "./test_write.txt"));
      pcie_op(pcie_write_file(X"20000000"&X"10000020", 2, "./test_write.txt"));      
      pcie_op(pcie_write_file(X"20000000"&X"10000030", 3, "./test_write.txt"));      
      pcie_op(pcie_write_file(X"20000000"&X"10000040", 0, "./test_write.txt"));      


      --                   board        local    len    data for write
      --                   offset      address   inB    tag  for read     
      pcie_op(pcie_write(X"20000000"&X"B0000003", 2, X"1234567890ABCDEF"));
      pcie_op(pcie_read (X"20000000"&X"B0000003", 2, 2));
      
      pcie_op(pcie_write(X"20000000"&X"C0000002", 3, X"1234567890ABCDEF"));
      pcie_op(pcie_read (X"20000000"&X"C0000002", 3, 3));
      
      pcie_op(pcie_write(X"20000000"&X"D0000003", 5, X"1234567890ABCDEF"));
      pcie_op(pcie_read (X"20000000"&X"D0000003", 5, 4));
      
      pcie_op(pcie_write(X"20000000"&X"E0000001", 7, X"1234567890ABCDEF"));
      pcie_op(pcie_read (X"20000000"&X"E0000001", 7, 5));      

      pcie_op(pcie_write(X"20000000"&X"F0000000", 8, X"1234567890ABCDEF"));      
      pcie_op(pcie_read (X"20000000"&X"F0000000", 8, 6));           
           
      wait;
   end process;

end behavioral;



