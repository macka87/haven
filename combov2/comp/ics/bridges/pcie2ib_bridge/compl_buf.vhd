--
-- compl_buf.vhd : Completion buffer for PCIe to IB Bridge
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

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--     ENTITY DECLARATION -- Completion buffer for PCIe to IB Bridge         -- 
-- ----------------------------------------------------------------------------

entity COMPL_BUF is 
   generic(
         LTAG_WIDTH : integer := 5; -- 'Local Read' Buffer tag width
         GTAG_WIDTH : integer := 5  -- 'Global Read' Buffer tag width         
      );  
   port (
      -- clock & reset --------------------------------------------------------
      CLK           : in std_logic;  -- FPGA clock
      RESET         : in std_logic;  -- Reset active high

      -- 'Local Read' Buffer (LR_BUF) interface -------------------------------
      -- RX buffer part (write ifc) --
      RX_TC         : in std_logic_vector( 2 downto 0); -- Traffic Class     
      RX_ATTR       : in std_logic_vector( 1 downto 0); -- Attributes     
      RX_TAG        : in std_logic_vector( 7 downto 0); -- Transaction Tag     
      RX_BUS_NUM    : in std_logic_vector( 7 downto 0); -- Bus number           
      RX_DEVICE_NUM : in std_logic_vector( 4 downto 0); -- Device number     
      RX_FUNC_NUM   : in std_logic_vector( 2 downto 0); -- Function number     
      RX_BMADDR     : in std_logic_vector(63 downto 0); -- BM global address      

      RXWE          : in std_logic; -- RX write enable
      RXWTAG        : in std_logic_vector(LTAG_WIDTH-1 downto 0); -- RX write address

      RX_FULL       : out std_logic; -- Local Read Buffer full flag

      -- TX buffer part (read ifc) --      
      TX_TC         : out std_logic_vector( 2 downto 0); -- Traffic Class     
      TX_ATTR       : out std_logic_vector( 1 downto 0); -- Attributes     
      TX_TAG        : out std_logic_vector( 7 downto 0); -- Transaction Tag     
      TX_BUS_NUM    : out std_logic_vector( 7 downto 0); -- Bus number           
      TX_DEVICE_NUM : out std_logic_vector( 4 downto 0); -- Device number     
      TX_FUNC_NUM   : out std_logic_vector( 2 downto 0); -- Function number     
      TX_BMADDR     : out std_logic_vector(63 downto 0); -- BM global address      
      
      TXRD          : in  std_logic;  -- TX read enable
      TXRTAG        : in  std_logic_vector(LTAG_WIDTH-1 downto 0); -- TX read address
      TXVLD         : out std_logic;  -- TX valid data
      
      -- 'Global Read' Buffer (GR_BUF) interface ------------------------------
      -- RX buffer part (read ifc) --      
      RX_GRADDR_IN  : in  std_logic_vector(31 downto 0); -- Global READ address
      RX_GRTAG_IN   : in  std_logic_vector(15 downto 0); -- completion tag for IB packet            
      RX_WRITE      : in  std_logic;  -- RX write enable      
      
      RX_GRADDR_OUT : out std_logic_vector(31 downto 0); -- Global READ address      
      RX_GRTAG_OUT  : out std_logic_vector(15 downto 0); -- completion tag for IB packet            
      RXRD          : in  std_logic;  -- RX read enable
      RXRTAG        : in  std_logic_vector(GTAG_WIDTH-1 downto 0); -- RX read address
      RXVLD         : out std_logic;  -- RX valid data

      RXLAST        : in  std_logic;  -- last read from GR Buffer
      
      -- TX buffer part (write ifc) --
      TX_GRADDR     : in std_logic_vector(31 downto 0); -- Global READ address
      TX_GRTAG      : in std_logic_vector(15 downto 0); -- completion tag for IB packet

      TXWE          : in std_logic; -- TX write enable
      TXWTAG        : in std_logic_vector(GTAG_WIDTH-1 downto 0); -- TX write address     
      TX_FULL       : out std_logic -- Global Read Buffer full flag      
   );
end COMPL_BUF;

-- ----------------------------------------------------------------------------
--  ARCHITECTURE DECLARATION  --  Completion buffer for PCIe to IB Bridge    --
-- ----------------------------------------------------------------------------

architecture compl_buf_arch of COMPL_BUF is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
  
   -- 'Local Read' Buffer (DP_BMEM) generic constants
   constant LR_BUF_WIDTH : integer := 96;           
   constant LR_BUF_BTYPE : integer := 36;

   -- 'Global Read' Buffer (DP_BMEM) generic constants
   constant GR_BUF_WIDTH : integer := 64;           
   constant GR_BUF_BTYPE : integer := 36;     

   -- ZERO and ONES constant
   constant ZERO         : std_logic_vector(LR_BUF_WIDTH - 1 downto 0) := (others => '0');   
   constant ONES_L       : std_logic_vector(LTAG_WIDTH - 3 downto 0)   := (others => '1');      
   constant ONES_G       : std_logic_vector(GTAG_WIDTH - 3 downto 0)   := (others => '1');   

   -- 'Local Read' Buffer signals
   signal lr_buf_in      : std_logic_vector(LR_BUF_WIDTH-1 downto 0);
   signal lr_buf_out     : std_logic_vector(LR_BUF_WIDTH-1 downto 0);
   signal local_cnt_en   : std_logic;
   signal local_cnt_dir  : std_logic;
   signal local_cnt      : std_logic_vector(LTAG_WIDTH-1 downto 0);

   -- 'Global Read' Buffer signals
   signal gr_buf_win     : std_logic_vector(GR_BUF_WIDTH-1 downto 0);
   signal gr_buf_in      : std_logic_vector(GR_BUF_WIDTH-1 downto 0);
   signal gr_buf_out     : std_logic_vector(GR_BUF_WIDTH-1 downto 0);      
   signal global_cnt_en   : std_logic;
   signal global_cnt_dir  : std_logic;
   signal global_cnt      : std_logic_vector(GTAG_WIDTH-1 downto 0);   
  
begin

   -- -------------------------------------------------------------------------
   --                         'LOCAL READ' BUFFER                            --
   -- ------------------------------------------------------------------------- 
   
   U_lr_buf: entity work.DP_BMEM  
      generic map(
         DATA_WIDTH => LR_BUF_WIDTH,
         ITEMS      => 2**LTAG_WIDTH,     
         BRAM_TYPE  => LR_BUF_BTYPE, 
         OUTPUT_REG => false,
         DEBUG      => false     
      )
      port map(
         RESET      => RESET,

         -- write port
         CLKA       => CLK,
         PIPE_ENA   => '1',
         REA        => '0',
         WEA        => RXWE,  
         ADDRA      => RXWTAG,
         DIA        => lr_buf_in,
         DOA_DV     => open,
         DOA        => open,
                    
         -- read port
         CLKB       => CLK,
         PIPE_ENB   => '1',
         REB        => TXRD,
         WEB        => '0',       
         ADDRB      => TXRTAG,
         DIB        => ZERO,
         DOB_DV     => TXVLD, 
         DOB        => lr_buf_out
      );     

   lr_buf_in <= RX_BMADDR&"000"&RX_TC&RX_ATTR&RX_TAG&RX_DEVICE_NUM&RX_FUNC_NUM&RX_BUS_NUM;
                  
   TX_BMADDR     <= lr_buf_out(95 downto 32);               
   TX_TC         <= lr_buf_out(28 downto 26);
   TX_ATTR       <= lr_buf_out(25 downto 24);
   TX_TAG        <= lr_buf_out(23 downto 16);
   TX_DEVICE_NUM <= lr_buf_out(15 downto 11);      
   TX_FUNC_NUM   <= lr_buf_out(10 downto  8);
   TX_BUS_NUM    <= lr_buf_out( 7 downto  0);   

   -- Counter of Local Read Transaction that are in-process -------------------
   local_cntp: process (CLK, RESET) 
   begin
      if (RESET = '1') then 
         local_cnt <= (others => '0');
      elsif (CLK = '1' and CLK'event) then
         if (local_cnt_en = '1') then
            if (local_cnt_dir = '1') then  
               local_cnt <= local_cnt + 1;
            else
               local_cnt <= local_cnt - 1;
            end if;
         end if;
      end if;
   end process; 

   local_cnt_en  <= (RXWE and (not TXRD)) or (TXRD and (not RXWE));
   local_cnt_dir <= RXWE;     

   RX_FULL <= '1' when (local_cnt(LTAG_WIDTH-1 downto 2) = (ONES_L)) else
              '0';
   
   -- -------------------------------------------------------------------------
   --                        'GLOBAL READ' BUFFER                            --
   -- ------------------------------------------------------------------------- 

   U_gr_buf: entity work.DP_BMEM  
      generic map(
         DATA_WIDTH => GR_BUF_WIDTH,
         ITEMS      => 2**GTAG_WIDTH,     
         BRAM_TYPE  => GR_BUF_BTYPE, 
         OUTPUT_REG => false,
         DEBUG      => false     
      )
      port map(
         RESET      => RESET,

         -- write port
         CLKA       => CLK,
         PIPE_ENA   => '1',
         REA        => '0',
         WEA        => TXWE,  
         ADDRA      => TXWTAG,
         DIA        => gr_buf_win,
         DOA_DV     => open,
         DOA        => open,
                                                         
         -- read port                                    
         CLKB       => CLK,                              
         PIPE_ENB   => '1',                              
         REB        => RXRD,                             
         WEB        => RX_WRITE,       
         ADDRB      => RXRTAG,
         DIB        => gr_buf_in,
         DOB_DV     => RXVLD, 
         DOB        => gr_buf_out
      );     

   gr_buf_win <= X"0000"&TX_GRTAG&TX_GRADDR;

   gr_buf_in  <= X"0000"&RX_GRTAG_IN&RX_GRADDR_IN;
   
   RX_GRADDR_OUT <= gr_buf_out(31 downto  0);
   RX_GRTAG_OUT  <= gr_buf_out(47 downto 32);

   -- Counter of Global Read Transaction that are in-process ------------------
   global_cntp: process (CLK, RESET) 
   begin
      if (RESET = '1') then 
         global_cnt <= (others => '0');
      elsif (CLK = '1' and CLK'event) then
         if (global_cnt_en = '1') then
            if (global_cnt_dir = '1') then  
               global_cnt <= global_cnt + 1;
            else
               global_cnt <= global_cnt - 1;
            end if;
         end if;
      end if;
   end process; 

   global_cnt_en  <= (TXWE and (not RXLAST)) or (RXLAST and (not TXWE));
   global_cnt_dir <= TXWE;     

   TX_FULL <= '1' when (global_cnt(GTAG_WIDTH-1 downto 2) = (ONES_G)) else
              '0';   
   
end compl_buf_arch;



