--
-- global_compl_buf.vhd : Global completion buffer for PCIe to IB Bridge
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
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

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--     ENTITY DECLARATION -- Completion buffer for PCIe to IB Bridge         -- 
-- ----------------------------------------------------------------------------

entity GLOBAL_COMPL_BUF is 
   generic (
      GLOBAL_TAG_WIDTH 		: integer := 4;	-- 'Global' Tag width  ( MUST BE <=7 )
      LIMIT                : integer := 2    -- Number of actually free items in buffer when TRANS_EN_N signal is asserted  
   );  
   port (
      -- clock & reset --------------------------------------------------------
      CLK            : in std_logic;  	-- FPGA clock
      RESET          : in std_logic;  	-- Reset active high

	   -- Read Interface -------------------------------------------------------
      RX_LOCAL_ADDR  : out std_logic_vector(31 downto 0); 					   -- Local Address     
      RX_LOCAL_TAG   : out std_logic_vector(7 downto 0); 	               -- Local Tag     

      RX_RD     	   : in  std_logic;  										      -- Read Request
      RX_GLOBAL_TAG  : in  std_logic_vector(7 downto 0); 	               -- Read Address

	   RX_LAST_CPL	   : in  std_logic;										         -- Last Completion
	   RX_LEN_CPL	   : in  std_logic_vector(11 downto 0);					   -- Completion Length

	   -- Write interface ------------------------------------------------------
      TX_LOCAL_ADDR  : in  std_logic_vector(31 downto 0); 					   -- Local Address
	   TX_LOCAL_TAG   : in  std_logic_vector(7 downto 0);                	-- Local Tag
	   TX_WR			   : in  std_logic;										         -- Write Request
      TX_ALLOW       : out std_logic;                                      -- Allow to write
	   TX_RTAG 		   : out std_logic_vector(7 downto 0);                	-- Global Tag

      -- STATUS ---------------------------------------------------------------
      STATUS         : out std_logic_vector(8 downto 0);                   -- Number of pending Read Requests
      TRANS_EN_N     : out std_logic;                                      -- Enable transactions 
      TX_FULL        : out std_logic                                       -- Global Buffer full 
   );
end GLOBAL_COMPL_BUF;


-- ----------------------------------------------------------------------------
--  ARCHITECTURE DECLARATION  --  Completion buffer for PCIe to IB Bridge    --
-- ----------------------------------------------------------------------------

architecture full of GLOBAL_COMPL_BUF is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   constant BUF_FULL       : std_logic_vector(GLOBAL_TAG_WIDTH-1 downto 0) := (others => '1');
   constant BUF_EMPTY      : std_logic_vector(GLOBAL_TAG_WIDTH-1 downto 0) := (others => '0');
   constant ADDR_MAX         : std_logic_vector(GLOBAL_TAG_WIDTH downto 0) := ('1' & BUF_EMPTY);

   -- Buffer generic constants
   constant BUF_WIDTH 	   : integer := 32+8; --> Local Address (32) + Local Tag
  
   -- other constant
   constant CNT_ONES       : std_logic_vector(GLOBAL_TAG_WIDTH-1 downto 0) := (others => '1');
   constant GND_VEC        : std_logic_vector(31 downto 0) := (others => '0');

   -- global buffer interface
   signal buf_in           : std_logic_vector(BUF_WIDTH-1 downto 0);
   signal buf_out          : std_logic_vector(BUF_WIDTH-1 downto 0);
   signal buf_out_b        : std_logic_vector(BUF_WIDTH-1 downto 0);
   signal buf_addr         : std_logic_vector(GLOBAL_TAG_WIDTH-1 downto 0);
   signal buf_we           : std_logic;


   -- data valid memory interface
   signal data_valid_addr_a: std_logic_vector(GLOBAL_TAG_WIDTH-1 downto 0);
   signal data_valid_di_a  : std_logic_vector(0 downto 0);
   signal data_valid_we    : std_logic;
   signal data_valid_do_a  : std_logic_vector(0 downto 0);
   signal data_valid_do_b  : std_logic_vector(0 downto 0);
  
   --addresses to data_valid register
   signal clr_addr         : std_logic_vector(GLOBAL_TAG_WIDTH downto 0);

   -- alinged length to 32 bits
   signal rx_len_cpl_sig   : std_logic_vector(31 downto 0);
   
   -- global address/tag counter
   signal global_cnt       : std_logic_vector(GLOBAL_TAG_WIDTH-1 downto 0);
   signal global_cnt_en    : std_logic;
   
   -- needs to write back local address
   signal rx_write_back    : std_logic;

   -- last fragmented read
   signal rx_rd_last       : std_logic;

   -- detect full memory
   signal full_reg         : std_logic_vector(GLOBAL_TAG_WIDTH downto 0);

   -- init phase
   signal init             : std_logic;
   signal init_done        : std_logic;

   
begin

   -- -------------------------------------------------------------------------
   --                         'GLOBAL' BUFFER	                             --
   -- -------------------------------------------------------------------------
   
   U_LR_BUF: entity work.DP_DISTMEM (behavioral)
      generic map(
	  	   -- Data Width
      	DATA_WIDTH     => BUF_WIDTH,
      	-- Item in memory needed, one item size is DATA_WIDTH
      	ITEMS 		   => 2**GLOBAL_TAG_WIDTH,
      	-- Distributed Ram Type(capacity) only 16, 32, 64 bits
      	DISTMEM_TYPE   => 32, 
      	-- debug prints
      	DEBUG   	      => false
	)
	port map(
		-- Common interface
      	RESET  		=> RESET,	-- not used yet
      	-- R/W Port
      	DI     		=> buf_in,
      	WE     		=> buf_we,
      	WCLK   		=> CLK,
      	ADDRA  	 	=> buf_addr,
      	DOA    		=> buf_out,
         -- Read Port
         ADDRB  	   => RX_GLOBAL_TAG(GLOBAL_TAG_WIDTH-1 downto 0),
         DOB    	   => buf_out_b

	);
   
   -- output data
   RX_LOCAL_ADDR  <= buf_out(31 downto 0);     
   RX_LOCAL_TAG   <= buf_out(32+8-1 downto 32);     
   
   -- memmory to valid data signaling
   VALID_DATA_I :entity work.DP_DISTMEM (behavioral)
   	generic map(
      -- Data Width
      DATA_WIDTH     => 1,
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS 	      => 2**GLOBAL_TAG_WIDTH,
      -- Distributed Ram Type(capacity) only 16, 32, 64 bits
      DISTMEM_TYPE   => 16,
      -- debug prints
      DEBUG   	      => false
   )
   port map(
      -- Common interface
      RESET  	=> RESET,
      -- R/W Port
      DI     	=> data_valid_di_a,
      WE     	=> data_valid_we,
      WCLK   	=> CLK,
	   ADDRA   	=> data_valid_addr_a,
      DOA     	=> data_valid_do_a,
      -- Read Port
      ADDRB  	=> global_cnt,
      DOB    	=> data_valid_do_b
  	);

 	-- clear mode
   DATA_VALID_ADDR_A_MUX: process(init, clr_addr, buf_addr)
	   begin
		   case (init) is
		   	when '1' => data_valid_addr_a    <= clr_addr(GLOBAL_TAG_WIDTH-1 downto 0);
		   	when '0' => data_valid_addr_a    <= buf_addr;
		   	when others => data_valid_addr_a <= (others => 'X');
		   end case;
	   end process;

 	-- select write enable to data valid memory
   DATA_VALID_WE_MUX: process(rx_rd_last, TX_WR, RX_RD, init)
	   begin
		   case (RX_RD) is
		   	when '1' => data_valid_we <= rx_rd_last or init;   -- init added
		   	when '0' => data_valid_we <= TX_WR or init;        -- init added
		   	when others => data_valid_we <= 'X';
		   end case;
	   end process;

 	-- clear mode
   DATA_VALID_DI_A_MUX: process(init, RX_RD)
	   begin
		   case (init) is
		   	when '1' => data_valid_di_a(0) <= '0';             -- clear always
		   	when '0' => data_valid_di_a(0) <= not RX_RD;       -- clear/set valid memory data
		   	when others => data_valid_di_a(0) <= 'X';
		   end case;
	   end process;

   --  clear address to valid memory
   CLR_ADDR_I : process(CLK, RESET)
   	begin
		   if(CLK='1' and CLK'event) then
			   if( RESET = '1') then
				   clr_addr <= (others => '0');
            elsif(init = '1') then
               clr_addr <= clr_addr + 1; 
			   end if;
		   end if;
	   end process;

   -- test initialization phase   
   init_done   <= '1' when ( clr_addr = ADDR_MAX ) else '0';
   init        <= not init_done;

   -- allow to count
   global_cnt_en <= data_valid_do_b(0) or TX_WR; 
   
   -- counter of global read transaction
   GLOBAL_CNT_REG : process (CLK, RESET, global_cnt_en) 
      begin
         if (CLK = '1' and CLK'event) then
           if (RESET = '1') then 
             global_cnt <= (others => '0');
           elsif (global_cnt_en = '1') then
           	global_cnt <= global_cnt + 1;
           end if;
         end if;
      end process;

   -- zero added length      
   rx_len_cpl_sig <= GND_VEC(31 downto 12) & RX_LEN_CPL;
      
	-- select data to global buffer
   GLOBAL_BUF_DI_MUX : process(buf_out_b, RX_LEN_CPL, TX_LOCAL_ADDR, TX_LOCAL_TAG, RX_RD, rx_len_cpl_sig)
	   begin
		   case (RX_RD) is
		   	when '1' => buf_in <= buf_out_b(32+8-1 downto 32) & (buf_out_b(31 downto 0) + rx_len_cpl_sig);
		   	when '0' => buf_in <= TX_LOCAL_TAG & TX_LOCAL_ADDR;
		   	when others => buf_in <= (others => 'X');
		   end case;
	   end process;

	-- select address to global buffer
   GLOBAL_BUF_ADDR_MUX : process(RX_GLOBAL_TAG, global_cnt, RX_RD)
	   begin
		   case (RX_RD) is
		   	when '1' => buf_addr <= RX_GLOBAL_TAG(GLOBAL_TAG_WIDTH-1 downto 0);
		   	when '0' => buf_addr <= global_cnt;
		   	when others => buf_addr <= (others => 'X');
		   end case;
	   end process;

   -- write back modified local address to memory    
   rx_write_back <= RX_RD and (not RX_LAST_CPL);    
      
 	-- select write enable to global buffer
   GLOBAL_BUF_WE_MUX: process(rx_write_back, TX_WR, RX_RD)
	   begin
		   case (RX_RD) is
		   	when '1' => buf_we <= rx_write_back;
		   	when '0' => buf_we <= TX_WR;
		   	when others => buf_we <=  'X';
		   end case;
	   end process;

   -- last fragmented read    
   rx_rd_last <= RX_LAST_CPL and RX_RD;
     
   -- detect full memory
   FULL_REG_I : process (CLK, RESET)	
	   begin
	   	if(CLK='1' and CLK'event) then
	   		if(RESET='1') then
	   			full_reg <= (others => '0');
            else
	   			if(rx_rd_last = '1') then	-- store
	   				full_reg <= full_reg - 1;
	   			elsif(TX_WR = '1') then -- clear
	   				full_reg <= full_reg + 1;
	   		   end if;
	   		end if;
	   	end if;
	   end process;

   -- TX full indicator
   TX_FULL <= full_reg(GLOBAL_TAG_WIDTH);

   -- enable transactions
   TRANS_EN_N <= '1' when (full_reg >= (BUF_FULL - conv_std_logic_vector(LIMIT, full_reg'length)) or init = '1') else
                 '0';

   -- allow to write   
   TX_ALLOW <= (not (data_valid_do_b(0) or RX_RD)) and (not init);

   -- output global tag
   TX_RTAG(GLOBAL_TAG_WIDTH-1 downto 0) <= global_cnt;

   STATUS(GLOBAL_TAG_WIDTH downto 0) <= full_reg;

   GEN_ZERO : if not (GLOBAL_TAG_WIDTH = 8) generate
     TX_RTAG(7 downto GLOBAL_TAG_WIDTH) <= (others => '0');
     STATUS(8 downto GLOBAL_TAG_WIDTH+1) <= (others => '0');
   end generate;
        

end architecture full;

