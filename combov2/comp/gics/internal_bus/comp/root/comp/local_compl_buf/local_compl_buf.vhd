--
-- local_compl_buf.vhd : Local completion buffer for PCIe to IB Bridge
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

entity LOCAL_COMPL_BUF is 
   generic(
      LOCAL_TAG_WIDTH 	: integer := 8; 	-- 'Local' Tag width (2^LOCAL_TAG_WIDTH = number of pending Read Requests)
      LIMIT             : integer := 4    -- Number of actually free items in buffer when TRANS_EN_N signal is asserted  
   );  
   port (
      -- clock & reset --------------------------------------------------------
      CLK         : in std_logic;
      RESET       : in std_logic;

	  -- Write interface ------------------------------------------------------
	   RX_TAG      : in  std_logic_vector( 7 downto 0); 		           -- Transaction Tag
	   RX_WR_0		: in  std_logic;								              -- Write Request 0
	   RX_REQ_ID	: in  std_logic_vector(15 downto 0);	              -- Requester ID (BUS, DEVICE, FUNCTION)
	   RX_WR_1		: in  std_logic;								              -- Write Request 1
	   RX_ALLOW		: out std_logic;								              -- Allow to write
	   RX_LOCAL_TAG: out std_logic_vector(7 downto 0);                  -- Local Tag
	  -- Read Interface -------------------------------------------------------
      TX_TAG      : out std_logic_vector( 7 downto 0); 	              -- Transaction Tag     
      TX_REQ_ID   : out std_logic_vector(15 downto 0); 	              -- Requester ID (BUS, DEVICE, FUNCTION)
      TX_RD       : in  std_logic;  								           -- Read Request
      TX_RTAG     : in  std_logic_vector( 7 downto 0);                 -- Read Address

	  -- STATUS ---------------------------------------------------------------
      STATUS      : out std_logic_vector( 8 downto 0);                 -- Number of pending Read Requests
	   RX_FULL		: out std_logic								              -- Local Buffer Full
--       TRANS_EN_N  : out std_logic                                      -- Enable transactions 
   );
end LOCAL_COMPL_BUF;


-- ----------------------------------------------------------------------------
--  ARCHITECTURE DECLARATION  --  Completion buffer for PCIe to IB Bridge    --
-- ----------------------------------------------------------------------------

architecture full of LOCAL_COMPL_BUF is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   constant BUF_FULL       : std_logic_vector(LOCAL_TAG_WIDTH-1 downto 0) := (others => '1');
   constant BUF_EMPTY      : std_logic_vector(LOCAL_TAG_WIDTH-1 downto 0) := (others => '0');
   constant ADDR_MAX         : std_logic_vector(LOCAL_TAG_WIDTH downto 0) := ('1' & BUF_EMPTY);

   -- local address/tag counter
   signal local_cnt		   : std_logic_vector(LOCAL_TAG_WIDTH-1 downto 0);
   signal local_cnt_en	   : std_logic;

   -- Flag memory
   signal flag_mem_in      : std_logic_vector(0 downto 0);
   signal flag_mem_we 	   : std_logic;
   signal flag_mem_addr_a  : std_logic_vector(LOCAL_TAG_WIDTH-1 downto 0);
   signal flag_mem_do_b    : std_logic_vector(0 downto 0);

   -- addresses to data valid memory
   signal tx_rtag_sel_addr	: std_logic_vector(LOCAL_TAG_WIDTH-1 downto 0);
   signal flag_addr        : std_logic_vector(LOCAL_TAG_WIDTH-1 downto 0); 
   signal clr_addr         : std_logic_vector(LOCAL_TAG_WIDTH downto 0);
   signal tx_rtag_reg		: std_logic_vector(LOCAL_TAG_WIDTH-1 downto 0);

   -- want to write 0/1 to valid memory together
   signal tx_rd_rx_wr		: std_logic;
   signal tx_rd_rx_wr_reg	: std_logic;

   -- full register
   signal full_reg			: std_logic_vector(LOCAL_TAG_WIDTH downto 0);

   -- init phase
   signal init             : std_logic;
   signal init_done        : std_logic;

begin
   -- -------------------------------------------------------------------------
   --                         'LOCAL' BUFFER ASSERTIONS
   -- ------------------------------------------------------------------------- 
   -- coverage off
   assert not (flag_mem_do_b(0)='1' and (RX_WR_0='1' or RX_WR_1='1') and CLK='1' and CLK'event) report "ERROR: LOCAL_BUFFER: WRx WHEN ALLOW IS LOW" severity ERROR;
   assert not (full_reg(LOCAL_TAG_WIDTH) = '1' and RX_WR_1='1' and CLK='1' and CLK'event)       report "ERROR: LOCAL_BUFFER: WRx WHEN FULL"         severity ERROR;
   assert not ((full_reg=0) and TX_RD='1' and CLK='1' and CLK'event)                            report "ERROR: LOCAL_BUFFER: READ WHEN EMPTY"       severity ERROR;
   -- coverage on
   -- -------------------------------------------------------------------------
   --                         'LOCAL' BUFFER	                                --
   -- ------------------------------------------------------------------------- 
   
   -- -- Tag Memory -----------------------------------------------------------
   U_LR_BUF_1: entity work.DP_DISTMEM(behavioral)
      generic map(
      	DATA_WIDTH   => 8,
      	ITEMS 		 => 2**LOCAL_TAG_WIDTH,
      	DISTMEM_TYPE => 64, -- 16, 32, 64 bits
      	DEBUG   	    => false
	)
	port map (
		-- Common interface
      	RESET  		=> RESET,	-- not used yet
      	-- R/W Port
      	DI     		=> RX_TAG,
      	WE     		=> RX_WR_0,
      	WCLK   		=> CLK,
      	ADDRA  	 	=> local_cnt,
      	DOA    		=> open,
      	-- Read Port
      	ADDRB  		=> TX_RTAG(LOCAL_TAG_WIDTH-1 downto 0),
      	DOB    		=> TX_TAG
         );

   -- -- Local Req. ID Memory -------------------------------------------------
   U_LR_BUF_0: entity work.DP_DISTMEM(behavioral)
   	generic map (
	  	-- Data Width
      	DATA_WIDTH   => 16,
      	ITEMS 		 => 2**LOCAL_TAG_WIDTH,
      	DISTMEM_TYPE => 64,  -- 16, 32, 64 bits
      	DEBUG   	    => false
         )
	port map(
		   -- Common interface
      	RESET  		=> RESET,	-- not used yet
      	-- R/W Port
      	DI     		=> RX_REQ_ID,
      	WE     		=> RX_WR_1,
      	WCLK   		=> CLK,
      	ADDRA  	 	=> local_cnt,
      	DOA    		=> open,
      	-- Read Port
      	ADDRB  		=> TX_RTAG(LOCAL_TAG_WIDTH-1 downto 0),
      	DOB    		=> TX_REQ_ID
	);


   -- -- Free item counter ----------------------------------------------------
   -- enable counting
   local_cnt_en  <= flag_mem_do_b(0) or RX_WR_1;

   -- counter of local read transaction
   LOCAL_CNT_REG : process (CLK, RESET) 
      begin
         if (CLK='1' and CLK'event) then 
            if(RESET='1') then
               local_cnt <= (others => '0');
            elsif (local_cnt_en = '1') then
            	local_cnt <= local_cnt + 1;
            end if;
         end if;
      end process; 

   -- -- Free/Occupied tags flags memory --------------------------------------
   -- memmory to valid data signaling
   VALID_DATA_I : entity work.DP_DISTMEM(behavioral)
   	generic map(
      -- Data Width
      DATA_WIDTH  	=> 1,
      ITEMS 	    	=> 2**LOCAL_TAG_WIDTH,
      DISTMEM_TYPE   => 64, -- only 16, 32, 64 bits
      DEBUG   	      => false
   )
   port map(
      -- Common interface
      RESET  	=> RESET,
      -- R/W Port
      DI     	=> flag_mem_in,
      WE     	=> flag_mem_we,
      WCLK   	=> CLK,
	   ADDRA   	=> flag_mem_addr_a,
      DOA     	=> open,
      -- Read Port
      ADDRB  	=> local_cnt,
      DOB    	=> flag_mem_do_b
  	);

   -- detect full memory
   FULL_REG_I : process (CLK, RESET, RX_WR_1, TX_RD, tx_rd_rx_wr, full_reg )	
	   begin
	   	if(CLK='1' and CLK'event) then
	   		if(RESET='1') then
	   			full_reg <= (others => '0');
   			elsif(RX_WR_1 = '1') then	-- store
	   			full_reg <= full_reg + 1;
	   		elsif(TX_RD = '1' or tx_rd_rx_wr_reg='1') then -- clear
	   			full_reg <= full_reg - 1;
	   		end if;
	   	end if;
	   end process;
   

   STATUS(LOCAL_TAG_WIDTH downto 0) <= full_reg;

   -- -- RX signals mapping ---------------------------------------------------
   RX_FULL <= full_reg(LOCAL_TAG_WIDTH); 

   -- enable transactions
--    TRANS_EN_N <= '1' when (full_reg >= (BUF_FULL - conv_std_logic_vector(LIMIT, full_reg'length)) or init = '1') else
--                  '0';

   -- output allow write
   RX_ALLOW		<= (not flag_mem_do_b(0)) and (not init);  

   -- output tag 
   RX_LOCAL_TAG(LOCAL_TAG_WIDTH-1 downto 0)	<= local_cnt;

   GEN_ZERO : if not (LOCAL_TAG_WIDTH = 8) generate
     RX_LOCAL_TAG(7 downto LOCAL_TAG_WIDTH) <= (others => '0');
     STATUS(8 downto LOCAL_TAG_WIDTH+1) <= (others => '0');
   end generate;
       

   -- -- RX signals mapping ---------------------------------------------------
	-- allow write 0/1
   flag_mem_in(0) <= RX_WR_1;
	flag_mem_we    <= RX_WR_1 or TX_RD or tx_rd_rx_wr_reg or init;

	-- select corect address to valid register
   FLAG_ADDR_MUX : process(RX_WR_1, tx_rtag_sel_addr, local_cnt)
	   begin
		   case (RX_WR_1) is
		   	when '1' => flag_addr <= local_cnt;
		   	when '0' => flag_addr <= tx_rtag_sel_addr;
		   	when others => null;
		   end case;
	   end process;

	-- select corect address to valid register
   FLAG_MEM_ADDR_A_MUX : process(init, flag_addr, clr_addr)
	   begin
		   case (init) is
		   	when '1' => flag_mem_addr_a <= clr_addr(LOCAL_TAG_WIDTH-1 downto 0);
		   	when '0' => flag_mem_addr_a <= flag_addr;
		   	when others => null;
		   end case;
	   end process;

   --  clear address to valid memory
   CLR_ADDR_I : process( CLK, RESET, clr_addr, init )
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

   -- want to write 0/1 together
   tx_rd_rx_wr	<= RX_WR_1 and TX_RD;

   -- wait 1 period
   TX_RD_RX_WR_I : process( CLK, RESET, tx_rd_rx_wr )
   	begin
		   if(CLK='1' and CLK'event) then
			   if( RESET = '1') then
				   tx_rd_rx_wr_reg <= '0';
			   else
				   tx_rd_rx_wr_reg <= tx_rd_rx_wr;
			   end if;
		   end if;
	   end process;

   -- register input address
   TX_RTAG_REG_I : process(CLK, RESET)
	begin
		if(CLK='1' and CLK'event) then
			if(RESET = '1') then
				tx_rtag_reg <= (others => '0');
			else
				tx_rtag_reg <= TX_RTAG(LOCAL_TAG_WIDTH-1 downto 0);
			end if;
		end if;
	end process;

   -- select correct TX 
   TX_RTAG_MUX : process(TX_RTAG, tx_rtag_reg, tx_rd_rx_wr_reg)
	   begin
	   	case (tx_rd_rx_wr_reg) is
	   		when '1' => tx_rtag_sel_addr <= tx_rtag_reg;
	   		when '0' => tx_rtag_sel_addr <= TX_RTAG(LOCAL_TAG_WIDTH-1 downto 0);
	   		when others => null;
	   	end case;
	   end process;

end architecture full;



