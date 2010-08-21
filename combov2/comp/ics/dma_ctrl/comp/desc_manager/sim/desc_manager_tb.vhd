-- desc_manager_tb.vhd: Testbench File
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
-- TODO: more and more tests
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.numeric_std.all;

use work.ib_pkg.all;       -- Internal Bus Package
use work.ib_sim_oper.all;  -- Internal Bus Simulation Package
use work.ib_bfm_pkg.all;   -- Internal Bus BFM Package
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is
	
	constant CLKPER			: time := 10 ns;
   constant DMAWORKTIME    : time := 20 ns;
	constant BASE_ADDR		: std_logic_vector(31 downto 0) := (others => '0');
	constant FLOWS			   : integer := 1;
	constant BLOCK_SIZE		: integer := 32;
	constant TEST_LIMIT     : std_logic_vector(31 downto 0) := X"80000000";
	constant enable_0		   : std_logic_vector(FLOWS-1 downto 0) := (others => '0');
	constant enable_1		   : std_logic_vector(FLOWS-1 downto 0) := (others => '1');

	-- Common interface
	signal CLK		      : std_logic;
	signal RESET	      : std_logic;
   -- DMA ctrls interface
   signal data_out  	   : std_logic_vector(63 downto 0);
   signal empty     	   : std_logic_vector(FLOWS-1 downto 0); -- not data_vld
   signal read      	   : std_logic_vector(FLOWS-1 downto 0);
   -- Per channel enable interface
   signal enable    	   : std_logic_vector(FLOWS-1 downto 0);
	-- Endpoint map
	alias ib_clk	 	   : std_logic is CLK;
	alias ib_reset   	   : std_logic is RESET;
   signal ib_wr     	   : t_ibmi_write64;
	signal ib_rd     	   : t_ibmi_read64s;
	signal ib_bm     	   : t_ibbm_64;
	signal internal_bus  : t_internal_bus64;
	signal bm_type_4     : std_logic_vector(3 downto 0);  

   -- DESC fifo interface
   signal df_data    : std_logic_vector(63 downto 0);
   signal df_addr    : std_logic_vector(abs(log2(FLOWS)-1) downto 0);
   signal df_write   : std_logic;
   signal df_full    : std_logic_vector(FLOWS-1 downto 0);
   signal df_status  : std_logic_vector(log2(2*BLOCK_SIZE+1)*FLOWS-1 downto 0);

   signal data_vld   : std_logic_vector(FLOWS-1 downto 0);

begin
    
    -- zero padding!
    --bm_type_4 <= "00" & ib_bm.TRANS_TYPE;
    ib_bm.TRANS_TYPE <= bm_type_4(1 downto 0);
-- -------------------------------------------------------------------------
-- UUT Instantion
uut : entity work.DESC_MANAGER_BM
	generic map (
		BASE_ADDR      => BASE_ADDR,
		FLOWS		      => FLOWS,
		BLOCK_SIZE	   => BLOCK_SIZE
	)
	port map(
		-- Common interface
		CLK			   => CLK,
		RESET		      => RESET,

      -- Memory interface
      -- Write interface
		WR_ADDR		   => ib_wr.ADDR,
		WR_DATA		   => ib_wr.DATA,
		WR_BE		      => ib_wr.BE,
		WR_REQ		   => ib_wr.REQ,
		WR_RDY		   => ib_wr.RDY,

      -- Bus Master interface
 		BM_GLOBAL_ADDR =>  ib_bm.GLOBAL_ADDR,
 		BM_LOCAL_ADDR  =>  ib_bm.LOCAL_ADDR,
		BM_LENGTH      =>  ib_bm.LENGTH,   
		BM_TAG         =>  ib_bm.TAG,
 		BM_TRANS_TYPE  =>  bm_type_4,
 		BM_REQ         =>  ib_bm.REQ,
		-- Output                        
	 	BM_ACK         =>  ib_bm.ACK,
 		BM_OP_TAG      =>  ib_bm.OP_TAG,
 		BM_OP_DONE     =>  ib_bm.OP_DONE,
    
      -- DESC fifo interface
      DF_DATA           => df_data,
      DF_ADDR           => df_addr,
      DF_WRITE          => df_write,
      DF_FULL           => df_full,
      DF_STATUS         => df_status,


      -- Per channel enable interface
      ENABLE         => enable 
	);	

   -- multififo for whole descriptors storing
   DESCRIPTORS : entity work.fifo2nfifo
      generic map(
         DATA_WIDTH  => 64,
         FLOWS       => FLOWS,
         BLOCK_SIZE  => 2*BLOCK_SIZE,
         LUT_MEMORY  => false,
         GLOB_STATE  => false
      )
      port map(
         -- global signals
         CLK   => CLK,
         RESET => RESET,

         -- write interface
         DATA_IN     => df_data,
         BLOCK_ADDR  => df_addr,
         WRITE       => df_write,
         FULL        => df_full,

         -- read interface
         DATA_OUT => data_out,
         DATA_VLD => data_vld,
         READ     => read,
         EMPTY    => open,
         STATUS   => df_status
      );

    -- DMA EMPTY signal from manager
    GEN_FIFO_EMPTY_SIG: for i in 0 to FLOWS-1 generate
      empty(i) <= not data_vld(i);
    end generate;


-- Internal Bus Endpoint ---------------------------------------------------
IB_ENDPOINT_I : entity work.IB_ENDPOINT_MASTER
   generic map(
    	LIMIT         => TEST_LIMIT
   )
   port map(
      -- Common Interface
      IB_CLK        => ib_clk,
      IB_RESET      => ib_reset,
      -- Internal Bus Interface
      INTERNAL_BUS  => internal_bus,
      -- User Component Interface
      WR            => ib_wr,
      RD            => ib_rd,
      -- Busmaster
      BM            => ib_bm
   );

-- Internal Bus Bus Functional Model ------------------------------------------
IB_BFM_U : entity work.IB_BFM
   generic map (
      MEMORY_SIZE 		=> 4096,
      MEMORY_BASE_ADDR 	=> X"00000000" & X"CCCCD000" -- global addr
   )
   port map(
  	   CLK	=> ib_clk,
      -- Internal Bus Interface
      IB	   => internal_bus
   );

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process

begin
	
   RESET 	<= '1', '0' after 15 ns;
   InitMemory(256, "desc_data.txt", IbCmd);
	-- ShowMemory(IbCmd);

	-- disable next_desc_logic
	enable 	<= enable_0; 

   wait for 5*CLKPER;

   -- Init all descriptors from driver side (ONE FLOW)
   SendLocalWrite(   conv_std_logic_vector(2, 15) & conv_std_logic_vector(0, 5) & X"0" & conv_std_logic_vector(0, 5) & "000", 
                        X"08000000", 8, 16#1234#, X"00000000" & X"CCCCD000", IbCmd);


--    -- Init all descriptors from driver side (FLOWS = 32, BLOCK_SIZE = 32)
--    for i in 0 to (FLOWS - 1) loop   
--       SendLocalWrite(   conv_std_logic_vector(2, 15) & conv_std_logic_vector(i, 5) & X"0" & conv_std_logic_vector(i, 5) & "000", 
--                         X"08000000", 8, 16#1234#, X"00000000" & X"CCCCD000", IbCmd);
--    end loop;

   -- OLD ADDRESS (!) :

   -- Init all descriptors from driver side (FLOWS = 32, BLOCK_SIZE = 32)
--    for i in 0 to (FLOWS - 1) loop   
--       SendLocalWrite(   conv_std_logic_vector(1, 15) & conv_std_logic_vector(i, 5) & X"0" & conv_std_logic_vector(i, 5) & "000", 
--                         X"08000000", 8, 16#1234#, X"00000000" & X"CCCCD000", IbCmd);
--    end loop;

   -- Init all descriptors from driver side (FLOWS = 8, BLOCK_SIZE = 32)
   --for i in 0 to (FLOWS - 1) loop   
     -- SendLocalWrite(   conv_std_logic_vector(1, 17) & conv_std_logic_vector(i, 3) & X"0" & conv_std_logic_vector(i, 5) & "000", 
     --                   X"08000000", 8, 16#1234#, X"00000000" & X"CCCCD000", IbCmd);
   --end loop;

   -- Init all descriptors from driver side (FLOWS = 3, BLOCK_SIZE = 32)
   --for i in 0 to (FLOWS - 1) loop   
    --  SendLocalWrite(   conv_std_logic_vector(3, 20) & X"0" & conv_std_logic_vector(i, 5) & "000", 
    --                    X"08000000", 8, 16#1234#, X"00000000" & X"CCCCD000", IbCmd);
   --end loop; 

   wait for 5*CLKPER;
      
   -- Send data to 2nd channel (BLOCK_SIZE-1 to FIFO, but last one to REG_ARRAY - implicit behavior)
   --for i in 0 to (BLOCK_SIZE-1) loop 
   --   SendLocalWrite(   X"000020" & conv_std_logic_vector(i, 5) & "000", 
   --                     X"08000000", 8, 16#1234#, X"00000000" & X"CCCCD000", IbCmd); 
   --end loop;

   wait for 5*CLKPER;

   -- enable next_desc_logic
   enable <= enable_1;                             -- enable all channels
   --enable <= enable_0(31 downto 2) & '1' & '0'; -- enable only channel 1

   wait for 5*CLKPER;
   
	wait;
	 
end process;

-- DMA simulate read process
dma_read : process
begin
    read <= conv_std_logic_vector(0, read'length);
    for i in 0 to (FLOWS-1) loop
      if(EMPTY(i) = '0' and ENABLE(i) = '1') then
         read <= conv_std_logic_vector(i, read'length);
      end if;
    end loop;
    
   wait for DMAWORKTIME;

end process;

-- CLK clock generator
clkgen_CLK: process
begin
  		CLK <= '1';
  		wait for CLKPER/2;
  		CLK <= '0';
  		wait for CLKPER/2;
end process;

end architecture behavioral;
------------------------------------------------------------------------------


