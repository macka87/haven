--
-- tb_align_unit,vhd: For whole design testing
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
-- TODO: Run tests with various DATA_LEN!
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   signal clk        	: std_logic;
   signal reset      	: std_logic;

   signal src_addr   	: std_logic_vector(2 downto 0);
   signal dst_addr   	: std_logic_vector(2 downto 0);
   signal data_len   	: std_logic_vector(2 downto 0);

   signal in_data    	: std_logic_vector(63 downto 0);
   signal in_sof     	: std_logic;
   signal in_eof        : std_logic;
   signal in_src_rdy	   : std_logic;
   signal in_dst_rdy	   : std_logic;

   signal out_data    	: std_logic_vector(63 downto 0);
   signal out_sof     	: std_logic;
   signal out_eof       : std_logic;
   signal out_src_rdy	: std_logic;
   signal out_dst_rdy	: std_logic;

   constant clkper      : time         := 10 ns;
   signal test_data     : std_logic_vector(7 downto 0) := X"00";

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

uut : entity work.ALIGN_UNIT
	port map(
      -- Common interface -----------------------------------------------------
      CLK           => clk, 
      RESET         => reset,  

      -- Control interface ----------------------------------------------------    
      SRC_ADDR      => src_addr, 
      DST_ADDR      => dst_addr, 
      DATA_LEN      => data_len,  

      -- Input interface ------------------------------------------------------
      IN_DATA       => in_data,
      IN_SOF        => in_sof,
      IN_EOF        => in_eof,
      IN_SRC_RDY    => in_src_rdy,
      IN_DST_RDY    => in_dst_rdy,      

      -- Output interface -----------------------------------------------------
      OUT_DATA      => out_data,
      OUT_SOF       => out_sof,
      OUT_EOF       => out_eof,      
      OUT_SRC_RDY   => out_src_rdy,      
      OUT_DST_RDY   => out_dst_rdy
	);

-- ----------------------------------------------------
-- CLK clock generator
clkgen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

tb : process
begin

   -- RESET ACTIVE ------------------------------------------------------------
	reset      <= '1';
   src_addr   <= (others => '0');
   dst_addr   <= (others => '0');
   data_len   <= (others => '0');
   in_data    <= (others => '0');
   in_sof     <= '0';
   in_eof     <= '0';
   in_src_rdy <= '0';
   out_dst_rdy<= '0';
   wait for clkper/50;


   -- RESET DOWN --------------------------------------------------------------
	reset      <= '0';
   src_addr   <= (others => '0');
   dst_addr   <= (others => '0');
   data_len   <= (others => '0');
   in_data    <= (others => '0');
   in_sof     <= '0';
   in_eof     <= '0';
   in_src_rdy <= '0';
   out_dst_rdy<= '0';
	wait for clkper;
	
   
   -- FIRST FRAME -------------------------------------------------------------
   src_addr   <= conv_std_logic_vector(0, src_addr'length);
 	dst_addr   <= conv_std_logic_vector(0, dst_addr'length);
	data_len   <= conv_std_logic_vector(16, data_len'length);
	in_data    <= X"0011223344556677"; 
	in_sof     <= '1';
   in_eof     <= '0';
   in_src_rdy <= '1';
   out_dst_rdy<= '1';
	wait for clkper;


   -- LAST FRAME --------------------------------------------------------------
	src_addr   <= conv_std_logic_vector(0, src_addr'length);
 	dst_addr   <= conv_std_logic_vector(0, dst_addr'length);
	data_len   <= conv_std_logic_vector(16, data_len'length);
	in_data    <= X"9911223344556677";
	in_sof     <= '0';
   in_eof     <= '1';
   in_src_rdy <= '1';
   out_dst_rdy<= '1';
	wait for clkper;
   
   -- STOP INPUT and OUTPUT ---------------------------------------------------
   in_sof         <= '0';
   in_eof         <= '0';
   in_src_rdy     <= '0';
   out_dst_rdy    <= '1';  -- wait for last

	wait for clkper;
   out_dst_rdy    <= '0';  -- last


-- 	in_sof	<= '0';
-- 	for i in 1 to 2 loop
--       test_data <= conv_std_logic_vector(i, 8);  

--		   in_data <= conv_std_logic_vector(i, in_data'length);

-- 		if(i = 3) then
-- 			out_dst_rdy <= '0';
-- 		else
-- 			out_dst_rdy <= '1';
-- 		end if;
			
--       in_data <= X"01234567ABCDEF" & test_data;
-- 	  	wait for clkper;
-- 	end loop;
-- 	
-- 	in_data <= conv_std_logic_vector(1023, in_data'length);
--    in_eof  <= '1';
-- 	wait for clkper;
-- 		  
-- 	in_eof     <= '0';
--    --out_dst_rdy<= '1';
-- 	in_src_rdy <= '0';
-- 
-- 	-- next frame
--    wait until (in_dst_rdy = '1');
--    wait for clkper/20;
-- 
-- 	src_addr   <= conv_std_logic_vector(1, src_addr'length);
--  	dst_addr   <= conv_std_logic_vector(1, dst_addr'length);
-- 	data_len   <= conv_std_logic_vector(0, data_len'length);
-- 	in_data    <= conv_std_logic_vector(1023, in_data'length);
-- 	in_sof     <= '1';
--    in_eof     <= '0';
--    in_src_rdy <= '1';
--    out_dst_rdy<= '1';
-- 	wait for clkper;
-- 
-- 	in_sof	<= '0';
-- 	for i in 1 to 10 loop
--       test_data <= conv_std_logic_vector(i, 8);  
-- 		-- in_data <= conv_std_logic_vector(i, in_data'length);
-- 
-- -- 		if(i = 3) then
-- -- 			out_dst_rdy <= '0';
-- -- 		else
-- -- 			out_dst_rdy <= '1';
-- -- 		end if;
-- 			
--       in_data <= X"01234567ABCDEF" & test_data;
-- 	  	wait for clkper;
-- 	end loop;
-- 	
-- 	in_data <= conv_std_logic_vector(1023, in_data'length);
--    in_eof  <= '1';
-- 	wait for clkper;
-- 		  
-- 	in_eof     <= '0';
--    --out_dst_rdy<= '1';
-- 	in_src_rdy <= '0';
-- 
--    wait for clkper*10;
--    
--    -- next frame (address)
--    
--    src_addr   <= conv_std_logic_vector(0, src_addr'length);
--  	dst_addr   <= conv_std_logic_vector(0, dst_addr'length);
-- 	data_len   <= conv_std_logic_vector(0, data_len'length);
-- 	in_data    <= conv_std_logic_vector(1111, in_data'length);
-- 	in_sof     <= '1';
--    in_eof     <= '0';
--    in_src_rdy <= '1';
--    --out_dst_rdy<= '1';
-- 	wait for clkper;
--    
--    src_addr   <= conv_std_logic_vector(0, src_addr'length);
--  	dst_addr   <= conv_std_logic_vector(0, dst_addr'length);
-- 	data_len   <= conv_std_logic_vector(0, data_len'length);
-- 	in_data    <= conv_std_logic_vector(2222, in_data'length);
-- 	in_sof     <= '0';
--    in_eof     <= '1';
--    in_src_rdy <= '1';
--    --out_dst_rdy<= '1';
-- 	wait for clkper;
-- 
--    -- next frame (data)
--    
--    src_addr   <= conv_std_logic_vector(0, src_addr'length);
--  	dst_addr   <= conv_std_logic_vector(0, dst_addr'length);
-- 	data_len   <= conv_std_logic_vector(0, data_len'length);
-- 	in_data    <= conv_std_logic_vector(3333, in_data'length);
-- 	in_sof     <= '1';
--    in_eof     <= '0';
--    in_src_rdy <= '1';
--    --out_dst_rdy<= '1';
-- 	wait for clkper;
--    
--    src_addr   <= conv_std_logic_vector(0, src_addr'length);
--  	dst_addr   <= conv_std_logic_vector(0, dst_addr'length);
-- 	data_len   <= conv_std_logic_vector(0, data_len'length);
-- 	in_data    <= conv_std_logic_vector(4444, in_data'length);
-- 	in_sof     <= '0';
--    in_eof     <= '1';
--    in_src_rdy <= '1';
--    --out_dst_rdy<= '1';
-- 	wait for clkper;
-- 
--    --in_eof     <= '0';
--    --out_dst_rdy<= '1';
-- 	--in_src_rdy <= '0';
-- 
--    --wait for clkper*10;
-- 
-- 
--    -- TEST EOF AND SOF TOGETHER
-- 
--    src_addr   <= conv_std_logic_vector(0, src_addr'length);
--  	dst_addr   <= conv_std_logic_vector(0, dst_addr'length);
-- 	data_len   <= conv_std_logic_vector(0, data_len'length);
-- 	in_data    <= conv_std_logic_vector(5555, in_data'length);
-- 	in_sof     <= '1';
--    in_eof     <= '1';
--    in_src_rdy <= '1';
--    --out_dst_rdy<= '1';
-- 	wait for clkper;
-- 
--    in_sof     <= '0';
--    in_eof     <= '0';
--    out_dst_rdy<= '1';
-- 	in_src_rdy <= '0';


	wait;

end process;

-- ----------------------------------------------------------------------------
end architecture behavioral;
