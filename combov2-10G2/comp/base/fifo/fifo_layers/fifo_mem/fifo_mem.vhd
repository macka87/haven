--
-- fifo_mem.vhd: FIFO full architecture
-- Copyright (C) 2004 CESNET
-- Author(s): Jan Kastil <xkasti00@stud.fit.vutbr.cz>
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the OpenIPCore Hardware General Public
-- License as published by the OpenIPCore Organization; either version
-- 0.20-15092000 of the License, or (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful, but
-- WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- OpenIPCore Hardware General Public License for more details.
--
-- You should have received a copy of the OpenIPCore Hardware Public
-- License along with this program; if not, download it from
-- OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Cache package
use work.fifo_pkg.all;

-- Math package - log2 function
use work.math_pack.all;

use work.bmem_func.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FIFO_MEM is
--type Latency_Valid_Array is array (0 to latency-1 of std_logic);
type Latency_Data_Array is array (0 to latency-1) of std_logic_vector(item_width-1 downto 0);
type latency_Address_Array is array (0 to latency-1) of std_logic_vector(log2(items)-1 downto 0);

signal Data_Ready : std_logic;
signal Data : std_logic_vector(item_width-1 downto 0);
signal Data1 : std_logic_vector(item_width-1 downto 0);
signal D : std_logic;
signal D_Data : std_logic_vector(item_width-1 downto 0);
signal Data_Ready1 :std_logic;
signal Data_Ready2 :std_logic;
signal Address : std_logic_vector(log2(items)-1 downto 0);
signal AddressD : std_logic_vector(log2(items)-1 downto 0);

signal LatencyRegValid : std_logic_vector(latency-1 downto 0);
signal latencyRegAddress : Latency_Address_Array;
signal LatencyRegData : Latency_Data_Array;

signal gnd_item : std_logic_vector(ITEM_WIDTH-1 downto 0);
 
begin

	-- EDIT Lukas Solanka
	-- XST Problems - xst recognizes (others => '0') in port map as unconstrained
	-- path. Needs to be specified by constrained signal
	gnd_item <= (others => '0');

   LUT_GENERATE: if (mem_type = LUT) generate
   --This is FIFO from LUT
   MEM : entity work.DP_DISTMEM(behavioral)
      generic map (
         DATA_WIDTH =>item_width,
         ITEMS => items,
         DISTMEM_TYPE => 16,
         DEBUG => false
         )
      port map (
         RESET => reset,
         DI => DI,
         WCLK => clkw,
         ADDRA => WRITE_ADDR,
         DOA => open,
         WE => WRITE_EN,
         ADDRB => RE_ADDR,
         DOB => Data1
         );

   Data_Ready1 <= READ_EN;

   -- EDIT Jan Koritak
   -- Removed registers taking care of undefined signals
   -- Undefined signals were caused by undefined inputs in testbench

   D_Register2 : process(clkr, reset, PIPE_EN)
   begin
      if(reset='1') then 
         Data_Ready <= '0';
      else if(clkr'event and clkr ='1') then
	     if(PIPE_EN = '1') then 
            Data_Ready <= Data_Ready1;
	     end if;
      end if;
      end if;
   end process;       

   D_Register_Data1: process (clkr, reset, PIPE_EN)
   begin
      if(RESET = '1') then
         Data <= (others => '0');
      else if(clkr'event and clkr = '1') then
         if(Data_Ready1 = '1') then 
		    if(PIPE_EN = '1') then 
               Data <= Data1;
			end if;
         end if;
      end if;
      end if;   
   end process;

   end generate;
   BRAM_GENERATE: if (mem_type = BRAM) generate
   --This is FIFO from BlockRam
   MEM : entity work.DP_BMEM
      generic map (
         DATA_WIDTH => item_width,
         ITEMS => items,
         BRAM_TYPE => GET_BRAM_TYPE(item_width,items),
         OUTPUT_REG => false,
         DEBUG => false
      )
      port map(
         RESET => RESET,
         CLKA => CLKW,
         PIPE_ENA => '1',  --We do not use output register
         REA => '0',  --We do not want to read from A
         WEA => WRITE_EN,
         ADDRA => WRITE_ADDR,
         DIA => DI,
         DOA_DV => open,   --We do not read from port A
         DOA => open,
	 
         CLKB => CLKR,
         PIPE_ENB => PIPE_EN, --'1',
         REB => READ_EN,
         WEB => '0',
         ADDRB => RE_ADDR,
         DIB => gnd_item,
         DOB_DV => Data_Ready,
         DOB => Data
      );

   -- EDIT Jan Koritak
   -- Removed registers taking care of undefined signals
   -- Undefined signals were caused by undefined inputs in testbench

   end generate;
  
   AddressDReg: process(clkr)  --There is no need for reset, because valid value can be only with Data_valid, which is reseted
   begin
      if(clkr'event and clkr = '1') then
	     if(PIPE_EN = '1' and READ_EN = '1') then
	        AddressD <= RE_ADDR;
		 end if;
	  end if;
   end process;
  
   AddressReg: process(clkr)  --There is no need for reset, because valid value can be only with Data_valid, which is reseted
   begin
      if(clkr'event and clkr = '1') then
	     if(PIPE_EN = '1') then
	        Address <= AddressD;
		 end if;
	  end if;
   end process;

   LATENCY_ADDR_GEN: if(latency > 1) generate
      LATENCY_ADDR_LOOP: for i in 0 to (latency-2) generate
	     process(clkr)
	     begin
			if (clkr'event and clkr = '1') then
			   if(PIPE_EN = '1') then
			      if(i=0) then
				     LatencyRegAddress(i) <= AddressD;
			      else
				     LatencyRegAddress(i) <= LatencyRegAddress(i-1);
				  end if;
			   end if;
			end if;
		end process;
      end generate;
   end generate;

   LATENCY_GEN : if (latency > 1) generate
      LATENCY_LOOP :for i in 0 to (latency-2) generate
         process(clkr,reset)
         begin
            if(reset = '1') then 
            LatencyRegValid(i) <= '0';
            else if (clkr'event and clkr='1') then
			   if(PIPE_EN = '1') then
                  if(i=0) then LatencyRegValid(i) <= Data_Ready;
                  else LatencyRegValid(i) <= LatencyRegValid(i-1);
				  end if;
               end if;
            end if;
            end if;
         end process;
      end generate;
   end generate;
   LATENCY_DATA_GEN : if( latency > 1) generate
      LATENCY_DATA_LOOP: for i in 0 to (latency-2) generate
         process(clkr, reset)
         begin
            if(reset = '1') then
               LatencyRegData(i) <= (others => '0');
            else if (clkr'event and clkr='1') then
			   if(PIPE_EN = '1') then
                  if(i=0) then 
                     LatencyRegData(i) <= Data;
                  else LatencyRegData(i) <= LatencyRegData(i-1);
                  end if;
			   end if;
            end if;
            end if;
         end process;
      end generate;
   end generate;
   GEN_OUTPUT: if(latency > 1 ) generate
      DO_DV <= LatencyRegValid(latency-2);
      DO <= LatencyRegData(latency-2); 
	  ADDR_OUT <= LatencyRegAddress(latency -2);
   end generate;
   GEN_OUTPUT2: if(latency = 1) generate
      DO_DV <= Data_Ready;
	  ADDR_OUT <= AddressD;
      DO <= Data;
   end generate;

end architecture full;
