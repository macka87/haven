-- V5_CRC.vhd: Virtex 5 architecture embeded CRC block with some generics
-- Copyright (C) 2010 CESNET
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
--

library IEEE;
use IEEE.std_logic_1164.all;

-- synthesis translate_off
library unisim;
use unisim.all;
-- synthesis translate_on

-- ----------------------------------------------------------------------------
--                      Entity declaration
-- ----------------------------------------------------------------------------
entity v5_crc is
	generic(
      -- input register pipe
      INPUT_PIPE        : boolean := false;                   
      -- output register pipe
      OUTPUT_PIPE       : boolean := false;                    
      -- input CRC32 data width, only 32 or 64
      INPUT_WIDTH       : integer := 32;               
      -- CRC module init value
      CRC_INIT          : bit_vector := X"FFFFFFFF"
   );
	port(

      -- Common interface -----------------------------------------------------
      -- clock synchronization
      CLK         : in std_logic;
   
      -- Input interface ------------------------------------------------------
      -- reset input used to load init value before start
      CRCRESET       : in std_logic;
      -- data input 
      DATA_IN     : in std_logic_vector(INPUT_WIDTH-1 downto 0);
      -- input data valid
      DATA_VLD    : in std_logic;
      -- input data width
      DATA_WIDTH  : in std_logic_vector( 2 downto 0);
      -- 000 : 1st input byte is only valid (7 downto 0)
      -- 001 : 1st and 2nd input byte is valid (15 downto 0)
      -- 010 : 1st, 2nd and 3rd input byte valid (23 downto 0)
      -- 011 : 1st, 2nd, 3rd and 4th input byte valid (all 32 bits are valid)
      -- ... : other combinations are don't care for 32 bit input, but not for 64 bit input...
      -- ...
      -- 110 : only last byte is not valid (if 64 bit input)
      -- 111 : all 8 bytes are all valid (if 64 bit input)

      -- Output Interface -----------------------------------------------------
      CRC_OUT    : out std_logic_vector( 31 downto 0)
   );
end v5_crc;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of v5_crc is

   ----- CRC 32 component Instantiation -----
   component CRC32
      generic
      (
         CRC_INIT : bit_vector := X"FFFFFFFF"
      );
      port
      (
         CRCOUT         : out std_logic_vector(31 downto 0);
         CRCCLK         : in std_logic;
         CRCDATAVALID   : in std_logic;
         CRCDATAWIDTH   : in std_logic_vector(2 downto 0);
         CRCIN          : in std_logic_vector(31 downto 0);
         CRCRESET       : in std_logic
      );
   end component;

   ---- CRC 64 component Instantiation -----
   component CRC64
      generic
      (
         CRC_INIT : bit_vector := X"FFFFFFFF"
      );
      port
      (
         CRCOUT         : out std_logic_vector(31 downto 0);
         CRCCLK         : in std_logic;
         CRCDATAVALID   : in std_logic;
         CRCDATAWIDTH   : in std_logic_vector(2 downto 0);
         CRCIN          : in std_logic_vector(63 downto 0);
         CRCRESET       : in std_logic
      );
   end component;

	-- registers
   signal reset_reg        : std_logic := '0';
   signal data_in_reg      : std_logic_vector(INPUT_WIDTH-1 downto 0);
   signal data_vld_reg     : std_logic := '0';
   signal data_width_reg   : std_logic_vector(2 downto 0);
   signal crc_out_reg      : std_logic_vector(31 downto 0);
	
	-- component mapping
   signal reset_sig        : std_logic;
   signal data_in_sig      : std_logic_vector(INPUT_WIDTH-1 downto 0);
   signal data_vld_sig     : std_logic;
   signal data_width_sig   : std_logic_vector(2 downto 0);
   signal crc_out_sig      : std_logic_vector(31 downto 0);

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- input registers enabled -------------------------------------------------
   GENINPIPE : if(INPUT_PIPE) generate
      -- register reset_regp --------------------------------------------------
      reset_regp: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
               reset_reg <= CRCRESET;
         end if;
      end process;

      -- register data_in_regp ------------------------------------------------
      data_in_regp: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
               data_in_reg <= DATA_IN;
         end if;
      end process;
      
      -- register data_vld_regp -----------------------------------------------
      data_vld_regp: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
               data_vld_reg <= DATA_VLD;
         end if;
      end process;

      -- register data_width_regp ---------------------------------------------
      data_width_regp: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
               data_width_reg <= DATA_WIDTH;
         end if;
      end process;
   
      -- input mapping 
      reset_sig        <= reset_reg;
      data_in_sig      <= data_in_reg;
      data_vld_sig     <= data_vld_reg;
      data_width_sig   <= data_width_reg;
      end generate;

   -- input registers not enabled ---------------------------------------------
   NOGENINPIPE : if(not INPUT_PIPE) generate
      reset_sig        <= CRCRESET;
      data_in_sig      <= DATA_IN;
      data_vld_sig     <= DATA_VLD;
      data_width_sig   <= DATA_WIDTH;
   end generate;


   -- 32 bit input ------------------------------------------------------------
   GEN32IN : if (INPUT_WIDTH = 32) generate
      -- CRC block ------------------------------------------------------------
		CRC : CRC32
		generic map(
	      CRC_INIT       => CRC_INIT)
		port map(
	      CRCOUT         =>   crc_out_sig,
	      CRCCLK         =>   CLK,
	      CRCDATAVALID   =>   data_vld_sig,
	      CRCDATAWIDTH   =>   data_width_sig,
	      CRCIN          =>   data_in_sig,
	      CRCRESET       =>   reset_sig
		);
   end generate;

   -- 64 bit input ------------------------------------------------------------
   GEN64IN : if (INPUT_WIDTH = 64) generate
      -- CRC block ------------------------------------------------------------
		CRC : CRC64
		generic map(
	      CRC_INIT       => CRC_INIT)
		port map(
	      CRCOUT         =>   crc_out_sig,
	      CRCCLK         =>   CLK,
	      CRCDATAVALID   =>   data_vld_sig,
	      CRCDATAWIDTH   =>   data_width_sig,
	      CRCIN          =>   data_in_sig,
	      CRCRESET       =>   reset_sig
		);
   end generate;

   -- output registers enabled ------------------------------------------------
   GENOUTPIPE : if(OUTPUT_PIPE) generate
      -- register crc_out_regp ------------------------------------------------
      crc_out_regp: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
               crc_out_reg <= crc_out_sig;
         end if;
      end process;

      CRC_OUT <= crc_out_reg;
   end generate;
      
   -- output registers not enabled --------------------------------------------
   NOGENOUTPIPE : if(not OUTPUT_PIPE) generate
         CRC_OUT <= crc_out_sig;
   end generate;

end full;
