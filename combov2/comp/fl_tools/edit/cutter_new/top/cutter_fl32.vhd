-- cutter_fl32.vhd: 32b cover for cutter
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03 at stud.fit.vutbr.cz>
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
-- TODO:
--
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FL_CUTTER_FL32 is
   generic (  
      DATA_WIDTH	: integer := 32;	-- width of data word
      PART		: integer :=  0;	-- index of processed part (0 = first part)
      EXT_OFFSET	: integer :=  0;	-- index of first extracted byte
      EXT_SIZE		: integer :=  1;	-- num of extracted bytes ( >=1 )
      CUT_OFFSET	: integer :=  0;	-- index of first removed word
      CUT_SIZE		: integer :=  0		-- num of removed words ( 0 = no word is removed )
   );
   port (
      CLK		: in std_logic;
      RESET		: in std_logic;

      -- intput interface
      RX_DATA		: in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM		: in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SRC_RDY_N	: in std_logic;
      RX_DST_RDY_N	: out std_logic;
      RX_SOP_N		: in std_logic;
      RX_EOP_N		: in std_logic;
      RX_SOF_N		: in std_logic;
      RX_EOF_N		: in std_logic;

      -- output interface
      TX_DATA		: out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM		: out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N	: out std_logic;
      TX_DST_RDY_N	: in std_logic;
      TX_SOP_N		: out std_logic;
      TX_EOP_N		: out std_logic;
      TX_SOF_N		: out std_logic;
      TX_EOF_N		: out std_logic;

      -- extracted data
      EXTRACTED_DATA	: out std_logic_vector(EXT_SIZE*8 - 1 downto 0);
      EXTRACTED_DONE	: out std_logic;
      EXTRACTED_ERR	: out std_logic
   );
end entity FL_CUTTER_FL32;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_CUTTER_FL32 is
begin
   FL_CUTTER_I: entity work.fl_cutter
      generic map(
         DATA_WIDTH	=> DATA_WIDTH,
         PART	        => PART,
         EXT_OFFSET	=> EXT_OFFSET,
         EXT_SIZE	=> EXT_SIZE,
         CUT_OFFSET	=> CUT_OFFSET,
         CUT_SIZE	=> CUT_SIZE
      )
      port map(
          CLK          => CLK,
          RESET        => RESET,
          
          RX_DATA      => RX_DATA,
          RX_REM       => RX_REM,
          RX_SRC_RDY_N => RX_SRC_RDY_N,
          RX_DST_RDY_N => RX_DST_RDY_N,
          RX_SOP_N     => RX_SOP_N,
          RX_EOP_N     => RX_EOP_N,
          RX_SOF_N     => RX_SOF_N,
          RX_EOF_N     => RX_EOF_N,
          
          TX_DATA      => TX_DATA,
          TX_REM       => TX_REM,
          TX_SRC_RDY_N => TX_SRC_RDY_N,
          TX_DST_RDY_N => TX_DST_RDY_N,
          TX_SOP_N     => TX_SOP_N,
          TX_EOP_N     => TX_EOP_N,
          TX_SOF_N     => TX_SOF_N,
          TX_EOF_N     => TX_EOF_N,
          
          EXTRACTED_DATA  => EXTRACTED_DATA,
          EXTRACTED_DONE  => EXTRACTED_DONE,
          EXTRACTED_ERR   => EXTRACTED_ERR
      );
   
end architecture full;
