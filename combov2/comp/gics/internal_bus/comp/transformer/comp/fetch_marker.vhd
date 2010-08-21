--
-- fetch_marker.vhd : IB Transformer Fetch Marker
-- Copyright (C) 2008 CESNET
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
-- TODO:
--

library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

use work.math_pack.all;
use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 
use work.ib_transformer_pkg.all;

-- ----------------------------------------------------------------------------
--              ENTITY DECLARATION -- IB Transformer Fetch Marker            -- 
-- ----------------------------------------------------------------------------

entity IB_TRANSFORMER_FETCH_MARKER is 
   generic(
      -- Input Data Width (1-128)
      IN_DATA_WIDTH   : integer := 64;
      -- Output Data Width (1-128)
      OUT_DATA_WIDTH  : integer :=  8   
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK             : in std_logic;  
      RESET           : in std_logic;  

      -- IB interface ---------------------------------------------------------
      SOF_N           : in std_logic;   
      EOF_N           : in std_logic;            
      SRC_RDY_N       : in std_logic;
      DST_RDY_N       : in std_logic;

      -- Control Interface ----------------------------------------------------
      LEN_ALIGN_WE    : out std_logic_vector(align_we_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0);      
      ADDR_ALIGN_WE   : out std_logic_vector(align_we_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0);
      PAYLOAD_FLAG_WE : out std_logic;
      REG_DATA_WE     : out std_logic;
      HEADER_LAST     : out std_logic
   );
end IB_TRANSFORMER_FETCH_MARKER;

-- ----------------------------------------------------------------------------
--         ARCHITECTURE DECLARATION  --  IB Transformer Fetch Marker         --
-- ----------------------------------------------------------------------------

architecture ib_transformer_fetch_marker_arch of IB_TRANSFORMER_FETCH_MARKER is

   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------

   constant CNT_WIDTH : integer := log2(128/IN_DATA_WIDTH);
   constant ONES      : std_logic_vector(CNT_WIDTH-1 downto 0) := (others => '1');
   
   constant ALIGN_PARTS_NUM  : integer := align_we_width(IN_DATA_WIDTH,OUT_DATA_WIDTH); 
   
   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal transfer_cnt_ce : std_logic;  
   signal transfer_cnt    : std_logic_vector(CNT_WIDTH-1 downto 0);
                                                                                                   
begin

   -- -------------------------------------------------------------------------
   --                            TRANSFER COUNTER                            --
   -- -------------------------------------------------------------------------

   CNT_GEN: if (IN_DATA_WIDTH < 128) generate

      transfer_cntp: process (CLK) 
      begin
         if (CLK = '1' and CLK'event) then
            if (RESET = '1') then 
               transfer_cnt <= (others => '0');         
            elsif (transfer_cnt_ce = '1') then  
               transfer_cnt <= transfer_cnt + 1;
            end if;
         end if;
      end process;
      
      transfer_cnt_cep: process (transfer_cnt, EOF_N, SRC_RDY_N, DST_RDY_N)
      begin
         if (transfer_cnt = ONES) then
            transfer_cnt_ce <= not (EOF_N or SRC_RDY_N or DST_RDY_N);
         else
            transfer_cnt_ce <= not (SRC_RDY_N or DST_RDY_N);
         end if;
      end process;

   end generate;                      

   -- -------------------------------------------------------------------------
   --                         HEADER LAST DETERMINATION                      --
   -- -------------------------------------------------------------------------

   HEADER_LAST_LT128: if (IN_DATA_WIDTH < 128) generate
      process (transfer_cnt, SRC_RDY_N)
      begin
         if ((transfer_cnt = ONES) and (SRC_RDY_N = '0')) then
            HEADER_LAST <= '1';
         else
            HEADER_LAST <= '0';
         end if;
      end process;
   end generate;

   HEADER_LAST_EQ128: if (IN_DATA_WIDTH = 128) generate      
      HEADER_LAST <= not SOF_N;
   end generate;

   -- -------------------------------------------------------------------------
   --                 PAYLOAD FLAG WRITE ENABLE DETERMINATION                --
   -- -------------------------------------------------------------------------

   PAYLOAD_FLAG_WE <= not SOF_N and not DST_RDY_N;

   -- -------------------------------------------------------------------------
   --                 DATA REGISTER WRITE ENABLE DETERMINATION               --
   -- -------------------------------------------------------------------------

   REG_DATA_WE    <= not SRC_RDY_N and not DST_RDY_N;   

   -- -------------------------------------------------------------------------
   --              ADDRESS ALIGNMENT WRITE ENABLES DETERMINATION             --
   -- -------------------------------------------------------------------------

   ADDR_ALIGN_WE_GE64: if (IN_DATA_WIDTH >= 64) generate
      ADDR_ALIGN_WE(0) <= not SOF_N and not DST_RDY_N;
   end generate;


   ADDR_ALIGN_WE_LT64: if (IN_DATA_WIDTH < 64) generate
      ADDR_ALIGN_WE_FOR : for i in 0 to ALIGN_PARTS_NUM-1 generate
         process (transfer_cnt, SRC_RDY_N, DST_RDY_N)
         begin
            if ((transfer_cnt = (32/IN_DATA_WIDTH + i)) and (SRC_RDY_N = '0') and (DST_RDY_N = '0')) then
               ADDR_ALIGN_WE(i) <= '1';
            else
               ADDR_ALIGN_WE(i) <= '0';
            end if;
         end process;
      end generate;
   end generate;

   -- -------------------------------------------------------------------------
   --               LENGTH ALIGNMENT WRITE ENABLES DETERMINATION             --
   -- -------------------------------------------------------------------------

   LEN_ALIGN_WE_GE64: if (IN_DATA_WIDTH >= 8) generate
      LEN_ALIGN_WE(0) <= not SOF_N and not DST_RDY_N;
   end generate;


   LEN_ALIGN_WE_LT64: if (IN_DATA_WIDTH < 8) generate
      LEN_ALIGN_WE_FOR : for i in 0 to ALIGN_PARTS_NUM-1 generate
         process (transfer_cnt, SRC_RDY_N, DST_RDY_N)
         begin
            if ((transfer_cnt = (4/IN_DATA_WIDTH + i)) and (SRC_RDY_N = '0') and (DST_RDY_N = '0')) then
               LEN_ALIGN_WE(i) <= '1';
            else
               LEN_ALIGN_WE(i) <= '0';
            end if;
         end process;
      end generate;
   end generate;   

end ib_transformer_fetch_marker_arch;



