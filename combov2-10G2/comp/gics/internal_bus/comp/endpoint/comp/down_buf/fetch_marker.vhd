--
-- fetch_marker.vhd : IB Endpoint Down Buffer Fetch Marker
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
use work.ib_endpoint_pkg.all;

-- ----------------------------------------------------------------------------
--         ENTITY DECLARATION -- IB Endpoint Down Buffer Fetch Marker        -- 
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_DOWN_BUF_FETCH_MARKER is 
   generic(
      -- Data Width (8-128)
      DATA_WIDTH   : integer:= 64
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK           : in std_logic;  
      RESET         : in std_logic;  

      -- IB interface ---------------------------------------------------------
      SOF_N         : in std_logic;   
      EOF_N         : in std_logic;            
      SRC_RDY_N     : in std_logic;
      DST_RDY_N     : in std_logic;

      -- Control Interface ----------------------------------------------------
      TAG_VLD       : out std_logic;
      TYPE_VLD      : out std_logic;
      SRC_ADDR_VLD  : out std_logic;
      DST_ADDR_VLD  : out std_logic
   );
end IB_ENDPOINT_DOWN_BUF_FETCH_MARKER;

-- ----------------------------------------------------------------------------
--      ARCHITECTURE DECLARATION  --  IB Endpoint Down Buffer Fetch Marker   --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_down_buf_fetch_marker_arch of IB_ENDPOINT_DOWN_BUF_FETCH_MARKER is

   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------

   constant CNT_WIDTH : integer := log2(128/DATA_WIDTH);
   constant ONES      : std_logic_vector(CNT_WIDTH-1 downto 0) := (others => '1');
   
   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal transfer_cnt_ce : std_logic;  
   signal transfer_cnt    : std_logic_vector(CNT_WIDTH-1 downto 0);
                                                                                                   
begin

   -- -------------------------------------------------------------------------
   --            SIGNALS GENERATED ONLY FOR DATA_WIDTH = 8/16/32             --
   -- -------------------------------------------------------------------------
   DATA_WIDTH_GEN: if (DATA_WIDTH <= 32) generate   

      -- TRANSFER COUNTER -----------------------------------------------------
      
      transfer_cntp: process (CLK, RESET) 
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

      -- TIME MARK GENERATION -------------------------------------------------
      
      process (transfer_cnt)
      begin
         TAG_VLD      <= '0';
         SRC_ADDR_VLD <= '0';
         DST_ADDR_VLD <= '0';
         if (transfer_cnt = CNT_WIDTH-2) then
            TAG_VLD <= '1';
         end if;
         if (transfer_cnt(CNT_WIDTH-1 downto CNT_WIDTH-2) = "01") then
            SRC_ADDR_VLD <= '1';
         end if;
         if (transfer_cnt(CNT_WIDTH-1 downto CNT_WIDTH-2) = "10") then
            DST_ADDR_VLD <= '1';
         end if;
      end process;

      TYPE_VLD     <= not SOF_N;

      -- DATA_WIDTH=8 -> CNT_WIDTH=4     DATA_WIDTH=16 -> CNT_WIDTH=3     DATA_WIDTH=32 -> CNT_WIDTH=2
      --    TAG: 0010                       TAG: 001                         TAG: 00
      --                                                                             
      --    SRC: 0100                       SRC: 010                         SRC: 01
      --         0101                            011                              
      --         0110                                                             
      --         0111                                                             
      --                                                                             
      --    DST: 1000                       DST: 100                         DST: 10
      --         1001                            101                              
      --         1010                            
      --         1011                            
      
   end generate;
    
end ib_endpoint_down_buf_fetch_marker_arch;

                     

