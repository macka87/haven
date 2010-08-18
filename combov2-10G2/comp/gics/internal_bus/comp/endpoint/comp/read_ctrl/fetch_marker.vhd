--
-- fetch_marker.vhd : IB Endpoint Read Controller Fetch Marker
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
--       ENTITY DECLARATION -- IB Endpoint Read Controller Fetch Marker      -- 
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_READ_CTRL_FETCH_MARKER is 
   generic(
      -- Data Width (8-128)
      DATA_WIDTH    : integer:= 64;
      -- Address Width (1-32)
      ADDR_WIDTH    : integer:= 32      
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
      LENGTH_WE     : out std_logic_vector(length_we_width(DATA_WIDTH)-1 downto 0);      
      ADDR32_WE     : out std_logic_vector(addr_we_width(DATA_WIDTH, ADDR_WIDTH)-1 downto 0);                  
      ADDR64_WE     : out std_logic_vector(addr_we_width(DATA_WIDTH, ADDR_WIDTH)-1 downto 0);                        
      TAG_WE        : out std_logic;
      DONE_FLAG_WE  : out std_logic;
      TRANSFER      : out std_logic;
      HEADER_LAST   : out std_logic      
   );
end IB_ENDPOINT_READ_CTRL_FETCH_MARKER;

-- ----------------------------------------------------------------------------
--   ARCHITECTURE DECLARATION  --  IB Endpoint Read Controller Fetch Marker  --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_read_ctrl_fetch_marker_arch of IB_ENDPOINT_READ_CTRL_FETCH_MARKER is

   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------

   constant CNT_WIDTH : integer := log2(128/DATA_WIDTH);
   constant ONES      : std_logic_vector(CNT_WIDTH-1 downto 0) := (others => '1');
   
   constant ADDR_PARTS_NUM : integer := addr_we_width(DATA_WIDTH, ADDR_WIDTH);    
   
   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal transfer_cnt_ce : std_logic;  
   signal transfer_cnt    : std_logic_vector(CNT_WIDTH-1 downto 0);
                                                                                                   
begin

   -- -------------------------------------------------------------------------
   --                            TRANSFER COUNTER                            --
   -- -------------------------------------------------------------------------

   CNT_GEN: if (DATA_WIDTH < 128) generate

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

      transfer_cnt_ce <= not SRC_RDY_N and not DST_RDY_N;

   end generate;                      

   -- -------------------------------------------------------------------------
   --                    LENGTH WRITE ENABLES DETERMINATION                  --
   -- -------------------------------------------------------------------------                  
     
   LENGTH_WE_GT8: if (DATA_WIDTH > 8) generate
      LENGTH_WE(0) <= not SOF_N and not DST_RDY_N;
   end generate;

   LENGTH_WE_EQ8: if (DATA_WIDTH = 8) generate
      LENGTH_WE(0) <= not SOF_N and not DST_RDY_N;
      
      process (transfer_cnt, SRC_RDY_N, DST_RDY_N)
      begin
         if ((transfer_cnt="0001") and (SRC_RDY_N='0') and (DST_RDY_N='0')) then
            LENGTH_WE(1) <= '1';
         else
            LENGTH_WE(1) <= '0';
         end if;
      end process;

   end generate;   

   -- -------------------------------------------------------------------------
   --         (32+ADDR_WIDTH-1):32 ADDRESS WRITE ENABLES DETERMINATION       --
   -- -------------------------------------------------------------------------

   ADDR32_WE_GT: if (DATA_WIDTH >= 64) generate
      ADDR32_WE(0) <= not SOF_N and not DST_RDY_N;
   end generate;


   ADDR32_WE_LT: if (DATA_WIDTH < 64) generate
      ADDR32_WE_FOR : for i in 0 to ADDR_PARTS_NUM-1 generate
         process (transfer_cnt, SRC_RDY_N, DST_RDY_N)
         begin
            if ((transfer_cnt = (32/DATA_WIDTH + i)) and (SRC_RDY_N = '0') and (DST_RDY_N = '0')) then
               ADDR32_WE(i) <= '1';
            else
               ADDR32_WE(i) <= '0';
            end if;
         end process;
      end generate;
   end generate;

   -- -------------------------------------------------------------------------
   --         (64+ADDR_WIDTH-1):64 ADDRESS WRITE ENABLES DETERMINATION       --
   -- -------------------------------------------------------------------------

   ADDR64_WE_GT: if (DATA_WIDTH >= 64) generate
      ADDR64_WE(0) <= not EOF_N and not DST_RDY_N;
   end generate;


   ADDR64_WE_LT: if (DATA_WIDTH < 64) generate
      ADDR64_WE_FOR : for i in 0 to ADDR_PARTS_NUM-1 generate 
         process (transfer_cnt, SRC_RDY_N, DST_RDY_N)
         begin
            if ((transfer_cnt = (64/DATA_WIDTH + i)) and (SRC_RDY_N = '0') and (DST_RDY_N = '0')) then
               ADDR64_WE(i) <= '1';
            else
               ADDR64_WE(i) <= '0';
            end if;
         end process;
      end generate;
   end generate;   

   -- -------------------------------------------------------------------------
   --                       TAG WRITE ENABLE DETERMINATION                   --
   -- -------------------------------------------------------------------------

   TAG_WE_GE32: if (DATA_WIDTH >= 32) generate
      TAG_WE    <= not SOF_N and not DST_RDY_N;
   end generate;

   TAG_WE_LT32: if (DATA_WIDTH < 32) generate
      process (transfer_cnt, SRC_RDY_N, DST_RDY_N)
      begin
         if ((transfer_cnt = CNT_WIDTH-2) and (SRC_RDY_N = '0') and (DST_RDY_N = '0')) then
            TAG_WE <= '1';
         else
            TAG_WE <= '0';
         end if;
      end process;
      TAG_WE    <= '1' when ((transfer_cnt = CNT_WIDTH-2) and (SRC_RDY_N = '0') and (DST_RDY_N = '0')) else 
                   '0';
   end generate;

   -- -------------------------------------------------------------------------
   --                          TRANSFER DETERMINATION                        --
   -- -------------------------------------------------------------------------
   
   TRANSFER     <= not SRC_RDY_N and not DST_RDY_N;

   -- -------------------------------------------------------------------------
   --                         HEADER LAST DETERMINATION                      --
   -- -------------------------------------------------------------------------

   HEADER_LAST  <= not EOF_N and not DST_RDY_N;

   -- -------------------------------------------------------------------------
   --                   DONE FLAG WRITE ENABLE DETERMINATION                 --
   -- -------------------------------------------------------------------------

   DONE_FLAG_WE <= not SOF_N and not DST_RDY_N;   

end ib_endpoint_read_ctrl_fetch_marker_arch;

                     

