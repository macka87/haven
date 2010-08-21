--
-- fetch_marker.vhd : Address Decoder Fetch Marker
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
use work.addr_dec_fetch_marker_pkg.all;

-- ----------------------------------------------------------------------------
--            ENTITY DECLARATION -- Address Decoder Fetch Marker             --
-- ----------------------------------------------------------------------------

entity ADDR_DEC_FETCH_MARKER is 
   generic(
      -- Data Width (1-128)
      DATA_WIDTH : integer := 64;
      -- Compare Width (1-32)
      CMP_WIDTH  : integer := 16      
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK               : in  std_logic;
      RESET             : in  std_logic;
      
      -- Input interface ------------------------------------------------------
      TRANSFER          : in  std_logic;
      EOF               : in  std_logic;

      -- Output interface -----------------------------------------------------
      REQUEST_VECTOR_WE : out std_logic;
      PAUSE_TRANSFER    : out std_logic;
      ADDR_NEXT         : out std_logic;
      ADDR_MX           : out std_logic_vector(max(log2(addr_input_width(DATA_WIDTH)/CMP_WIDTH),1)-1 downto 0);
      ADDR_WE           : out std_logic;
      ADDRPART_WE       : out std_logic;
      TYPE_LG_WE        : out std_logic
   );
end ADDR_DEC_FETCH_MARKER;

-- ----------------------------------------------------------------------------
--       ARCHITECTURE DECLARATION  --  Address Decoder Fetch Marker          --
-- ----------------------------------------------------------------------------

architecture addr_dec_fetch_marker_arch of ADDR_DEC_FETCH_MARKER is

   -- -------------------------------------------------------------------------
   --                           Constant declaration                         --
   -- -------------------------------------------------------------------------

   constant CMP_SERIAL   : boolean := serial_cmp_of_addr(addr_input_width(DATA_WIDTH), CMP_WIDTH);
   constant CMP_PARALLEL : boolean := not CMP_SERIAL;

   constant CNT_BITS     : integer := max(log2(addr_input_width(DATA_WIDTH)/CMP_WIDTH),1);
   constant ONES         : std_logic_vector(CNT_BITS-1 downto 0) := (others => '1');

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   -- FSM types and signals ---------------------------------------------------
   type   fsm_states is (S_IDLE, S_TYPE, S_ADDR, S_ADDRPART, S_BEFORE_EOF);
   signal present_state, next_state : fsm_states;     

   -- Auxiliary signals -------------------------------------------------------
   signal fsm_request_vector_we : std_logic;
   signal fsm_pause_transfer    : std_logic;
   signal fsm_addr_next         : std_logic;
   signal fsm_addr_we           : std_logic;
   signal fsm_addrpart_we       : std_logic;
   signal fsm_type_lg_we        : std_logic;
                       
   signal ce_addr_last          : std_logic;
   signal ce_addrpart_we        : std_logic;
   signal ce_addr_start         : std_logic;
   signal ce_type_lg_we         : std_logic;

   signal addr_last_aux         : std_logic;
   signal addr_start_aux        : std_logic;
   signal type_lg_we_aux        : std_logic;
   signal eof_reg               : std_logic;
      
   signal cnt_addrpart_we       : std_logic_vector(CNT_BITS-1 downto 0);

begin
   
   -- -------------------------------------------------------------------------
   --                           OUTPUT INTERFACE                             --
   -- -------------------------------------------------------------------------

   REQUEST_VECTOR_WE <= fsm_request_vector_we;
   PAUSE_TRANSFER    <= fsm_pause_transfer;
   ADDR_NEXT         <= fsm_addr_next;
   ADDR_MX           <= cnt_addrpart_we;
   TYPE_LG_WE        <= fsm_type_lg_we;

   ADDR_WE           <= fsm_addr_we;
   
   process (fsm_addr_we, fsm_addrpart_we)
   begin
      if (CMP_SERIAL) then
         ADDRPART_WE <= fsm_addr_we;
      else
         ADDRPART_WE <= fsm_addrpart_we;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --              CYCLIC REGISTERS (+ CNT, REG) FOR TIME MARKS              --
   -- -------------------------------------------------------------------------

   -- TYPE_LG ---------------------------------------------
   U_reg_cyc_type_lg_we: entity work.REG_CYC
   generic map (
      INIT  => X"00000000000000000000000000000001",
      WIDTH => type_lg_we_reg_cyc_width(DATA_WIDTH)
   )
   port map (
      CLK   => CLK,      
      CE    => ce_type_lg_we,
      DOUT  => type_lg_we_aux
   );

   -- ADDR_START ------------------------------------------
   U_reg_cyc_addr_start: entity work.REG_CYC
   generic map (
      INIT  => X"00000000000000000000000000000001",
      WIDTH => addr_start_reg_cyc_width(DATA_WIDTH, CMP_PARALLEL)
   )
   port map (
      CLK   => CLK,      
      CE    => ce_addr_start,
      DOUT  => addr_start_aux
   );

   -- ADDR_LAST -------------------------------------------
   U_reg_cyc_addr_last: entity work.REG_CYC
   generic map (
      INIT  => X"00000000000000000000000000000001",
      WIDTH => addr_last_reg_cyc_width(DATA_WIDTH, CMP_PARALLEL)
   )
   port map(
      CLK   => CLK,
      CE    => ce_addr_last,
      DOUT  => addr_last_aux
   );      

   -- ADDRPART_WE -----------------------------------------
   ADDRPART_WE_GEN: if (CMP_PARALLEL) generate
      cnt_addrpart_wep: process (CLK, RESET) 
      begin
         if (CLK = '1' and CLK'event) then
            if (RESET = '1') then 
               cnt_addrpart_we <= (others => '0');         
            elsif (ce_addrpart_we = '1') then
               cnt_addrpart_we <= cnt_addrpart_we + 1;
            end if;
         end if;
      end process;
   end generate;

   -- EOF -------------------------------------------------
   eof_regp: process (CLK, RESET) 
   begin
      if (CLK = '1' and CLK'event) then
         if (RESET = '1') then 
            eof_reg <= '0';      
         elsif (TRANSFER = '1' and EOF = '1' and fsm_pause_transfer = '0') then
            eof_reg <= '1';
         elsif (present_state = S_IDLE) then
            eof_reg <= '0';
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                               FETCH FSM                                --
   -- -------------------------------------------------------------------------
 
   -- -------------------------------------------------------------------------
   -- synchronize logic -------------------------------------------------------
   synchlogp : process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            present_state <= S_IDLE;
         else
            present_state <= next_state;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   -- next state logic --------------------------------------------------------
   nextstatelogicp : process(present_state, TRANSFER, EOF, addr_last_aux, cnt_addrpart_we, addr_start_aux, type_lg_we_aux, eof_reg)    
   begin
      next_state <= present_state;
      
      case (present_state) is
           
         -- S_IDLE ------------------------------------------------------------
         when  S_IDLE => 
            if (TRANSFER = '1' and type_lg_we_aux = '1' and DATA_WIDTH < 64) then
               next_state <= S_TYPE;
            end if;

            if (TRANSFER = '1' and addr_start_aux = '1' and DATA_WIDTH >= 64 and CMP_PARALLEL) then
               next_state <= S_ADDRPART;
            end if;

            if (TRANSFER = '1' and addr_last_aux = '1' and DATA_WIDTH >= 64 and CMP_SERIAL) then
               next_state <= S_BEFORE_EOF;
            end if;
            
            if (TRANSFER = '1' and EOF = '1' and DATA_WIDTH = 128 and CMP_SERIAL) then
               next_state <= S_IDLE;
            end if;

         -- S_TYPE ------------------------------------------------------------
         when  S_TYPE =>
            if (TRANSFER = '1' and addr_start_aux = '1') then
               if (CMP_PARALLEL) then
                  next_state <= S_ADDRPART;
               elsif (DATA_WIDTH < 32) then
                  next_state <= S_ADDR;
               else
                  next_state <= S_BEFORE_EOF;
               end if;
            end if;

         -- S_ADDR ------------------------------------------------------------
         when  S_ADDR =>  
            -- serial comparison --------------------------
            if (CMP_SERIAL) then
               if (TRANSFER = '1' and addr_last_aux = '1') then
                  next_state <= S_BEFORE_EOF;
               end if;
            end if;
            -- parallel comparison --------------------------
            if (CMP_PARALLEL) then
               if (CMP_WIDTH = 16) then
                  if (DATA_WIDTH = 32) then
                     next_state <= S_BEFORE_EOF;
                  end if;
                  
                  if (DATA_WIDTH = 64) then
                     if (TRANSFER = '1' and EOF = '1') then
                        next_state <= S_IDLE;
                     else
                        next_state <= S_BEFORE_EOF;
                     end if;
                  end if;

                  if (DATA_WIDTH = 128) then
                     if (eof_reg = '1' or (TRANSFER = '1' and EOF = '1')) then
                        next_state <= S_IDLE;
                     else
                        next_state <= S_BEFORE_EOF;
                     end if;
                  end if;
               end if;

               if (CMP_WIDTH < 16) then
                  if (TRANSFER = '1') then
                     next_state <= S_ADDRPART;
                  end if;
               end if;
            end if;

         -- S_ADDRPART --------------------------------------------------------
         when  S_ADDRPART =>  
               if (addr_last_aux = '1' and cnt_addrpart_we = ONES) then
                  if (DATA_WIDTH < 64) then
                     next_state <= S_BEFORE_EOF;
                  end if;
                  
                  if (DATA_WIDTH = 64) then
                     next_state <= S_BEFORE_EOF;
                  end if;

                  if (DATA_WIDTH = 128) then
                     if (eof_reg = '1' or (TRANSFER = '1' and EOF = '1')) then
                        next_state <= S_IDLE;
                     else
                        next_state <= S_BEFORE_EOF;
                     end if;
                  end if;
               end if;

               if (addr_last_aux = '0' and cnt_addrpart_we = ONES) then
                  next_state <= S_ADDR;
               end if;

         -- S_BEFORE_EOF ------------------------------------------------------
         when  S_BEFORE_EOF =>  
            if (TRANSFER = '1' and EOF = '1') then
               next_state <= S_IDLE;
            end if;
            
      end case;
   end process;
    
   -- -------------------------------------------------------------------------
   -- output logic ------------------------------------------------------------
   outputlogicp : process(present_state, TRANSFER, EOF, addr_last_aux, cnt_addrpart_we, addr_start_aux, type_lg_we_aux, eof_reg)
   begin 
      fsm_request_vector_we <= '0';
      fsm_pause_transfer    <= '0';  
      fsm_addr_next         <= '0';
      fsm_addr_we           <= '0'; 
      fsm_addrpart_we       <= '0'; 
      fsm_type_lg_we        <= '0'; 
                            
      ce_addr_last          <= '0'; 
      ce_addrpart_we        <= '0'; 
      ce_addr_start         <= '0'; 
      ce_type_lg_we         <= '0';      

      case (present_state) is 
      
         -- S_IDLE ------------------------------------------------------------
         when  S_IDLE => 
            fsm_type_lg_we        <= '1';
            
            if (TRANSFER = '1') then
               if (CMP_PARALLEL) then
                  ce_addr_start   <= '1';
               end if;
               ce_type_lg_we      <= '1';                     
            end if;

            if (TRANSFER = '1' and addr_start_aux = '1' and DATA_WIDTH >= 64) then
               fsm_addr_we        <= '1';
               fsm_addrpart_we    <= '1';
               ce_addrpart_we     <= '1';
            end if;

            if (TRANSFER = '1' and addr_last_aux = '1' and DATA_WIDTH >= 64 and CMP_SERIAL) then
               fsm_addr_next         <= '1';
               fsm_request_vector_we <= '1';
            end if;

         -- S_TYPE ------------------------------------------------------------
         when  S_TYPE =>      
            if (TRANSFER = '1') then
               ce_addr_start      <= '1';
            end if;
            
            if (TRANSFER = '1' and addr_start_aux = '1') then
               fsm_addr_we        <= '1';
               fsm_addrpart_we    <= '1';    
               ce_addrpart_we     <= '1';
               ce_addr_last       <= '1';  
            end if;

            if (TRANSFER = '1' and addr_last_aux = '1' and (DATA_WIDTH = 32 and CMP_SERIAL)) then
               fsm_addr_next         <= '1';
               fsm_request_vector_we <= '1';
            end if;

         -- S_ADDR ------------------------------------------------------------
         when  S_ADDR =>  
            if (TRANSFER = '1') then
               -- serial comparison --------------------------
               if (CMP_SERIAL) then
                  ce_addr_last       <= '1';
                  fsm_addr_we        <= '1';
                  fsm_addrpart_we    <= '1';
               
                  if (addr_last_aux = '1') then
                     fsm_addr_next         <= '1';
                     fsm_request_vector_we <= '1';
                  end if;
               end if;
               
               -- parallel comparison --------------------------
               if (CMP_PARALLEL) then
                  if (CMP_WIDTH = 16) then
                     ce_addr_last          <= '1';
                     ce_addrpart_we        <= '1';
                     fsm_addrpart_we       <= '1';
                     fsm_addr_next         <= '1';
                     fsm_request_vector_we <= '1';
   
                     if (DATA_WIDTH = 128 and eof_reg = '1') then
                        fsm_pause_transfer    <= '1';
                     else
                        fsm_pause_transfer    <= '0';
                     end if;
                  end if;
                  
                  if (CMP_WIDTH < 16) then
                     fsm_addr_we           <= '1';
                     fsm_addrpart_we       <= '1';
                     ce_addrpart_we        <= '1';
                  end if;
               end if;
              end if;
              
         -- S_ADDRPART --------------------------------------------------------
         when  S_ADDRPART =>  
               fsm_pause_transfer       <= '1';
               fsm_addrpart_we          <= '1';
               ce_addrpart_we        <= '1';
               
               if (cnt_addrpart_we = ONES and addr_last_aux = '0') then
                  ce_addr_last          <= '1';
               end if;
         
               if (addr_last_aux = '1' and cnt_addrpart_we = ONES) then
                  fsm_request_vector_we <= '1';
                  fsm_addr_next         <= '1';
                  ce_addr_last          <= '1';

                  if (DATA_WIDTH = 128 and eof_reg = '0') then
                     fsm_pause_transfer    <= '0';
                  end if;
               end if;


         -- S_BEFORE_EOF ------------------------------------------------------
         when  S_BEFORE_EOF =>
            
      end case;
   end process; 
   
end addr_dec_fetch_marker_arch;

