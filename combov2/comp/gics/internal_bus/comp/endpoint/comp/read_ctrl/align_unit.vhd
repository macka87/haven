-- align_unit_ep.vhd : Alignment Unit for IB Endpoint
-- Copyright (C) 2009 CESNET
-- Author(s): Vaclav Bartos <washek@liberouter.org>
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

-- ----------------------------------------------------------------------------
--            ENTITY DECLARATION -- Alignment Unit for IB Endpoint           --
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_READ_CTRL_ALIGN_UNIT is 
   generic (
      DATA_WIDTH    : integer:= 64
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK           : in std_logic;
      RESET         : in std_logic;

      -- Control interface ----------------------------------------------------
      COUNT         : in  std_logic_vector(13-log2(DATA_WIDTH/8)-1 downto 0);
      SRC_ALIGN     : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      DST_ALIGN     : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      LEN_ALIGN     : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      NEXT_TRANS    : out std_logic;

      -- Input interface ------------------------------------------------------
      IN_DATA       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_SRC_RDY    : in  std_logic;
      IN_DST_RDY    : out std_logic;

      -- Output interface -----------------------------------------------------
      OUT_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_SOF       : out std_logic;
      OUT_EOF       : out std_logic;
      OUT_SRC_RDY   : out std_logic;
      OUT_DST_RDY   : in  std_logic
   );
end IB_ENDPOINT_READ_CTRL_ALIGN_UNIT;

-- ----------------------------------------------------------------------------
--         ARCHITECTURE DECLARATION -- Alignment Unit for IB Endpoint        --
-- ----------------------------------------------------------------------------

architecture align_unit_arch of IB_ENDPOINT_READ_CTRL_ALIGN_UNIT is

   type   fsm_states is (S_IDLE, S_SOF, S_TRANSFER, S_WAIT_START, S_WAIT_END, S_SHORT1, S_SHORT2);
   signal present_state, next_state : fsm_states;

   signal cnt_data_ce : std_logic;
   signal cnt_data_we : std_logic;
   signal cnt_data    : std_logic_vector(13-log2(DATA_WIDTH/8)-1 downto 0);
   
   signal sel         : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal wait_start  : std_logic;
   signal wait_end    : std_logic;
   
   signal shreg_out   : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal shreg_addr  : std_logic_vector(DATA_WIDTH/8-1 downto 0);
   signal shreg_ce    : std_logic;

begin

   -- -------------------------------------------------------------------------
   --                              DATA COUNTER                              --
   -- -------------------------------------------------------------------------

   cnt_datap: process (CLK) 
   begin
      if (CLK = '1' and CLK'event) then
         if (RESET = '1') then 
            cnt_data <= (others => '0');
         elsif (cnt_data_ce = '1') then
            cnt_data <= cnt_data - 1;
         elsif (cnt_data_we = '1') then
            cnt_data <= COUNT;
         end if;
      end if;
   end process; 
   
   -- -------------------------------------------------------------------------
   
   sel <= SRC_ALIGN - DST_ALIGN;
   
   -- determine if we need to wait one cycle at the start or at the end -------
   wait_start_p: process(SRC_ALIGN, DST_ALIGN)
   begin
      if (SRC_ALIGN > DST_ALIGN) then
         wait_start <= '1';
      else
         wait_start <= '0';
      end if;
   end process;
   
   wait_end_p: process(sel, SRC_ALIGN, LEN_ALIGN)
   begin
      if (sel /= 0 and (sel < SRC_ALIGN + LEN_ALIGN or SRC_ALIGN + LEN_ALIGN = 0)) then
         wait_end <= '1';
      else
         wait_end <= '0';
      end if;
   end process;
   
   -- addresses for shift registers -------------------------------------------
   shreg_addr(0) <= '0';
   
   shreg_addr_loop: for i in 1 to (DATA_WIDTH/8-1) generate
      process (sel)
      begin
         if (sel > i or sel = 0) then
            shreg_addr(i) <= '0';
         else
            shreg_addr(i) <= '1';
         end if;
      end process;
   end generate;
   
   -- addressable shift registers mapped dirrectly to LUT ---------------------
   SHIFT_REG : for i in 0 to (DATA_WIDTH/8-1) generate
      ONE_BYTE : for j in 0 to 7 generate
         SRLC16E_I : SRLC16E
-- synthesis translate_off 
         generic map (INIT => X"0000")
-- synthesis translate_on 
         port map 
         (
            Q     => shreg_out((i*8)+j),  -- SRL data output
            Q15   => open,                -- Carry output (connect to next SRL)
            A0    => shreg_addr(i),       -- Select[0] input
            A1    => '0',                 -- Select[1] input
            A2    => '0',                 -- Select[2] input
            A3    => '0',                 -- Select[3] input
            CE    => shreg_ce,            -- Clock enable input
            CLK   => CLK,                 -- Clock input
            D     => IN_DATA((i*8)+j)     -- SRL data input
         );
     end generate; -- one_byte
   end generate; -- shift_reg
   
   
   -- Barrel shifter ----------------------------------------------------------
   BARREL_SHIFTER_I : entity work.barrel_shifter
   generic map (
      DATA_WIDTH  => DATA_WIDTH,
      SHIFT_LEFT  => false
   )
   port map (
      DATA_IN     => shreg_out,
      DATA_OUT    => OUT_DATA,
      SEL         => sel
   );
   
   
   -- -------------------------------------------------------------------------
   --                              CONTROL FSM                               --
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
   
   -- next state logic --------------------------------------------------------
   nextstatelogicp : process(present_state, IN_SRC_RDY, OUT_DST_RDY, 
                                                cnt_data, wait_start, wait_end)
   begin
      next_state <= present_state;
      
      case (present_state) is
         
         when S_IDLE =>
            if (IN_SRC_RDY = '1') then
               if (cnt_data = 1) then
                  next_state <= S_SHORT1;
               else
                  if (wait_start = '1') then
                     next_state <= S_WAIT_START;
                  else
                     next_state <= S_SOF;
                  end if;
               end if;
            end if;
         
         when S_WAIT_START =>
            if (IN_SRC_RDY = '1') then
               next_state <= S_SOF;
            end if;
         
         when S_SOF =>
            if (IN_SRC_RDY = '1') then
               next_state <= S_TRANSFER;
            end if;
            
            if (cnt_data = 1 and OUT_DST_RDY = '1') then
               if (wait_end = '1') then
                  next_state <= S_WAIT_END;
               else
                  next_state <= S_IDLE;
               end if;
            end if;
            
         
         when S_TRANSFER =>
            if (cnt_data = 1 and OUT_DST_RDY = '1') then
               if (wait_end = '1') then
                  next_state <= S_WAIT_END;
               else
                  next_state <= S_IDLE;
               end if;
            end if;
         
         when S_WAIT_END =>
            if (OUT_DST_RDY = '1') then
               next_state <= S_IDLE;
            end if;
         
          when S_SHORT1 =>
            if (OUT_DST_RDY = '1') then
               if (wait_end = '1') then
                  next_state <= S_SHORT2;
               else
                  next_state <= S_IDLE;
               end if;
            end if;
         
         when S_SHORT2 =>
            if (OUT_DST_RDY = '1') then
               next_state <= S_IDLE;
            end if;
         
      end case;
   end process;
   
   -- output logic ------------------------------------------------------------
   outputlogicp : process(present_state, IN_SRC_RDY, OUT_DST_RDY, 
                                                cnt_data, wait_start, wait_end)
   begin
      cnt_data_ce <= '0';
      cnt_data_we <= '0';
      shreg_ce    <= '0';
      IN_DST_RDY  <= '0';
      OUT_SRC_RDY <= '0';
      OUT_SOF     <= '0';
      OUT_EOF     <= '0';
      NEXT_TRANS  <= '0';
      
      case (present_state) is
         
         when S_IDLE =>
            cnt_data_we <= '1';
            shreg_ce    <= '1';
            IN_DST_RDY  <= '1';
         
         when S_WAIT_START =>
            cnt_data_ce <= IN_SRC_RDY;
            shreg_ce    <= IN_SRC_RDY;
            IN_DST_RDY  <= '1';
         
         when S_SOF =>
            cnt_data_ce <= IN_SRC_RDY and OUT_DST_RDY;
            shreg_ce    <= IN_SRC_RDY and OUT_DST_RDY;
            IN_DST_RDY  <= OUT_DST_RDY;
            OUT_SRC_RDY <= IN_SRC_RDY;
            OUT_SOF     <= '1';
            if (cnt_data = 1) then
               OUT_SRC_RDY <= '1';
               if (wait_end = '1') then
                  shreg_ce    <= OUT_DST_RDY;
               else
                  OUT_EOF     <= '1';
                  NEXT_TRANS  <= OUT_DST_RDY;
               end if;
            end if;
         
         when S_TRANSFER =>
            cnt_data_ce <= IN_SRC_RDY and OUT_DST_RDY;
            shreg_ce    <= IN_SRC_RDY and OUT_DST_RDY;
            IN_DST_RDY  <= OUT_DST_RDY;
            OUT_SRC_RDY <= IN_SRC_RDY;
            if (cnt_data = 1) then
               OUT_SRC_RDY <= '1';
               if (wait_end = '1') then
                  shreg_ce    <= OUT_DST_RDY;
               else
                  OUT_EOF     <= '1';
                  NEXT_TRANS  <= OUT_DST_RDY;
               end if;
            end if;
         
         when S_WAIT_END =>
            OUT_SRC_RDY <= '1';
            OUT_EOF     <= '1';
            NEXT_TRANS  <= OUT_DST_RDY;
         
         when S_SHORT1 =>
            IN_DST_RDY  <= OUT_DST_RDY;
            if (wait_start = '0') then
               OUT_SRC_RDY <= '1';
               OUT_SOF     <= '1';
            end if;
            if (wait_end = '1') then
               shreg_ce    <= OUT_DST_RDY;
            else
               OUT_EOF     <= '1';
               NEXT_TRANS  <= OUT_DST_RDY;
            end if;
         
         when S_SHORT2 =>
            OUT_SRC_RDY <= '1';
            if (wait_start = '1') then
               OUT_SOF <= '1';
            end if;
            OUT_EOF     <= '1';
            NEXT_TRANS  <= OUT_DST_RDY;
         
      end case;
   end process;
   
end align_unit_arch;

