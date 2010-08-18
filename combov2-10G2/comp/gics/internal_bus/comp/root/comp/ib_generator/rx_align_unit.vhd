--
-- rx_align_unit.vhd : Align unit connected to RX part of PCIe2IB Bridge
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


--- -------------------------------
-- Completition data packet format 
-----------------------------------
-- 63                            32 31         16 15     12 11           0
-- -----------------------------------------------------------------------
-- |        DST.ADDR (LOCAL)       |     TAG     |   TYPE  |    LENGTH   |
-- -----------------------------------------------------------------------
-- |                              RESERVED                               |
-- -----------------------------------------------------------------------
-- |                                DATA                                 |
-- -----------------------------------------------------------------------

-- TYPE:
--    C_IB_RD_COMPL_TRANSACTION = 101
--    => 0101 (Read completion without last fragment)
--    => 1101 (Read completion with last fragment)
--    For more information see --ib_pkg.vhd--
   
library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity RX_ALIGN_UNIT is
  port (
      -- Common interface -----------------------------------------------------
      CLK                   : in  std_logic;
      RESET                 : in  std_logic;   
      -- Input interface ------------------------------------------------------
      IN_DATA               : in  std_logic_vector( 63 downto 0 ); -- Data or Header
      IN_SOP_N              : in  std_logic;                       -- Start of Packet
      IN_EOP_N              : in  std_logic;                       -- End of Packet
      IN_SRC_RDY_N          : in  std_logic;                       -- Source Ready
      IN_DST_RDY_N          : out std_logic;                       -- Destination Ready
      IN_SRC_ADDR           : in  std_logic_vector( 2 downto 0);   -- Source Addres from IB_GENERATOR  
      -- Output interface -----------------------------------------------------
      OUT_DATA              : out std_logic_vector( 63 downto 0 ); -- Data or Header
      OUT_SOP_N             : out std_logic;                       -- Start of Packet
      OUT_EOP_N             : out std_logic;                       -- End of Packet
      OUT_SRC_RDY_N         : out std_logic;                       -- Source Ready
      OUT_DST_RDY_N         : in  std_logic                        -- Destination Ready
  );
end RX_ALIGN_UNIT;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of RX_ALIGN_UNIT is

   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------

   constant ZERO           : std_logic_vector( 2 downto 0) := "000";

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
   
   -- align unit interface
   signal au_src_addr       : std_logic_vector( 2 downto 0);
   signal au_dst_addr       : std_logic_vector( 2 downto 0);
	signal au_data_len       : std_logic_vector( 2 downto 0);

   signal au_wait_on_start  : std_logic;
   signal au_wait_on_end    : std_logic;

   signal au_in_data        : std_logic_vector(63 downto 0);
   signal au_in_sof         : std_logic;
   signal au_in_eof         : std_logic;
   signal au_in_src_rdy     : std_logic;
   signal au_in_dst_rdy     : std_logic;

   signal au_out_data       : std_logic_vector(63 downto 0);
   signal au_out_sof        : std_logic;
   signal au_out_eof        : std_logic;
   signal au_out_src_rdy    : std_logic;
   signal au_out_dst_rdy    : std_logic;

   -- registred values
   signal in_type_reg      : std_logic_vector( 3 downto 0);
   signal in_src_addr_reg  : std_logic_vector( 2 downto 0);
   signal in_dst_addr_reg  : std_logic_vector( 2 downto 0);
   signal in_data_len_reg  : std_logic_vector( 2 downto 0);
   
   -- positive SOP logic
   signal in_sop           : std_logic;
   -- 2nd clock period
   signal in_sop_reg       : std_logic;
   -- 3rd clock period
   signal in_sop_reg2      : std_logic;

   -- detected true type of transaction
   signal go_align         : std_logic;

   -- data part of input frame
   signal data_sel         : std_logic;

   -- output/input multiplexor selector
   signal mux_sel          : std_logic;

   -- registred SRC_RDY for AU
   signal in_src_rdy_n_reg : std_logic;
   signal in_dst_rdy_n_sig : std_logic;

begin

   -- ALIGN UNIT --------------------------------------------------------------
   ALIGN_UNIT_U : entity work.GICS_ALIGN_UNIT
      port map (
         -- Common interface --------------------------------------------------
         CLK           => CLK,
         RESET         => RESET,

         -- Control input interface -------------------------------------------   
         SRC_ADDR      => au_src_addr,
         DST_ADDR      => au_dst_addr,
	      DATA_LEN      => au_data_len,

         -- Control ouptup interface ------------------------------------------
         WAIT_ON_START => au_wait_on_start,
         WAIT_ON_END   => au_wait_on_end,  

         -- Input interface ---------------------------------------------------
         IN_DATA       => au_in_data,
         IN_SOF        => au_in_sof,
         IN_EOF        => au_in_eof,
         IN_SRC_RDY    => au_in_src_rdy,
         IN_DST_RDY    => au_in_dst_rdy,

         -- Output interface --------------------------------------------------
         OUT_DATA      => au_out_data,
         OUT_SOF       => au_out_sof,     -- open
         OUT_EOF       => au_out_eof,
         OUT_SRC_RDY   => au_out_src_rdy,
         OUT_DST_RDY   => au_out_dst_rdy
   );   


   -- align unit interconection -----------------------------------------------
   au_in_data     <= IN_DATA;
   au_in_sof      <= in_sop_reg2;
   au_in_eof      <= not IN_EOP_N;
   au_src_addr    <= in_src_addr_reg;
   au_dst_addr    <= in_dst_addr_reg;
   au_data_len    <= in_data_len_reg;
   au_out_dst_rdy <= not OUT_DST_RDY_N;

   -- multiplexor AU_IN_SRC_RDY -----------------------------------------------
   AU_IN_SRC_RDY_MUX: process(mux_sel, data_sel, in_src_rdy_n)
   begin
      case mux_sel is
            when '0' => au_in_src_rdy <= '0';               -- AU not active
            when '1' => au_in_src_rdy <= not in_src_rdy_n;  -- from input, and when we needs output
            when others => null;
      end case;
   end process;

   -- multiplexor AU_IN_DST_RDY_MUX -------------------------------------------
   AU_IN_DST_RDY_MUX: process(mux_sel, OUT_DST_RDY_N, au_in_dst_rdy, au_out_eof)
   begin
      case mux_sel is
            when '0' => in_dst_rdy_n_sig <= OUT_DST_RDY_N;                           -- bypass
            when '1' => in_dst_rdy_n_sig <= (au_out_eof or (not au_in_dst_rdy));     -- from AU
            when others => null;
      end case;
   end process;
   
   IN_DST_RDY_N <= in_dst_rdy_n_sig;

   in_sop         <= not IN_SOP_N;
   
   -- register IN_SOP_REG -----------------------------------------------------
   IN_SOP_REG_I : process(CLK, RESET, in_sop, IN_SRC_RDY_N, in_dst_rdy_n_sig)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               in_sop_reg <= '0';
            elsif(IN_SRC_RDY_N='0' and in_dst_rdy_n_sig='0') then
               in_sop_reg <= in_sop;
            end if;
         end if;
      end process;

    -- register IN_SOP_REG2 ---------------------------------------------------
   IN_SOP_REG2_II : process(CLK, RESET, in_sop_reg, IN_SRC_RDY_N, in_dst_rdy_n_sig)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               in_sop_reg2 <= '0';
            elsif(IN_SRC_RDY_N='0' and in_dst_rdy_n_sig='0') then
               in_sop_reg2 <= in_sop_reg;
            end if;
         end if;
      end process;

   -- multiplexor OUT_DATA_MUX ------------------------------------------------
   OUT_DATA_MUX: process(mux_sel, IN_DATA, au_out_data)
   begin
      case mux_sel is
            when '0' => OUT_DATA <= IN_DATA;          -- bypass
            when '1' => OUT_DATA <= au_out_data;      -- from AU
            when others => null;
      end case;
   end process;

   -- multiplexor OUT_SOP_MUX -------------------------------------------------
   OUT_SOP_MUX: process(mux_sel, IN_SOP_N )
   begin
      case mux_sel is
            when '0' => OUT_SOP_N <= IN_SOP_N;       -- bypass
            when '1' => OUT_SOP_N <= '1';            -- open, no start of packet need
            when others => null;
      end case;
   end process;

   -- multiplexor OUT_EOP_MUX -------------------------------------------------
   OUT_EOP_MUX: process(mux_sel, IN_EOP_N, au_out_eof)
   begin
      case mux_sel is
            when '0' => OUT_EOP_N <= IN_EOP_N;           -- bypass
            when '1' => OUT_EOP_N <= not au_out_eof;     -- from AU
            when others => null;
      end case;
   end process;

   -- multiplexor OUT_SRC_RDY_MUX ---------------------------------------------
   OUT_SRC_RDY_MUX: process(mux_sel, IN_SRC_RDY_N, au_out_src_rdy)
   begin
      case mux_sel is
            when '0' => OUT_SRC_RDY_N <= IN_SRC_RDY_N;         -- bypass
            when '1' => OUT_SRC_RDY_N <= not au_out_src_rdy;   -- from AU
            when others => null;
      end case;
   end process;

   -- register IN_SRC_ADDR_REG ------------------------------------------------
   IN_SRC_ADDR_REG_I : process(CLK, RESET, IN_SOP_N, IN_SRC_ADDR, au_in_dst_rdy)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               in_src_addr_reg <= (others => '0');
            elsif(IN_SOP_N='0' and au_in_dst_rdy='1') then
               in_src_addr_reg <= IN_SRC_ADDR;
            end if;
         end if;
      end process;

   -- register IN_DST_ADDR_REG ------------------------------------------------
   IN_DST_ADDR_REG_I : process(CLK, RESET, IN_SOP_N, IN_DATA, au_in_dst_rdy)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               in_dst_addr_reg <= (others => '0');
            elsif(IN_SOP_N='0' and au_in_dst_rdy='1') then
               in_dst_addr_reg <= IN_DATA(34 downto 32);
            end if;
         end if;
      end process;

   -- register IN_LEN_REG -----------------------------------------------------
   IN_LEN_REG_I : process(CLK, RESET, IN_SOP_N, IN_DATA, au_in_dst_rdy)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               in_data_len_reg <= (others => '0');
            elsif(IN_SOP_N='0' and au_in_dst_rdy='1') then
               in_data_len_reg <= IN_DATA(2 downto 0);
            end if;
         end if;
      end process;

   -- register IN_TYPE_REG ----------------------------------------------------
   IN_TYPE_REG_I : process(CLK, RESET, IN_SOP_N, IN_DATA, au_in_dst_rdy)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               in_type_reg <= (others => '0');
            elsif(IN_SOP_N='0' and au_in_dst_rdy='1') then
               in_type_reg <= IN_DATA(15 downto 12);  
            end if;
         end if;
      end process;

   -- test type of transaction
   go_align    <= '1' when (in_type_reg(2 downto 0) = "101" ) else -- C_IB_RD_COMPL_TRANSACTION ) else
                  '0';  

   -- register DATA_SEL -------------------------------------------------------
   DATA_SEL_I : process(CLK, RESET, IN_SRC_RDY_N, OUT_DST_RDY_N, in_sop_reg, au_out_eof)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               data_sel <= '0';
            -- elsif(in_sop_reg='1' and OUT_DST_RDY_N = '0' and IN_SRC_RDY_N = '0') then    -- set
            elsif(in_sop_reg='1' and OUT_DST_RDY_N = '0') then    -- set 
               data_sel <= '1';
            -- elsif(au_out_eof='1' and OUT_DST_RDY_N = '0' and IN_SRC_RDY_N = '0') then    -- clear
            elsif(au_out_eof='1' and OUT_DST_RDY_N = '0') then    -- clear
               data_sel <= '0';
            end if;
         end if;
      end process;

   -- select multiplexor output      
   mux_sel <= go_align and data_sel; -- and (not au_out_eof);
      
end architecture FULL;

