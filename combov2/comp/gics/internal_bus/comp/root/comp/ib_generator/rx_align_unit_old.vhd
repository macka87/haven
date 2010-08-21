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
   signal align_unit_src_addr       : std_logic_vector( 2 downto 0);
   signal align_unit_dst_addr       : std_logic_vector( 2 downto 0);
	signal align_unit_data_len       : std_logic_vector( 3 downto 0);
   signal align_unit_wait_on_start  : std_logic;
   signal align_unit_wait_on_end    : std_logic;
   signal align_unit_in_data        : std_logic_vector(63 downto 0);
   signal align_unit_in_sof         : std_logic;
   signal align_unit_in_eof         : std_logic;
   signal align_unit_in_src_rdy     : std_logic;
   signal align_unit_in_dst_rdy     : std_logic;
   signal align_unit_out_data       : std_logic_vector(63 downto 0);
   signal align_unit_out_sof        : std_logic;
   signal align_unit_out_eof        : std_logic;
   signal align_unit_out_src_rdy    : std_logic;
   signal align_unit_out_dst_rdy    : std_logic;

   -- input selected signals
   signal in_type                   : std_logic_vector( 3 downto 0);
   signal in_dst_addr               : std_logic_vector( 2 downto 0);
   signal in_data_len               : std_logic_vector( 3 downto 0);

   -- negative/positive input logic
   signal in_sop                    : std_logic;
   signal in_eop                    : std_logic;
   signal in_src_rdy                : std_logic;
   
   -- registred input
   signal in_type_reg               : std_logic_vector( 3 downto 0);
   signal in_src_addr_reg           : std_logic_vector( 2 downto 0);
   signal in_dst_addr_reg           : std_logic_vector( 2 downto 0);
   signal in_data_len_reg           : std_logic_vector( 3 downto 0);
   
   -- 2nd clock period
   signal in_sop_reg                : std_logic;
   signal in_eop_reg                : std_logic;
   -- 3rd clock period
   signal in_sop_reg2               : std_logic;

   -- select multiplexor output
   signal go_align                  : std_logic;
   signal go_align_mux              : std_logic;
   signal go_align_reg              : std_logic;
   signal in_type_mux_out           : std_logic_vector( 3 downto 0);
   signal in_src_addr_mux_out       : std_logic_vector( 2 downto 0);
   signal in_dst_addr_mux_out       : std_logic_vector( 2 downto 0);
   signal in_data_len_mux_out       : std_logic_vector( 2 downto 0);

   --output registers
   signal align_unit_out_eof_reg    : std_logic;
   signal align_unit_out_sof_reg    : std_logic;

   -- clock enable multiplexors
   signal align_unit_out_eof_mux    : std_logic;
   signal align_unit_out_sof_mux    : std_logic;

   -- FIXME: stop clock enable
   signal in_src_rdy_n_reg          : std_logic;
   
   signal next_part                 : std_logic;


begin

   -- ALIGN UNIT --------------------------------------------------------------
   ALIGN_UNIT_U : entity work.ALIGN_UNIT
      port map (
         -- Common interface --------------------------------------------------
         CLK           => CLK,
         RESET         => RESET,

         -- Control input interface -------------------------------------------   
         SRC_ADDR      => align_unit_src_addr,
         DST_ADDR      => align_unit_dst_addr,
	      DATA_LEN      => align_unit_data_len,

         -- Control ouptup interface ------------------------------------------
         WAIT_ON_START => align_unit_wait_on_start,
         WAIT_ON_END   => align_unit_wait_on_end,  

         -- Input interface ---------------------------------------------------
         IN_DATA       => align_unit_in_data,
         IN_SOF        => align_unit_in_sof,
         IN_EOF        => align_unit_in_eof,
         IN_SRC_RDY    => align_unit_in_src_rdy,
         IN_DST_RDY    => align_unit_in_dst_rdy,

         -- Output interface --------------------------------------------------
         OUT_DATA      => align_unit_out_data,
         OUT_SOF       => align_unit_out_sof,
         OUT_EOF       => align_unit_out_eof,
         OUT_SRC_RDY   => align_unit_out_src_rdy,
         OUT_DST_RDY   => align_unit_out_dst_rdy
   );   

   -- send input data
   align_unit_in_data  <= IN_DATA;

   -- get correct part of data to align_unit
   in_type     <= IN_DATA(15 downto 12);  -- 1st clock cycle 
   --in_src_addr <= IN_SRC_ADDR;            -- from input interface  
   in_dst_addr <= IN_DATA(34 downto 32);  -- 1st clock cycle
   in_data_len <= IN_DATA( 3 downto 0);   -- 1st clock cycle
     
   in_sop         <= not IN_SOP_N;
   in_eop         <= not IN_EOP_N;
   
   align_unit_in_src_rdy   <= not IN_SRC_RDY_N;
   IN_DST_RDY_N            <= not align_unit_in_dst_rdy;

   -- IN_SRC_RDY registred ----------------------------------------------------
   IN_SRC_RDY_I : process(CLK, IN_SRC_RDY_N)
	 begin
	 	if (CLK'event and CLK='1') then
			in_src_rdy_n_reg <= IN_SRC_RDY_N;
		end if;
	end process;

   -- multiplexor IN_SOF_MUX --------------------------------------------------
   IN_SOF_MUX: process(go_align, in_sop, in_sop_reg2)
   begin
      case go_align is
            when '0' => align_unit_in_sof <= in_sop;
            when '1' => align_unit_in_sof <= (in_sop or in_sop_reg2); -- 3rd clock period, start of data (or normal start)
            when others => null;
      end case;
   end process;

   -- multiplexor IN_EOF_MUX --------------------------------------------------
   IN_EOF_MUX: process(go_align, in_eop, in_sop_reg)
   begin
      case go_align is
            when '0' => align_unit_in_eof <= in_eop;
            when '1' => align_unit_in_eof <= (in_eop or in_sop_reg); -- 2nd clock period, end of headers (or normal end)
            when others => null;
      end case;
   end process;

   -- register IN_EOP_REG -----------------------------------------------------
   IN_EOP_REG_I : process(CLK, RESET, go_align, IN_SRC_RDY_N, in_eop)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               in_eop_reg <= '0';
            elsif(IN_SRC_RDY_N='0' and go_align='1') then --enable
               in_eop_reg <= in_eop;
            end if;
         end if;
      end process;

   -- register IN_SOP_REG -----------------------------------------------------
   IN_SOP_REG_I : process(CLK, RESET, go_align, IN_SRC_RDY_N, in_sop)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               in_sop_reg <= '0';
            elsif(IN_SRC_RDY_N='0' and go_align='1') then --enable
               in_sop_reg <= in_sop;
            end if;
         end if;
      end process;

    -- register IN_SOP_REG2 ----------------------------------------------------
   IN_SOP_REG2_II : process(CLK, RESET, go_align, IN_SRC_RDY_N, in_sop_reg)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               in_sop_reg2 <= '0';
            elsif(IN_SRC_RDY_N='0' and go_align='1') then -- enable
               in_sop_reg2 <= in_sop_reg;
            end if;
         end if;
      end process;

   -- register IN_TYPE_REG ----------------------------------------------------
   IN_TYPE_REG_I : process(CLK, RESET, IN_SOP_N, in_type)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               in_type_reg <= (others => '0');
            elsif(IN_SOP_N='0') then
               in_type_reg <= in_type;
            end if;
         end if;
      end process;
            
   -- register IN_SRC_ADDR_REG ------------------------------------------------
   IN_SRC_ADDR_REG_I : process(CLK, RESET, IN_SOP_N, IN_SRC_ADDR, align_unit_in_dst_rdy)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               in_src_addr_reg <= (others => '0');
            elsif(IN_SOP_N='0' and align_unit_in_dst_rdy='1') then
               in_src_addr_reg <= IN_SRC_ADDR;
            end if;
         end if;
      end process;

   -- register IN_DST_ADDR_REG ------------------------------------------------
   IN_DST_ADDR_REG_I : process(CLK, RESET, IN_SOP_N, in_dst_addr, align_unit_in_dst_rdy)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               in_dst_addr_reg <= (others => '0');
            elsif(IN_SOP_N='0' and align_unit_in_dst_rdy='1') then
               in_dst_addr_reg <= in_dst_addr;
            end if;
         end if;
      end process;

   -- register IN_LEN_REG -----------------------------------------------------
   IN_LEN_REG_I : process(CLK, RESET, IN_SOP_N, in_data_len, align_unit_in_dst_rdy)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               in_data_len_reg <= (others => '0');
            elsif(IN_SOP_N='0' and align_unit_in_dst_rdy='1') then
               in_data_len_reg <= in_data_len;
            end if;
         end if;
      end process;

   -- multiplexor IN_TYPE_MUX -------------------------------------------------
   IN_TYPE_MUX : process(IN_SOP_N, in_type, in_type_reg)
   begin
      case IN_SOP_N is
            when '0' => in_type_mux_out <= in_type;
            when '1' => in_type_mux_out <= in_type_reg;
            when others => null;
      end case;
   end process;
   
   -- test type of transaction
   go_align    <= '1' when (in_type_mux_out(2 downto 0) = "101" ) else -- C_IB_RD_COMPL_TRANSACTION ) else
                  '0';  
   -- switch control input to align unit
   go_align_mux   <= go_align and next_part;

   -- register NEXT_PART ------------------------------------------------------
   NEXT_PART_I : process(CLK, RESET, in_sop_reg2, in_eop_reg) -- CHANGES: SOP: reg -> reg2, EOP: ''-> reg
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               next_part <= '0';
            elsif(in_eop_reg='1') then    -- clear, after data transmit on output
               next_part <= '0';
            elsif(in_sop_reg2='1') then   -- load, after header is transmited
               next_part <= '1';
            end if;
         end if;
      end process;

   -- multiplexor IN_SRC_ADDR_MUX ---------------------------------------------
   IN_SRC_ADDR_MUX_II: process(go_align_mux, in_src_addr_reg)
   begin
      case go_align_mux is
            when '0' => align_unit_src_addr <= ZERO;
            when '1' => align_unit_src_addr <= in_src_addr_reg;
            when others => null;
      end case;
   end process;

   -- multiplexor IN_DST_ADDR_MUX ---------------------------------------------
   IN_DST_ADDR_MUX_II: process(go_align_mux, in_dst_addr_reg)
   begin
      case go_align_mux is
            when '0' => align_unit_dst_addr <= ZERO;
            when '1' => align_unit_dst_addr <= in_dst_addr_reg;
            when others => null;
      end case;
   end process;

   -- multiplexor IN_DATA_LEN_MUX ----------------------------------------------
   IN_DATA_LEN_MUX_II: process(go_align_mux, in_data_len_reg)
   begin
      case go_align_mux is
            when '0' => align_unit_data_len <= '0' & ZERO;
            when '1' => align_unit_data_len <= in_data_len_reg;
            when others => null;
      end case;
   end process;

   -- Output data & rdy connection
   OUT_DATA       <= align_unit_out_data;
   OUT_SRC_RDY_N  <= not align_unit_out_src_rdy;
   align_unit_out_dst_rdy <= not OUT_DST_RDY_N;

   -- register GO_ALIGN_REG ---------------------------------------------------
   GO_ALIGN_REG_I : process(CLK, RESET, go_align)
      begin
         if(CLK='1' and CLK'event) then
            go_align_reg <= go_align;
         end if;
      end process;

   -- multiplexor OUT_SOP_MUX -------------------------------------------------
   OUT_SOP_MUX: process(go_align_reg, align_unit_out_sof, align_unit_out_sof_reg)
   begin
      case go_align_reg is
            when '0' => OUT_SOP_N <= not align_unit_out_sof;
            when '1' => OUT_SOP_N <= not (align_unit_out_sof and align_unit_out_sof_reg);
            when others => null;
      end case;
   end process;

   -- multiplexor OUT_EOP_MUX -------------------------------------------------
   OUT_EOP_MUX: process(go_align_reg, align_unit_out_eof, align_unit_out_eof_reg)
   begin
      case go_align_reg is
            when '0' => OUT_EOP_N <= not align_unit_out_eof;
            when '1' => OUT_EOP_N <= not (align_unit_out_eof and align_unit_out_eof_reg);
            when others => null;
      end case;
   end process;

   -- register OUT_SOP_REG -----------------------------------------------------
   OUT_SOP_REG_I : process(CLK, RESET, align_unit_out_sof, align_unit_out_sof_reg)
      begin
        if(CLK='1' and CLK'event) then
            if(RESET='1') then
               align_unit_out_sof_reg <= '1';   --FIXME:
            elsif(align_unit_out_sof_mux = '1' and in_src_rdy_n_reg = '0') then -- CE
               align_unit_out_sof_reg <= not align_unit_out_sof_reg;
            end if;
         end if;
      end process;

   -- multiplexor CE_OUT_SOP_MUX -------------------------------------------------
   CE_OUT_SOP_MUX: process(go_align_reg, align_unit_out_sof)
   begin
      case go_align_reg is
            when '0' => align_unit_out_sof_mux <= '0';
            when '1' => align_unit_out_sof_mux <= align_unit_out_sof;
            when others => null;
      end case;
   end process;


   -- register OUT_EOP_REG -----------------------------------------------------
   OUT_EOP_REG_I : process(CLK, RESET, align_unit_out_eof, align_unit_out_eof_reg)
      begin
         if(CLK='1' and CLK'event) then
            if(RESET='1') then
               align_unit_out_eof_reg <= '0';      --FIXME:
            elsif(align_unit_out_eof_mux = '1' and in_src_rdy_n_reg = '0') then -- CE
               align_unit_out_eof_reg <= not align_unit_out_eof_reg;
            end if;
         end if;
      end process;

   -- multiplexor CE_OUT_EOP_MUX -------------------------------------------------
   CE_OUT_EOP_MUX: process(go_align_reg, align_unit_out_eof)
   begin
      case go_align_reg is
            when '0' => align_unit_out_eof_mux <= '0';
            when '1' => align_unit_out_eof_mux <= align_unit_out_eof;
            when others => null;
      end case;
   end process;

end architecture FULL;

