--
-- swapper.vhd : IB Endpoint Swapper
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
--                 ENTITY DECLARATION -- IB Endpoint Swapper                 -- 
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_SWAPPER is 
   generic(
      -- Data Width (8-128)
      DATA_WIDTH   : integer:= 64
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK           : in std_logic;  
      RESET         : in std_logic;  

      -- Input Packed Header interface ----------------------------------------
      IN_DATA       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_SOF_N      : in  std_logic;
      IN_EOF_N      : in  std_logic;
      IN_SRC_RDY_N  : in  std_logic;
      IN_DST_RDY_N  : out std_logic;

      -- Output Packed Header interface ---------------------------------------
      OUT_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_SOF_N     : out std_logic;
      OUT_EOF_N     : out std_logic;
      OUT_SRC_RDY_N : out std_logic;
      OUT_DST_RDY_N : in  std_logic;      

      -- Control Interface ----------------------------------------------------
      DST_ADDR_VLD  : in std_logic;
      SRC_ADDR_VLD  : in std_logic;
      TYPE_VLD      : in std_logic      
   );
end IB_ENDPOINT_SWAPPER;

-- ----------------------------------------------------------------------------
--              ARCHITECTURE DECLARATION  --  IB Endpoint Swapper            --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_swapper_arch of IB_ENDPOINT_SWAPPER is

   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal input_transfer         : std_logic;
   signal input_destination_rdy  : std_logic;
   signal output_transfer        : std_logic;
   signal output_source_rdy      : std_logic;
   
   signal full                   : std_logic;
   signal empty                  : std_logic;
   signal re                     : std_logic;
   signal we                     : std_logic;

   signal type_mx                : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal out_mx                 : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal in_mx                  : std_logic_vector(DATA_WIDTH-1 downto 0);
                                 
   signal swap_buffer_dout       : std_logic_vector(DATA_WIDTH-1+3 downto 0);
   signal swap_buffer_din        : std_logic_vector(DATA_WIDTH-1+3 downto 0);
                                 
   signal dout_src_addr_vld      : std_logic;
   signal dout_data              : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal dout_eof_n             : std_logic;
   signal dout_sof_n             : std_logic;
                                 
   signal src_addr_shreg_ce      : std_logic;
   signal src_addr_shreg         : std_logic_vector(DATA_WIDTH-1 downto 0);

   signal data_reg               : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal data_reg_vld           : std_logic;
   signal eof_n_reg              : std_logic;
   signal OUT_SRC_RDY_N_aux      : std_logic;
                                 
begin                            

   -- -------------------------------------------------------------------------
   -- -------------------------------------------------------------------------
   --                           DATA_WIDTH == 8/16                           --
   -- -------------------------------------------------------------------------
   -- -------------------------------------------------------------------------     
   DATA_WIDTH_8_16: if (DATA_WIDTH = 8 or DATA_WIDTH = 16) generate

   -- TRANSFER CONTROL --------------------------------------------------------

      -- input transfer logic -----------------------------
      input_transfer <= input_destination_rdy and not IN_SRC_RDY_N;
      
      input_destination_rdyp: process(DST_ADDR_VLD, full, dout_src_addr_vld, empty, OUT_DST_RDY_N)
      begin
         if (DST_ADDR_VLD = '0') then
            input_destination_rdy <= not full;
         else
            input_destination_rdy <= not full and dout_src_addr_vld and not empty and not OUT_DST_RDY_N;
         end if;
      end process;   

      -- output transfer logic ----------------------------
      output_transfer <= output_source_rdy and not OUT_DST_RDY_N;
      
      output_source_rdyp: process(DST_ADDR_VLD, IN_SRC_RDY_N, full, dout_src_addr_vld, empty)
      begin
         if (dout_src_addr_vld = '0') then
            output_source_rdy <= not empty;
         else
            output_source_rdy <= not empty and not IN_SRC_RDY_N and not full and DST_ADDR_VLD;
         end if;
      end process;      

   -- SRC_ADDR SHIFT REGISTER -------------------------------------------------

   U_src_addr_sh_reg : entity work.SH_REG_BUS
   generic map (
      NUM_BITS    => 32/DATA_WIDTH,
      DATA_WIDTH  => DATA_WIDTH
   )
   port map(
      CLK         => CLK,

      DIN         => IN_DATA,
      CE          => src_addr_shreg_ce,
      DOUT        => src_addr_shreg
   );

   src_addr_shreg_ce <= (DST_ADDR_VLD or SRC_ADDR_VLD) and input_transfer;

   -- INPUT MULTIPLEX LOGIC ---------------------------------------------------
   with TYPE_VLD select
      type_mx <= IN_DATA(DATA_WIDTH-1 downto 4)&C_IB_RDCL when '1',
                 IN_DATA                                  when others;

   with DST_ADDR_VLD select
      in_mx   <= src_addr_shreg when '1',
                 type_mx        when others;

   -- SWAP BUFFER -------------------------------------------------------------

   U_swap_buffer : entity work.SH_FIFO
   generic map (
      FIFO_WIDTH     => DATA_WIDTH+3,
      FIFO_DEPTH     => 128/DATA_WIDTH,
      USE_INREG      => false,
      USE_OUTREG     => false
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,

      -- write interface
      DIN            => swap_buffer_din,
      WE             => we,
      FULL           => full,

      -- read interface
      DOUT           => swap_buffer_dout,
      RE             => re,
      EMPTY          => empty,

      -- status
      STATUS         => open
   );

   swap_buffer_din   <= IN_SOF_N&IN_EOF_N&SRC_ADDR_VLD&in_mx;

   dout_data         <= swap_buffer_dout(DATA_WIDTH-1 downto 0);
   dout_src_addr_vld <= swap_buffer_dout(DATA_WIDTH); 
   dout_eof_n        <= swap_buffer_dout(DATA_WIDTH+1);
   dout_sof_n        <= swap_buffer_dout(DATA_WIDTH+2);

   we <= input_transfer;
   re <= output_transfer;

   -- OUTPUT MULTIPLEX LOGIC --------------------------------------------------
   with dout_src_addr_vld select out_mx <= IN_DATA   when '1',
                                           dout_data when others;

   -- OUTPUT INTERFACE --------------------------------------------------------
   OUT_DATA      <= out_mx;
   OUT_SOF_N     <= dout_sof_n or not output_source_rdy;
   OUT_EOF_N     <= dout_eof_n or not output_source_rdy;

   OUT_SRC_RDY_N <= not output_source_rdy;

   IN_DST_RDY_N  <= not input_destination_rdy;

   end generate;
   -- -------------------------------------------------------------------------        
   -- -------------------------------------------------------------------------
   --                           DATA_WIDTH == 32                             --
   -- -------------------------------------------------------------------------
   -- -------------------------------------------------------------------------        
   DATA_WIDTH_32: if (DATA_WIDTH = 32) generate   

   -- DATA PATH ---------------------------------------------------------------
   data_regp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (IN_SRC_RDY_N = '0' and OUT_DST_RDY_N = '0' and DST_ADDR_VLD = '0') then
            data_reg <= type_mx;
         end if;
      end if;
   end process; 
   
   with TYPE_VLD select
      type_mx <= IN_DATA(DATA_WIDTH-1 downto 4)&C_IB_RDCL when '1',
                 IN_DATA                                  when others;
   
   with (DST_ADDR_VLD and not IN_SRC_RDY_N) select
      OUT_DATA <= IN_DATA  when '1',
                  data_reg when others;

   -- CONTROL PATH ------------------------------------------------------------
   control_regp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            eof_n_reg <= '1';
         elsif (OUT_DST_RDY_N = '0') then
            if (IN_EOF_N = '0') then
               eof_n_reg <= '0';
            else
               eof_n_reg <= '1';
            end if;
         end if;
      end if;
   end process;

   OUT_SOF_N  <= not (SRC_ADDR_VLD and not IN_SRC_RDY_N);
   OUT_EOF_N  <= eof_n_reg;
   
   OUT_SRC_RDY_N <= (IN_SRC_RDY_N or not IN_SOF_N) and eof_n_reg;
   
   IN_DST_RDY_N <= OUT_DST_RDY_N;

   end generate;
   -- -------------------------------------------------------------------------        
   -- -------------------------------------------------------------------------
   --                           DATA_WIDTH == 64                             --
   -- -------------------------------------------------------------------------
   -- -------------------------------------------------------------------------        
   DATA_WIDTH_64: if (DATA_WIDTH = 64) generate   

   -- DATA PATH ---------------------------------------------------------------
   with IN_SOF_N select
      in_mx <= IN_DATA(DATA_WIDTH-1 downto  4)&C_IB_RDCL              when '0',
               IN_DATA(DATA_WIDTH-1 downto 32)&data_reg(63 downto 32) when others;   
              
   data_regp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            data_reg_vld <= '0';
         elsif (IN_SRC_RDY_N = '0' and (OUT_DST_RDY_N = '0' or data_reg_vld = '0')) then
            data_reg     <= in_mx;
            data_reg_vld <= '1';
         elsif (OUT_SRC_RDY_N_aux = '0' and OUT_DST_RDY_N = '0') then
            data_reg_vld <= '0';
         end if;
      end if;
   end process; 

   with IN_EOF_N select
      out_mx <= data_reg                                   when '1',
                IN_DATA(31 downto 0)&data_reg(31 downto 0) when others;

   OUT_DATA      <= out_mx;              

   -- CONTROL PATH ------------------------------------------------------------
   control_regp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            eof_n_reg <= '1';
         elsif (IN_EOF_N = '0') then
            eof_n_reg <= '0';
         elsif (eof_n_reg = '0' and OUT_DST_RDY_N = '0') then
            eof_n_reg <= '1';
         end if;
      end if;
   end process;    

   OUT_SOF_N         <= IN_EOF_N;
   OUT_EOF_N         <= eof_n_reg or not IN_EOF_N;
   
   OUT_SRC_RDY_N_aux <= IN_EOF_N and eof_n_reg;

   OUT_SRC_RDY_N     <= OUT_SRC_RDY_N_aux;
   
   IN_DST_RDY_N      <= OUT_DST_RDY_N and data_reg_vld;
                        
   end generate;
   -- -------------------------------------------------------------------------        
   -- -------------------------------------------------------------------------
   --                           DATA_WIDTH == 128                            --
   -- -------------------------------------------------------------------------   
   -- -------------------------------------------------------------------------        
   DATA_WIDTH_128: if (DATA_WIDTH = 128) generate

                    --    last 32 bits    |       src addr      |       dst addr      |    first 32 bits with type   |
   OUT_DATA      <= IN_DATA(127 downto 96)&IN_DATA(63 downto 32)&IN_DATA(95 downto 64)&IN_DATA(31 downto 4)&C_IB_RDCL;
   OUT_SOF_N     <= IN_SOF_N;    
   OUT_EOF_N     <= IN_EOF_N;    
   OUT_SRC_RDY_N <= IN_SRC_RDY_N;
   
   IN_DST_RDY_N  <= OUT_DST_RDY_N; 

   end generate;
    
end ib_endpoint_swapper_arch;

                     

