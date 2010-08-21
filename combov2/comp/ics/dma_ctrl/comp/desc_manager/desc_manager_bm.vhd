-- desc_manager_bm.vhd: Descriptor manager AKA process P1 (with BM)
-- Copyright (C) 2008 CESNET
-- Author(s): Petr Kastovsky <kastosvky@liberouter.org>
--            Pavol Korcek <korcek@liberouter.org> 
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
--
-- $Id$
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

use work.desc_man_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity desc_manager_bm is
   generic(
      -- local base address
      BASE_ADDR         : std_logic_vector(31 downto 0) := X"00000000";
      -- number of connected controlers (TX + RX)
      FLOWS             : integer := 8;
      -- number of descriptors. In scheme DOWNLOADED_BLOCK_SIZE. 
      -- Must be 2**N
      BLOCK_SIZE        : integer := 8;
      -- address gap between two init descriptors
      DESC_INIT_GAP     : integer := 8
   );
   port(
      -- Common interface
      CLK               : in std_logic;
      RESET             : in std_logic;

      -- Memory interface (InternalBus)
      -- Write interface
      WR_ADDR           : in std_logic_vector(31 downto 0);
      WR_DATA           : in std_logic_vector(63 downto 0);
      WR_BE             : in std_logic_vector(7 downto 0);
      WR_REQ            : in std_logic;
      WR_RDY            : out std_logic;

      -- BM Interface 
      BM_GLOBAL_ADDR    : out std_logic_vector(63 downto 0); 
      BM_LOCAL_ADDR     : out std_logic_vector(31 downto 0); 
      BM_LENGTH         : out std_logic_vector(11 downto 0); 
      BM_TAG            : out std_logic_vector(15 downto 0); 
      BM_TRANS_TYPE     : out std_logic_vector(3 downto 0);  
      BM_REQ            : out std_logic;                     
      BM_ACK            : in std_logic;                     
      BM_OP_TAG         : in std_logic_vector(15 downto 0); -- NOT USED!
      BM_OP_DONE        : in std_logic;                     -- NOT USED!  

      -- DESC fifo interface
      DF_DATA           : out std_logic_vector(63 downto 0);
      DF_ADDR           : out std_logic_vector(abs(log2(FLOWS)-1) downto 0);
      DF_WRITE          : out std_logic;
      DF_FULL           : in  std_logic_vector(FLOWS-1 downto 0);
      DF_STATUS         : in std_logic_vector(log2(2*BLOCK_SIZE+1)*FLOWS-1 downto 0);

      -- Per channel enable interface
      ENABLE            : in std_logic_vector(FLOWS-1 downto 0) 
   );
   
end entity desc_manager_bm;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------


architecture behavioral of desc_manager_bm is

   constant RAM2FPGA : integer := 0;         -- type of transaction used in BM

   -- address width for FLOWS and LSB/MSB positions
   constant FLOW_ADDR_WIDTH : integer := log2(FLOWS);
   constant FLOW_MSB        : integer := FLOW_ADDR_WIDTH + 12 - 1;

   constant INIT_GAP        : integer := log2(DESC_INIT_GAP/8);
   -- Desc_WE_Logic FSM signals    
   signal fsm_enable_input    : std_logic;   -- enable whole write FSM
   signal fsm_flag_clr        : std_logic;   -- clear flag to flag register from FSM
   signal fsm_fifo_we         : std_logic;   -- write enable to fifo memory
   signal fsm_reg_array_we    : std_logic;   -- write enable to register array
   signal fsm_store_addr      : std_logic;   -- indicates to store address

   -- Desc_Flags signals
   signal flag_get      : std_logic;                                       -- get flag 
   signal get_addr      : std_logic_vector(abs(log2(FLOWS)-1) downto 0);   -- from this get address
   signal flag_set      : std_logic;                                       -- set flag
   signal set_addr      : std_logic_vector(abs(log2(FLOWS)-1) downto 0);   -- from this set address
   signal clr_addr      : std_logic_vector(abs(log2(FLOWS)-1) downto 0);   -- from this clr address

   -- Desc_Get_Next signals
   signal fifo_status         : std_logic_vector(0 downto 0);  -- status signal to FSM
   signal next_addr           : std_logic;                     -- counter enable signal from FSM
   signal fsm_enable_output   : std_logic_vector(0 downto 0);  -- enable signal to output FSM

   -- Addresses
   signal channel_addr    : std_logic_vector(abs(log2(FLOWS)-1) downto 0); -- dma channel address
   signal desc_index      : std_logic_vector(abs(log2(FLOWS)-1) downto 0); -- descriptor index 
   signal init_sel        : std_logic;                                     -- init. phase indicator
   signal cnt_select_addr : std_logic_vector(abs(log2(FLOWS)-1) downto 0); -- output select address counter

   -- Reg_Array signals
   signal reg_array_we        : std_logic;                           -- input (or-ed) write enable to reg_array
   signal reg_array_be        : std_logic_vector(7 downto 0);        -- input be to reg_array
   signal reg_array_addr      : std_logic_vector(abs(log2(FLOWS)-1) downto 0);   -- input write address 
   signal reg_array_wdata     : std_logic_vector(63 downto 0);       -- input write data
   signal reg_array_rdata     : std_logic_vector(63 downto 0);       -- input read data
   signal reg_array_raddr_out : std_logic_vector(abs(log2(FLOWS)-1) downto 0);   -- output read address
   signal reg_array_rdata_out : std_logic_vector(63 downto 0);    -- output read data

   -- Fifo2NFifo signals (more flows)
--   signal data_vld            : std_logic_vector(FLOWS-1 downto 0);           -- valid data output from mfifo
   signal fifo_status_array   : std_logic_vector(log2(2*BLOCK_SIZE+1)*FLOWS-1 downto 0); -- full status
   signal fifo_status_msb     : std_logic_vector(FLOWS-1 downto 0);  	      -- status from mfifo, half full

   -- Fifo signals (one flow)
   signal fifo_status_one_flow    : std_logic_vector(log2(2*BLOCK_SIZE) downto 0);   -- status

   -- FSM's state decoders 
   signal fsm_we_state_dec        : std_logic_vector(1 downto 0);
   signal fsm_next_desc_state_dec : std_logic_vector(1 downto 0);
   signal fsm_bm_req              : std_logic;

   -- Number of words written on IB
   signal cnt_ibwords_written    : std_logic_vector(log2(BLOCK_SIZE)-1 downto 0);

   signal reg_array_increment    : std_logic_vector(11 downto 0); -- increment part of data in reg array


   signal gnd_vec                : std_logic_vector(31 downto 0);

begin

   gnd_vec <= (others => '0');

   -- write always possible
   WR_RDY <= '1';

   -- detect initialization write phase based on address
   process (WR_ADDR)
   begin                          
      if (WR_ADDR(DESC_MAN_INIT_BIT_POS) = '1') then
         init_sel <= '1';
      else
         init_sel <= '0';
      end if;
   end process;

   -- enables we_logic_fsm when WR_REQ occurs and desc_manager is not in
   -- initialization phase
   fsm_enable_input  <= WR_REQ and (not init_sel);

   -- enable write to reg_array when automata wants to write classical
   -- descriptor type 1 write (fsm_reg_array_write) and when last descriptor
   -- address have to be written or when initialization phase
   -- (init_sel with RD_REQ from bus).
   reg_array_we <= fsm_reg_array_we or (init_sel and WR_REQ);

      -- multiplex BE signal depending on what we need to write
   -- if address, we have to change only last 12 bits,
   -- so we read from reg_array data, add 8 to them and
   -- return only 16 modified bits (BE == 0x02 value)
   MUX_ERG_ARRAY_BE : process(fsm_store_addr, WR_BE)
   begin
      case fsm_store_addr is
         when '1' => reg_array_be <= conv_std_logic_vector(3, reg_array_be'length);    -- write only last 16 bits
         when '0' => reg_array_be <= WR_BE;                    -- write from input
         when others => reg_array_be <= (others => '0');       -- not defined
     end case;
   end process;


   -- multiple data from input in init mode, or from
   -- input data in normal mode (type 0 or 1)
   -- We assume 4KB page size, thus, incrementation only on low 12 bits
   reg_array_increment <= reg_array_rdata(11 downto 0) + X"008";

   MUX_REG_ARRAY_WDATA : process(fsm_store_addr, WR_DATA, reg_array_rdata,
      reg_array_increment)
   begin
      case fsm_store_addr is
         when '1' => reg_array_wdata <=
            reg_array_rdata(63 downto 12) & 
            reg_array_increment;  -- new address to store
         when '0' => reg_array_wdata <= WR_DATA(63 downto 1) & '0'; --type 1 or init
         when others => reg_array_wdata <= (others => '0');         
      end case;
   end process;

   -- cnt_ibwords_written counter
   cnt_ibwords_writtenp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_ibwords_written <= (others => '0');
         elsif (fsm_enable_input = '1') then       -- new descriptor added
            cnt_ibwords_written <= cnt_ibwords_written + 1;
         end if;
      end if;
   end process;

   -- control write logic with automata
   DESC_WE_LOGIC : entity work.desc_we_logic_fsm
      generic map(
         BLOCK_SIZE => BLOCK_SIZE
      )
      port map(
         -- global signals
         CLK            => CLK,
         RESET          => RESET,
         -- input signals
         ENABLE         => fsm_enable_input,
         DESC_TYPE      => WR_DATA(0),           
         COUNT          => cnt_ibwords_written, 
         --output signals
         FLAG_CLEAR     => fsm_flag_clr,
         FIFO_WE        => fsm_fifo_we,
         REG_ARRAY_WE   => fsm_reg_array_we,
         STORE_ADDR     => fsm_store_addr,
         STATE_DEC      => fsm_we_state_dec
      );
   
   -- automata for new descriptor download 
   DESC_GET_NEXT : entity work.desc_get_next_fsm
      port map(
         -- global signals
         CLK   => CLK,
         RESET => RESET,
         -- channel enable signal
         ENABLE   => fsm_enable_output(0),
         -- input signals
         STATUS   => fifo_status(0),
         FLAG_GET => flag_get,
         DMA_ACK  => BM_ACK,
         -- output signals
         NEXT_ADDR   => next_addr,
         DMA_REQ     => fsm_bm_req,
         FLAG_SET    => flag_set,
         STATE_DEC   => fsm_next_desc_state_dec
      );

   DF_DATA  <= WR_DATA;
   DF_ADDR  <= channel_addr;
   DF_WRITE <= fsm_fifo_we;
--    DF_FULL  
   fifo_status_array <= DF_STATUS;

--    -- multififo for whole descriptors storing
--    DESCRIPTORS : entity work.fifo2nfifo
--       generic map(
--          DATA_WIDTH  => 64,
--          FLOWS       => FLOWS,
--          BLOCK_SIZE  => 2*BLOCK_SIZE,
--          LUT_MEMORY  => false,
--          GLOB_STATE  => false
--       )
--       port map(
--          -- global signals
--          CLK   => CLK,
--          RESET => RESET,
--          -- write interface
--          DATA_IN     => WR_DATA,
--          BLOCK_ADDR  => channel_addr,
--          WRITE       => fsm_fifo_we,
--          FULL        => open,
--          -- read interface
--          DATA_OUT => DATA_OUT,
--          DATA_VLD => data_vld,
--          READ     => READ,
--          EMPTY    => open,
--          STATUS   => fifo_status_array
--       );

   -------------------------------------------------------------------
   -- More than one flow logic
   -------------------------------------------------------------------
   MORE_ONE_FLOW_GEN: if (FLOWS /= 1) generate

   -- clear select address depents on descriptor manager state
   -- when init, address == descriptor index number (driver)
   -- when others, address == channel number 
   clr_addr    <= reg_array_addr(log2(FLOWS)-1 downto 0);

   -- two addresses to flag array
   set_addr    <= cnt_select_addr;

   -- same as previous
   get_addr    <= cnt_select_addr;

   -- DMA channel address from input address
   channel_addr   <= WR_ADDR(log2(FLOWS)+12-1 downto 12);

   -- descriptor index from input address
   desc_index     <= WR_ADDR(log2(FLOWS)+3-1+INIT_GAP downto 3+INIT_GAP);

   -- multiplex write address in init mode and in normal mode
   MUX_REG_ARRAY_ADDR : process(init_sel, desc_index, channel_addr)
   begin
      case init_sel is
         when '1' => reg_array_addr <= desc_index; -- (log2(FLOWS)-1 downto 0);    -- init phase
         when '0' => reg_array_addr <= channel_addr;                -- type 0 or 1 descriptor
         when others => reg_array_addr <= (others => '0');
      end case;
   end process;


   -- address to reg_array from output connected to output address counter
   reg_array_raddr_out <= cnt_select_addr;

   -- atomic array of flags for all channels
   DESC_FLAG_ARRAY : entity work.desc_flags
      generic map(
         ITEMS   => FLOWS         
      )
      port map(
         -- global signals
         CLK   => CLK,
         RESET => RESET,
         -- set/clr/get interface
         GET      => flag_get,
         GET_ADDR => get_addr,
         SET      => flag_set,
         SET_ADDR => set_addr,
         CLR      => fsm_flag_clr,
         CLR_ADDR => clr_addr
      );

   -- register array to store next descriptor address      
   NEXT_DESC : entity work.reg_array
      generic map(
         DATA_WIDTH  => 64,
         ITEMS       => FLOWS
      )
      port map(
         -- global signals
         CLK   => CLK,
         -- write interface
         WEA    => reg_array_we,
         BEA    => reg_array_be,
         ADDRA  => reg_array_addr,
         DIA    => reg_array_wdata,
         DOA    => reg_array_rdata,
         -- read interface
         ADDRB  => reg_array_raddr_out,
         DOB    => reg_array_rdata_out
      );

   -- select address counter
   CNT_SELECT_I : process(CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (RESET='1') then
            cnt_select_addr <= conv_std_logic_vector(0, log2(FLOWS));
         elsif (next_addr = '1') then -- enable from FSM
            cnt_select_addr <= cnt_select_addr + 1;
         end if;
      end if;
   end process;

    -- generate half full status bit from fifo staus output
    GEN_STATUS_BIT : for i in 0 to (FLOWS-1) generate
	   fifo_status_msb(i)	<= fifo_status_array((i+1)*log2(2*BLOCK_SIZE+1) - 2);
    end generate;
	
--     -- DMA EMPTY signal from manager
--     GEN_FIFO_EMPTY_SIG: for i in 0 to FLOWS-1 generate
--       EMPTY(i) <= not data_vld(i);
--     end generate;

   -- status multiplexor connected to output FSM
   MUX_FIFO_STATUS : entity work.gen_mux
   generic map(
      DATA_WIDTH  => 1,
      MUX_WIDTH   => FLOWS        
   )
   port map(
      DATA_IN  => fifo_status_msb,
      SEL      => cnt_select_addr,
      DATA_OUT => fifo_status
   );
   
   -- enable multiplexor connected to output FSM   
    MUX_ENABLE : entity work.gen_mux
    generic map(
      DATA_WIDTH  => 1,
      MUX_WIDTH   => FLOWS
    )
    port map(
      DATA_IN  => ENABLE, --from input interface
      SEL      => cnt_select_addr,
      DATA_OUT => fsm_enable_output
   );

   BM_LOCAL_ADDR    <= BASE_ADDR(31 downto FLOW_MSB + 1) &
                       cnt_select_addr &
                       reg_array_rdata_out(11 downto 0);

   end generate;

   -------------------------------------------------------------------
   -- Only one flow logic
   -------------------------------------------------------------------
   ONE_FLOW_GEN : if (FLOWS = 1) generate

   -- DMA channel address for fifo2nfifo
   channel_addr   <= (others => '0');

   -- register to store next descriptor address      
   NEXT_DESC : entity work.be_register
      generic map(
         DATA_WIDTH  => 64
      )
      port map(
         -- global signals
         CLK   => CLK,
         -- write interface
         WEA    => reg_array_we,
         BEA    => reg_array_be,
         DIA    => reg_array_wdata,
         DOA    => reg_array_rdata,
         -- read interface
         DOB    => reg_array_rdata_out
      );

   -- atomic array flag register for one channel
   FLAG_GETP : process(CLK)
   begin
      if (CLK='1' and CLK'event) then
         if (RESET='1') then
            flag_get <= '0';
         elsif (flag_set = '1') then -- set from output FSM
            flag_get <= '1';
         elsif(fsm_flag_clr =  '1') then -- clear from input FSM
            flag_get <= '0';
         end if;
      end if;
   end process;

   -- generate half full status bit from fifo staus output
	fifo_status_msb(0)	<= fifo_status_array(log2(2*BLOCK_SIZE+1) - 2);
	fifo_status          <= fifo_status_msb;

--    -- DMA EMPTY signal from manager
--    EMPTY(0) <= not data_vld(0);

   -- enable dirrect from input
   fsm_enable_output <= ENABLE;

   -- local BM adress
   BM_LOCAL_ADDR     <= BASE_ADDR(31 downto 12) &
                     reg_array_rdata_out(11 downto 0);

   end generate;


   -- bus master (BM) interface
   BM_GLOBAL_ADDR   <= reg_array_rdata_out;       -- descriptor
   BM_LENGTH        <= conv_std_logic_vector(BLOCK_SIZE * 8, BM_LENGTH'length);
   BM_TAG           <= X"00FF"; -- last component on BM interface
   BM_TRANS_TYPE    <= conv_std_logic_vector(RAM2FPGA, BM_TRANS_TYPE'length);
   BM_REQ           <= fsm_bm_req;

end architecture;
