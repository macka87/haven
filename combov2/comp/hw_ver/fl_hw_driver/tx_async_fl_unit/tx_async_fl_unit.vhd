-- --------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    TX Asynchronous FrameLink Unit  
-- Description: 
-- Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
-- Date:         15.4.2011 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity TX_ASYNC_FL_UNIT is

   generic
   (
      -- data width
      DATA_WIDTH     : integer := 64;
      DELAY_WIDTH    : integer := 9
   );

   port
   (
      WR_CLK         : in  std_logic;
      RD_CLK         : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input FrameLink interface
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      
      -- input delay interface
      RX_DELAY       : in  std_logic_vector(DELAY_WIDTH-1 downto 0);
      RX_DELAY_WR_N  : in  std_logic;
      RX_DELAY_RDY_N : out std_logic;
      
      -- driver is disabled from software
      RX_FINISH      : in  std_logic; 
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      
      -- unit is ready 
      OUTPUT_RDY     : out std_logic
      
   );
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of TX_ASYNC_FL_UNIT is
-- ==========================================================================
--                                      TYPES
-- ==========================================================================


-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================
constant FIFO_DATA_WIDTH : integer := DATA_WIDTH + log2(DATA_WIDTH/8) + 4;
constant REM_INDEX  : integer := 4+log2(DATA_WIDTH/8);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- data fifo signals
signal sig_data_fifo_write    : std_logic;
signal sig_data_fifo_data_in  : std_logic_vector(FIFO_DATA_WIDTH-1 downto 0);
signal sig_data_fifo_data_out : std_logic_vector(FIFO_DATA_WIDTH-1 downto 0);
signal sig_data_fifo_read     : std_logic;
signal sig_data_fifo_rdy      : std_logic;

-- delay fifo signals
signal sig_delay_fifo_write   : std_logic;
signal sig_delay_fifo_data    : std_logic_vector(DELAY_WIDTH-1 downto 0);
signal sig_delay_fifo_read    : std_logic;
signal sig_delay_fifo_empty   : std_logic;
signal sig_delay_fifo_rdy     : std_logic;

signal sig_delay_fifo_data_only : std_logic_vector(DELAY_WIDTH-2 downto 0);
signal sig_is_delay         : std_logic; 
signal sig_reg_out_is_delay : std_logic; 
signal sig_mux_is_delay     : std_logic; 
signal sig_src_rdy          : std_logic; 
signal sig_decremented      : std_logic_vector(DELAY_WIDTH-2 downto 0);
signal sig_delay            : std_logic_vector(DELAY_WIDTH-2 downto 0);
signal sig_take             : std_logic;
signal sig_comp_output      : std_logic;
signal sig_neg_comp_output  : std_logic;
signal sig_reg_out          : std_logic_vector(DELAY_WIDTH-2 downto 0);
signal sig_taken            : std_logic;
signal sig_reg_taken        : std_logic;

-- ==========================================================================
--                           ARCHITECTURE BODY
-- ==========================================================================
begin

   sig_data_fifo_data_in(FIFO_DATA_WIDTH-1 downto REM_INDEX) <= RX_DATA;
   sig_data_fifo_data_in(REM_INDEX-1 downto 4)               <= RX_REM;
   sig_data_fifo_data_in(0)                                  <= RX_SOF_N;
   sig_data_fifo_data_in(1)                                  <= RX_EOF_N;
   sig_data_fifo_data_in(2)                                  <= RX_SOP_N;
   sig_data_fifo_data_in(3)                                  <= RX_EOP_N;

   -- --------------- DATA FIFO INSTANCE ------------------------------------
   data_async_fifo : entity work.cdc_fifo
   generic map(
      DATA_WIDTH  => FIFO_DATA_WIDTH
   )
   port map(
      RESET       => RESET,
      
      -- Write interface
      WR_CLK          => WR_CLK,
      WR_DATA         => sig_data_fifo_data_in,
      WR_WRITE        => sig_data_fifo_write,
      WR_FULL         => RX_DST_RDY_N,
      WR_ALMOST_FULL  => open,
      
      RD_CLK          => RD_CLK,
      RD_DATA         => sig_data_fifo_data_out,
      RD_READ         => sig_data_fifo_read,
      RD_EMPTY        => open,
      RD_ALMOST_EMPTY => sig_data_fifo_rdy
   );
   
   -- --------------- DELAY FIFO INSTANCE -----------------------------------
   delay_async_fifo : entity work.cdc_fifo
   generic map(
      DATA_WIDTH  => DELAY_WIDTH
   )
   port map(
      RESET       => RESET,
      
      -- Write interface
      WR_CLK          => WR_CLK,
      WR_DATA         => RX_DELAY,
      WR_WRITE        => sig_delay_fifo_write,
      WR_FULL         => RX_DELAY_RDY_N,
      WR_ALMOST_FULL  => open,
      
      RD_CLK          => RD_CLK,
      RD_DATA         => sig_delay_fifo_data,
      RD_READ         => sig_delay_fifo_read,
      RD_EMPTY        => sig_delay_fifo_empty,
      RD_ALMOST_EMPTY => sig_delay_fifo_rdy
   );

   -- ================= IMPLEMENTATION ======================================
   
   -- data fifo input side
   sig_data_fifo_write  <= not RX_SRC_RDY_N;
   
   -- data fifo output side
   TX_SOF_N <= sig_data_fifo_data_out(0);
   TX_EOF_N <= sig_data_fifo_data_out(1);
   TX_SOP_N <= sig_data_fifo_data_out(2);
   TX_EOP_N <= sig_data_fifo_data_out(3);
   TX_REM   <= sig_data_fifo_data_out(REM_INDEX-1 downto 4); 
   TX_DATA  <= sig_data_fifo_data_out(FIFO_DATA_WIDTH-1 downto REM_INDEX);
   
   -- delay fifo input side
   sig_delay_fifo_write <= not RX_DELAY_WR_N;
   
   -- delay fifo output side
   sig_delay_fifo_data_only <= sig_delay_fifo_data(DELAY_WIDTH-2 downto 0);
   sig_is_delay <= sig_delay_fifo_data(DELAY_WIDTH-1);
   
   -- register for identification if delay or wait transaction 
   reg1 : process (RD_CLK)
   begin
      if (RESET = '1') then 
        sig_reg_out_is_delay <= '0';
      elsif (rising_edge(RD_CLK)) then
         if (sig_take = '1') then
            sig_reg_out_is_delay <= sig_is_delay;   
         end if;   
      end if;
   end process;
   
   -- multiplexer
   mux1 : process (sig_take, sig_is_delay, sig_reg_out_is_delay)
   begin
      sig_mux_is_delay <= '0';

      case sig_take is
         when '0'    => sig_mux_is_delay <= sig_reg_out_is_delay;
         when '1'    => sig_mux_is_delay <= sig_is_delay;
         when others => null;   
      end case;   
   end process;
   
   -- multiplexer
   mux2 : process (sig_take, sig_delay_fifo_data_only, sig_decremented)
   begin
      sig_delay <= sig_decremented;

      case sig_take is
         when '0'    => sig_delay <= sig_decremented;
         when '1'    => sig_delay <= sig_delay_fifo_data_only;
         when others => null;   
      end case;   
   end process;
   
   -- comparator
   comp : process (sig_delay)
   begin
     if (sig_delay = "00000000") then sig_comp_output <= '1';
     else sig_comp_output <= '0'; 
     end if;
   end process;
   
   sig_neg_comp_output <= not sig_comp_output;
   sig_taken <= sig_neg_comp_output nor TX_DST_RDY_N;
      
   -- register for decrement 
   reg2 : process (RD_CLK)
   begin
      if (RESET = '1') then 
         sig_reg_out <= (others => '0');
      elsif (rising_edge(RD_CLK)) then
         if (sig_neg_comp_output = '1') then
            sig_reg_out <= sig_delay;   
         end if;   
      end if;
   end process;
   
   sig_decremented <= sig_reg_out - 1;
   
   -- register for taken
   reg3 : process (RD_CLK, RESET)
   begin
      if (RESET = '1') then 
         sig_reg_taken <= '1';
      elsif (rising_edge(RD_CLK)) then
         if (sig_taken = '1') then
            sig_reg_taken <= sig_taken;
         elsif (sig_take = '1') then
            sig_reg_taken <= '0';   
         end if;   
      end if;
   end process;
   
   sig_take <= sig_reg_taken and (not sig_delay_fifo_empty); 
   sig_src_rdy <= (sig_neg_comp_output or sig_mux_is_delay) or (sig_delay_fifo_empty and sig_reg_taken);
   TX_SRC_RDY_N <= sig_src_rdy;
   sig_data_fifo_read <= sig_src_rdy nor TX_DST_RDY_N; 
   sig_delay_fifo_read <= sig_take;
   
   OUTPUT_RDY <= RX_FINISH or ((not sig_data_fifo_rdy) and 
                               (not sig_delay_fifo_rdy));    
end architecture;
