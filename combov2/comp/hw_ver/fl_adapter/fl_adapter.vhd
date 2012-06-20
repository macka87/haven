--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Adapter
-- Description:  Drives and processes the bitflow from generator according to
--               request from software.
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         19.6.2013 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity FL_ADAPTER_UNIT is

   generic
   (
      -- data width
      DATA_WIDTH  : integer := 64;
      -- the width of the maximum number of parts counter (the maximum size is
      -- 2^PART_NUM_CNT_WIDTH)
      PART_NUM_CNT_WIDTH : integer := 3;
      -- the width of the maximum size of a part counter (the maximum size is
      -- 2^PART_SIZE)
      PART_SIZE_CNT_WIDTH : integer := 32;
      -- endpoint id
      ENDPOINT_ID : integer := 0
   );

   port
   (
      CLK       : in std_logic;
      RESET     : in std_logic;

      -- MI32 Interface
      MI_DWR    :  in std_logic_vector(31 downto 0);
      MI_ADDR   :  in std_logic_vector(31 downto 0);
      MI_RD     :  in std_logic;
      MI_WR     :  in std_logic;
      MI_BE     :  in std_logic_vector( 3 downto 0);
      MI_DRD    : out std_logic_vector(31 downto 0);
      MI_ARDY   : out std_logic;
      MI_DRDY   : out std_logic;
      
      -- Generator Interface
      GEN_FLOW  :  in std_logic_vector(DATA_WIDTH-1 downto 0);
      
      -- Output FrameLink Interface
      DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      D_REM     : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      SRC_RDY_N : out std_logic;
      DST_RDY_N : in  std_logic;
      SOP_N     : out std_logic;
      EOP_N     : out std_logic;
      SOF_N     : out std_logic;
      EOF_N     : out std_logic
   );       
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of FL_ADAPTER_UNIT is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================
type state_type is (header_state, data_state);

type header_type is (SOME_PART_UNCOMPLETE, SOME_PART_COMPLETE, 
                     LAST_PART_UNCOMPLETE, LAST_PART_COMPLETE
                     );

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- the maximum number of parts in a frame
   constant MAX_PARTS        : integer := 8;

-- endpoint tag
   constant ENDPOINT_TAG     : std_logic_vector(7 downto 0) :=
      conv_std_logic_vector(ENDPOINT_ID, 8);
      
-- FrameLink protocol ID
   constant FL_PROTOCOL_ID   : std_logic_vector(7 downto 0) := X"90";   
   
-- data transaction type 
   constant DATA_TRANS_TYPE  : std_logic_vector(7 downto 0) := X"00";     
   
-- FrameLink Interface info - some part, uncomplete data   
   constant SOME_PART_UNCOMPLETE_INFO : std_logic_vector(15 downto 0) := X"0000";  
   
-- FrameLink Interface info - some part, complete data   
   constant SOME_PART_COMPLETE_INFO   : std_logic_vector(15 downto 0) := X"0002";
   
-- FrameLink Interface info - last part, uncomplete data   
   constant LAST_PART_UNCOMPLETE_INFO : std_logic_vector(15 downto 0) := X"0001";  
   
-- FrameLink Interface info - last part, complete data   
   constant LAST_PART_COMPLETE_INFO   : std_logic_vector(15 downto 0) := X"0003";          

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================
-- register processing unit interface signals 
signal sig_mi_dwr             : std_logic_vector(31 downto 0);
signal sig_mi_addr            : std_logic_vector(31 downto 0);
signal sig_mi_wr              : std_logic;
signal sig_mi_rd              : std_logic;
signal sig_mi_be              : std_logic_vector( 3 downto 0); 
signal sig_mi_drd             : std_logic_vector(31 downto 0);
signal sig_mi_ardy            : std_logic; 
signal sig_mi_drdy            : std_logic; 
signal sig_gen_flow           : std_logic_vector(DATA_WIDTH - 1 downto 0);
signal sig_part_size_in       : std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0);
signal sig_size_vld           : std_logic;
signal sig_size_take          : std_logic;
signal sig_last               : std_logic;

-- fifo interface signals 
signal sig_part_size_out      : std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0);
signal sig_part_complete      : std_logic;
signal sig_fifo_full          : std_logic;
signal sig_fifo_empty         : std_logic;

-- data size processing unit interface signals
signal sig_data_size          : std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0);
signal sig_data_size_vld      : std_logic;
signal sig_data_complete      : std_logic;

-- data processing unit interface signals
signal sig_data_request       : std_logic;
signal sig_data_ready         : std_logic;
signal sig_rem                : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

-- FSM signals 
signal state_reg, state_next  : state_type;
signal is_header              : std_logic;

-- Header signals
signal sig_header_type        : header_type;
signal sig_header             : std_logic_vector(DATA_WIDTH-1 downto 0);

-- Data signals 
signal sig_data_out           : std_logic_vector(DATA_WIDTH-1 downto 0); 

begin

   -- Assertions
   assert (PART_NUM_CNT_WIDTH <= 3)
      report "Unsupported value of PART_NUM_CNT_WIDTH (PART_NUM_CNT_WIDTH > 3)"
      severity failure;

   -- Assertions
   assert (PART_NUM_CNT_WIDTH <= PART_SIZE_CNT_WIDTH)
      report "Unsupported value of PART_NUM_CNT_WIDTH (PART_NUM_CNT_WIDTH > PART_SIZE_CNT_WIDTH)"
      severity failure;

   -- Assertions
   assert (log2(MAX_PARTS) <= PART_NUM_CNT_WIDTH)
      report "Unsupported value of PART_NUM_CNT_WIDTH"
      severity failure;

   assert (PART_SIZE_CNT_WIDTH <= 32)
      report "Unsupported value of PART_SIZE_CNT_WIDTH"
      severity failure;

-- -- REGISTERS PROCESSING UNIT INSTANCE --
   reg_proc_unit_i : entity work.reg_proc_unit
   generic map(
      DATA_WIDTH          => DATA_WIDTH,
      PART_NUM_CNT_WIDTH  => PART_NUM_CNT_WIDTH,
      PART_SIZE_CNT_WIDTH => PART_SIZE_CNT_WIDTH
   )
   port map(
      CLK      => CLK,
      RESET    => RESET,
      
      -- MI32 interface
      MI_DWR   => sig_mi_dwr,
      MI_ADDR  => sig_mi_addr,
      MI_RD    => sig_mi_rd,
      MI_WR    => sig_mi_wr,
      MI_BE    => sig_mi_be,
      MI_DRD   => sig_mi_drd,
      MI_ARDY  => sig_mi_ardy,
      MI_DRDY  => sig_mi_drdy,
      
      -- Generator interface
      GEN_FLOW => sig_gen_flow,
      
      -- Output interface
      PART_SIZE        => sig_part_size_in,
      PART_SIZE_VLD    => sig_size_vld,
      PART_SIZE_TAKE   => sig_size_take,

      IS_LAST_IN_FRAME => sig_last
   );

-- -- ORD FIFO INSTANCE --
   fifo_sync_ord_i : entity work.fifo_sync_ord
   generic map(
      MEM_TYPE   => 0,  -- LUT
      LATENCY    => 1,
      ITEMS      => 16,
      ITEM_WIDTH => PART_SIZE_CNT_WIDTH, 
      PREFETCH   => false
   )
   
   port map(
      CLK      => CLK,
      RESET    => RESET,
      
      WR       => sig_size_vld,
      DI       => sig_part_size_in,

      RD       => sig_part_complete,
      DO       => sig_part_size_out,
      DO_DV    => open,

      FULL     => sig_fifo_full,
      EMPTY    => sig_fifo_empty,
      STATUS   => open
   );
 
   sig_size_take <= not sig_fifo_full;

-- -- DATA SIZE PROCESSING UNIT INSTANCE --
   data_size_proc_unit_i : entity work.data_size_proc_unit   
   generic map(
      DATA_WIDTH => PART_SIZE_CNT_WIDTH
   )
   
   port map(
      CLK      => CLK,
      RESET    => RESET,

      -- Input interface
      PART_SIZE      => sig_part_size_out,
      PART_SIZE_VLD  => sig_fifo_empty,
      PART_COMPLETE  => sig_part_complete,
      
      -- Output interface
      DATA_SIZE      => sig_data_size,
      DATA_SIZE_VLD  => sig_data_size_vld,
      DATA_REQUEST   => sig_data_complete
   );

-- -- DATA PROCESSING UNIT INSTANCE --
   data_proc_unit_i : entity work.data_proc_unit   
   generic map(
      DATA_WIDTH => DATA_WIDTH,
      SIZE_WIDTH => PART_SIZE_CNT_WIDTH
   )
   
   port map(
      CLK      => CLK,
      RESET    => RESET,
   
      -- Data Part processing interface
      DATA_SIZE     => sig_data_size, 
      DATA_SIZE_VLD => sig_data_size_vld,
      
      -- Data processing interface
      DATA_REQUEST  => sig_data_request,
      DATA_RDY      => sig_data_ready,
      DATA_REM      => sig_rem,
      DATA_COMPLETE => sig_data_complete
   ); 
   
   sig_data_request <= (not is_header) and DST_RDY_N; 
   
-- -- CONTROL FINITE STATE MACHINE --  
  
-- -- state logic
   fsm_state_logic : process (CLK)
   begin
     if (rising_edge(CLK)) then
        if (RESET='1') then
          state_reg <= header_state;
        else
          state_reg <= state_next;
        end if;   
     end if;   
   end process;
   
   -- next state logic
   fsm_next_state_logic : process (state_reg)
   begin
     state_next <= state_reg;  
     
     case state_reg is
        when header_state =>
          state_next <= data_state;
          
        when data_state =>
          if (sig_data_complete = '1') then
              state_next <= header_state; 
          else 
              state_next <= data_state;
          end if; 
     end case;      
   end process;
   
   -- Moore output logic
   moore_output : process (state_reg)
   begin
      -- default values
      is_header    <= '0';
                  
      case state_reg is
         when header_state => 
            is_header <= '1';
            if (sig_last = '0' and sig_part_complete = '0') then
                sig_header_type <= SOME_PART_UNCOMPLETE;
            elsif (sig_last = '0' and sig_part_complete = '1') then   
                sig_header_type <= SOME_PART_COMPLETE; 
            elsif (sig_last = '1' and sig_part_complete = '0') then   
                sig_header_type <= LAST_PART_UNCOMPLETE;   
            elsif (sig_last = '1' and sig_part_complete = '1') then   
                sig_header_type <= LAST_PART_COMPLETE;   
            end if; 
         when data_state => 
            is_header <= '0';
      end case;   
   end process moore_output; 
     
-- -- OUTPUT FRAMELINK SETTINGS --

-- header type multiplexer 
   header_type_mux : process (sig_header_type)
   begin
      sig_header <= (others => '0');

      case sig_header_type is
         when SOME_PART_UNCOMPLETE => 
            sig_header(63 downto 48) <= SOME_PART_UNCOMPLETE_INFO;
            sig_header(47 downto 40) <= X"00";
            sig_header(39 downto 32) <= DATA_TRANS_TYPE;
            sig_header(31 downto 24) <= X"00";
            sig_header(23 downto 16) <= X"00";
            sig_header(15 downto 8)  <= FL_PROTOCOL_ID;
            sig_header( 7 downto 0)  <= ENDPOINT_TAG;
         
         when SOME_PART_COMPLETE   => 
            sig_header(63 downto 48) <= SOME_PART_COMPLETE_INFO;
            sig_header(47 downto 40) <= X"00";
            sig_header(39 downto 32) <= DATA_TRANS_TYPE;
            sig_header(31 downto 24) <= X"00";
            sig_header(23 downto 16) <= X"00";
            sig_header(15 downto 8)  <= FL_PROTOCOL_ID;
            sig_header( 7 downto 0)  <= ENDPOINT_TAG;
        
         when LAST_PART_UNCOMPLETE => 
            sig_header(63 downto 48) <= LAST_PART_UNCOMPLETE_INFO;
            sig_header(47 downto 40) <= X"00";
            sig_header(39 downto 32) <= DATA_TRANS_TYPE;
            sig_header(31 downto 24) <= X"00";
            sig_header(23 downto 16) <= X"00";
            sig_header(15 downto 8)  <= FL_PROTOCOL_ID;
            sig_header( 7 downto 0)  <= ENDPOINT_TAG;
            
         when LAST_PART_COMPLETE   => 
            sig_header(63 downto 48) <= LAST_PART_COMPLETE_INFO;
            sig_header(47 downto 40) <= X"00";
            sig_header(39 downto 32) <= DATA_TRANS_TYPE;
            sig_header(31 downto 24) <= X"00";
            sig_header(23 downto 16) <= X"00";
            sig_header(15 downto 8)  <= FL_PROTOCOL_ID;
            sig_header( 7 downto 0)  <= ENDPOINT_TAG;
            
         when others => null;   
      end case;   
   end process;
   
-- data register
   data_reg : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then 
            sig_data_out <= (others => '0');
         elsif (sig_data_ready = '1') then
            sig_data_out <= GEN_FLOW;  
         end if;   
      end if;
   end process; 
   
-- data - header multiplexer
   data_header_mux : process (is_header, sig_data_out, sig_header)
   begin
      DATA <= (others => '0');

      case is_header is
         when '0'    => DATA <= sig_data_out;
         when '1'    => DATA <= sig_header;
         when others => null;   
      end case;   
   end process;     
   
-- rem multiplexer
   rem_mux : process (is_header, sig_rem)
   begin
      D_REM <= (others => '0');

      case is_header is
         when '0'    => D_REM <= sig_rem;
         when '1'    => D_REM <= (others => '1');
         when others => null;   
      end case;   
   end process;     

   SRC_RDY_N <= not sig_data_ready;
   SOF_N     <= not is_header;
   SOP_N     <= not is_header;
   EOF_N     <= not sig_data_complete; 
   EOP_N     <= not sig_data_complete;

end architecture;
