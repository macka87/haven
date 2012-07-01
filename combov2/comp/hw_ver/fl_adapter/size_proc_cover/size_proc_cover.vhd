--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Adapter data size cover
-- Description:  A cover over the whole setting of constraints on FrameLink
--               frames.
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
entity SIZE_PROC_COVER is

   generic
   (
      -- data width
      DATA_WIDTH  : integer := 64;
      -- the width of the maximum number of parts counter (the maximum size is
      -- 2^PART_NUM_CNT_WIDTH)
      PART_NUM_CNT_WIDTH : integer := 3;
      -- the width of the maximum size of a part counter (the maximum size is
      -- 2^PART_SIZE_CNT_WIDTH)
      PART_SIZE_CNT_WIDTH : integer := 32;
      -- the width of the maximum size of a data frame (the maximum size is
      -- 2^DATA_SIZE_CNT_WIDTH)
      DATA_SIZE_CNT_WIDTH : integer := 12
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
      
      -- Data size interface (to connect delay_proc_unit)
      DATA_SIZE       : out std_logic_vector(DATA_SIZE_CNT_WIDTH-1 downto 0);
      DATA_SIZE_VLD   : out std_logic;
      DATA_SIZE_TAKE  :  in std_logic;

      -- Output interface
      -- A data word can be sent
      FRAME_RDY            : out std_logic;
      -- this is the last word of the sent segment
      FRAME_LAST_WORD      : out std_logic;
      -- the REM if it is the last word
      FRAME_REM            : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      -- the segment is the last in the part being currently sent
      FRAME_LAST_IN_PART   : out std_logic;
      -- the part is the last in the frame being currently sent
      FRAME_LAST_IN_FRAME  : out std_logic;
      -- acknowledge signal
      FRAME_TAKE           :  in std_logic
   );       
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of SIZE_PROC_COVER is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- width of the REM signal
constant DREM_WIDTH       : integer := log2(DATA_WIDTH/8);

-- width of the FIFO
constant FIFO_WIDTH       : integer := PART_SIZE_CNT_WIDTH + 1;

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- input signals
signal sig_gen_flow             : std_logic_vector(DATA_WIDTH-1 downto 0);

-- the data size interface
signal sig_out_data_size        : std_logic_vector(DATA_SIZE_CNT_WIDTH-1 downto 0);
signal sig_out_data_size_vld    : std_logic;
signal sig_out_data_size_take   : std_logic;

-- output signals
signal sig_frame_rdy            : std_logic;
signal sig_frame_last_word      : std_logic;
signal sig_frame_rem            : std_logic_vector(DREM_WIDTH-1 downto 0);
signal sig_frame_last_in_part   : std_logic;
signal sig_frame_last_in_frame  : std_logic;
signal sig_frame_take           : std_logic;

-- reg_proc_cover signals
signal reg_proc_part_size             : std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0);
signal reg_proc_part_size_vld         : std_logic;
signal reg_proc_part_size_take        : std_logic;
signal reg_proc_part_is_last_in_frame : std_logic;

-- fifo_sync_ord signals
signal fifo_di               : std_logic_vector(FIFO_WIDTH-1 downto 0);
signal fifo_wr               : std_logic;
signal fifo_do               : std_logic_vector(FIFO_WIDTH-1 downto 0);
signal fifo_rd               : std_logic;
signal fifo_do_dv            : std_logic;
signal fifo_full             : std_logic;

-- data_size_proc_unit signals
signal data_size_proc_part_size         : std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0);
signal data_size_proc_part_size_vld     : std_logic;
signal data_size_proc_part_complete     : std_logic;
signal data_size_proc_data_size         : std_logic_vector(DATA_SIZE_CNT_WIDTH-1 downto 0);
signal data_size_proc_data_size_vld     : std_logic;
signal data_size_proc_data_size_is_last : std_logic;
signal data_size_proc_data_size_request : std_logic;

-- data_proc_unit signals
signal data_proc_data_size       : std_logic_vector(DATA_SIZE_CNT_WIDTH-1 downto 0);
signal data_proc_data_size_vld   : std_logic;
signal data_proc_data_size_req   : std_logic;
signal data_proc_data_rdy        : std_logic;
signal data_proc_data_rem        : std_logic_vector(DREM_WIDTH-1 downto 0);
signal data_proc_data_complete   : std_logic;
signal data_proc_data_take       : std_logic;

-- register for the last part in the sent frame for the data_size_proc_unit
signal reg_is_last_part_for_data_size    : std_logic;
signal reg_is_last_part_for_data_size_in : std_logic;
signal reg_is_last_part_for_data_size_en : std_logic;

-- register for the last part in the sent frame for the data_proc_unit
signal reg_is_last_part_for_data         : std_logic;
signal reg_is_last_part_for_data_in      : std_logic;
signal reg_is_last_part_for_data_en      : std_logic;

-- register for the last segment in the sent part for the data_proc_unit
signal reg_is_last_seg         : std_logic;
signal reg_is_last_seg_in      : std_logic;
signal reg_is_last_seg_en      : std_logic;

begin

   -- mapping input signals
   sig_gen_flow      <= GEN_FLOW;

   -- the data size interface
   DATA_SIZE              <= sig_out_data_size;
   DATA_SIZE_VLD          <= sig_out_data_size_vld;
   sig_out_data_size_take <= DATA_SIZE_TAKE;

   sig_out_data_size_vld  <=     data_size_proc_data_size_vld
                             AND data_proc_data_size_req;


   -- -- REGISTERS PROCESSING UNIT INSTANCE --
   reg_proc_unit_i : entity work.reg_proc_unit
   generic map(
      DATA_WIDTH => DATA_WIDTH,
      PART_NUM_CNT_WIDTH => PART_NUM_CNT_WIDTH,
      PART_SIZE_CNT_WIDTH => PART_SIZE_CNT_WIDTH
   )
   port map(
      CLK       => CLK,
      RESET     => RESET,
      
      -- MI32 interface
      MI_DWR    => MI_DWR,
      MI_ADDR   => MI_ADDR,
      MI_RD     => MI_RD,
      MI_WR     => MI_WR,
      MI_BE     => MI_BE,
      MI_DRD    => MI_DRD,
      MI_ARDY   => MI_ARDY,
      MI_DRDY   => MI_DRDY,
      
      -- Generator interface
      GEN_FLOW  => sig_gen_flow,
      
      -- Output interface
      PART_SIZE       => reg_proc_part_size,
      PART_SIZE_VLD   => reg_proc_part_size_vld,
      PART_SIZE_TAKE  => reg_proc_part_size_take,

      IS_LAST_IN_FRAME => reg_proc_part_is_last_in_frame
   );

   reg_proc_part_size_take  <= NOT fifo_full;

   --
   fifo_di <= reg_proc_part_is_last_in_frame & reg_proc_part_size;
   fifo_wr <= reg_proc_part_size_vld;

   -- -- ORD FIFO INSTANCE --
   fifo_sync_ord_i : entity work.fifo_sync_ord
   generic map(
      MEM_TYPE    => 0, -- LUT
      LATENCY     => 1,
      ITEMS       => 16,
      ITEM_WIDTH  => FIFO_WIDTH,
      PREFETCH    => true
   )
   port map(
      CLK      => CLK,
      RESET    => RESET,
      
      WR       => fifo_wr,
      DI       => fifo_di,

      RD       => fifo_rd,
      DO       => fifo_do,
      DO_DV    => fifo_do_dv,

      FULL     => fifo_full,
      EMPTY    => open,
      STATUS   => open
   );

   fifo_rd <= data_size_proc_part_complete;

   --
   data_size_proc_part_size      <= fifo_do(PART_SIZE_CNT_WIDTH-1 downto 0);
   data_size_proc_part_size_vld  <= fifo_do_dv;

   -- -- DATA SIZE PROCESSING UNIT INSTANCE --
   data_size_proc_unit_i : entity work.data_size_proc_unit
   generic map(
      IN_DATA_WIDTH  => PART_SIZE_CNT_WIDTH,
      OUT_DATA_WIDTH => DATA_SIZE_CNT_WIDTH
   )
   port map(
      CLK               => CLK,
      RESET             => RESET,

      -- Input interface
      PART_SIZE         => data_size_proc_part_size,
      PART_SIZE_VLD     => data_size_proc_part_size_vld,
      PART_COMPLETE     => data_size_proc_part_complete,
 
      -- Output interface
      DATA_SIZE         => data_size_proc_data_size,
      DATA_SIZE_VLD     => data_size_proc_data_size_vld,
      DATA_SIZE_IS_LAST => data_size_proc_data_size_is_last,
      DATA_REQUEST      => data_size_proc_data_size_request
   );

   data_size_proc_data_size_request  <=     data_proc_data_size_req
                                        AND sig_out_data_size_take;

   sig_out_data_size                 <= data_size_proc_data_size;

   --
   reg_is_last_part_for_data_size_in <= fifo_do(PART_SIZE_CNT_WIDTH);
   reg_is_last_part_for_data_size_en <= fifo_do_dv AND data_size_proc_part_complete;

   -- register holding the value whether the current part size is for the last
   -- part in the frame for the data_size_proc_unit
   reg_is_last_part_for_data_size_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (reg_is_last_part_for_data_size_en = '1') then
            reg_is_last_part_for_data_size <= reg_is_last_part_for_data_size_in;
         end if;
      end if;
   end process;

   --
   data_proc_data_size     <= data_size_proc_data_size;
   data_proc_data_size_vld <=     data_size_proc_data_size_vld
                              AND sig_out_data_size_take;

   -- -- DATA PROCESSING UNIT INSTANCE --
   data_proc_unit_i : entity work.data_proc_unit
   generic map(
      DATA_WIDTH => DATA_WIDTH,
      SIZE_WIDTH => DATA_SIZE_CNT_WIDTH
   )
   port map(
      CLK              => CLK,
      RESET            => RESET,
   
      -- Data Part processing interface
      DATA_SIZE     => data_proc_data_size,
      DATA_SIZE_VLD => data_proc_data_size_vld,
      DATA_SIZE_REQ => data_proc_data_size_req,
      
      -- Data processing interface
      DATA_RDY      => data_proc_data_rdy,
      DATA_REM      => data_proc_data_rem,
      DATA_COMPLETE => data_proc_data_complete,
      DATA_TAKE     => data_proc_data_take
   ); 

   data_proc_data_take  <= sig_frame_take;
   sig_frame_rdy        <= data_proc_data_rdy;
   sig_frame_last_word  <= data_proc_data_complete;
   sig_frame_rem        <= data_proc_data_rem;

   --
   reg_is_last_part_for_data_in <= reg_is_last_part_for_data_size;
   reg_is_last_part_for_data_en <=     data_proc_data_size_vld
                                   AND data_proc_data_size_req;

   -- register holding the value whether the current part size is for the last
   -- part in the frame for the data_proc_unit
   reg_is_last_part_for_data_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (reg_is_last_part_for_data_en = '1') then
            reg_is_last_part_for_data <= reg_is_last_part_for_data_in;
         end if;
      end if;
   end process;

   sig_frame_last_in_frame <= reg_is_last_part_for_data;

   --
   reg_is_last_seg_in <= data_size_proc_data_size_is_last;
   reg_is_last_seg_en <= reg_is_last_part_for_data_en;

   -- register holding the value whether the current segment size is for the
   -- last segment in the part for the data_proc_unit
   reg_is_last_seg_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (reg_is_last_seg_en = '1') then
            reg_is_last_seg <= reg_is_last_seg_in;
         end if;
      end if;
   end process;

   sig_frame_last_in_part <= reg_is_last_seg;

   -- mapping output signals
   FRAME_RDY           <= sig_frame_rdy;
   FRAME_LAST_WORD     <= sig_frame_last_word;
   FRAME_REM           <= sig_frame_rem;
   FRAME_LAST_IN_PART  <= sig_frame_last_in_part;
   FRAME_LAST_IN_FRAME <= sig_frame_last_in_frame;
   sig_frame_take      <= FRAME_TAKE;

end architecture;
