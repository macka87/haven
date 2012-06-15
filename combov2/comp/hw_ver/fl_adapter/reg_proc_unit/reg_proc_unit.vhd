--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Adapter
-- Description:  Drives and processes the bitflow from generator according to
--               request from software.
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         12.6.2013 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity FL_REG_PROC_UNIT is

   generic
   (
      -- data width
      DATA_WIDTH  : integer := 64;
      -- the width of the maximum number of parts counter (the maximum size is
      -- 2^PART_NUM_CNT_WIDTH)
      PART_NUM_CNT_WIDTH : integer := 3;
      -- the width of the maximum size of a part counter (the maximum size is
      -- 2^PART_SIZE)
      PART_SIZE_CNT_WIDTH : integer := 32
   );

   port
   (
      CLK   : in std_logic;
      RESET : in std_logic;

      -- MI32 interface
      MI_DWR    :  in std_logic_vector(31 downto 0);
      MI_ADDR   :  in std_logic_vector(31 downto 0);
      MI_RD     :  in std_logic;
      MI_WR     :  in std_logic;
      MI_BE     :  in std_logic_vector( 3 downto 0);
      MI_DRD    : out std_logic_vector(31 downto 0);
      MI_ARDY   : out std_logic;
      MI_DRDY   : out std_logic;
      
      -- Generator interface
      GEN_FLOW  :  in std_logic_vector(DATA_WIDTH-1 downto 0);
      
      -- Output interface
      
      PARTS_NUM     : out std_logic_vector(PART_NUM_CNT_WIDTH-1 downto 0);   -- Number of FL parts
      PARTS_NUM_VLD : out std_logic;                      -- Parts num valid
      PART_SIZE     : out std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0); -- Part size
      PART_SIZE_VLD : out std_logic                      -- Part size valid
   );       
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of FL_REG_PROC_UNIT is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- TODO: infer this from PART_NUM_CNT_WIDTH?
constant COUNT : integer := 7;

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- interface signals 
   signal sig_dwr                : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sig_addr               : std_logic_vector(DATA_WIDTH-1 downto 0);
   
-- register signals
   signal sig_mask               : std_logic_vector(COUNT*PART_SIZE_CNT_WIDTH-1 downto 0);
   signal sig_base               : std_logic_vector(COUNT*PART_SIZE_CNT_WIDTH-1 downto 0);
   signal sig_max                : std_logic_vector(COUNT*PART_SIZE_CNT_WIDTH-1 downto 0);
   
-- processing of part number signals        
   signal sig_parts_number       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sig_parts_number_vld   : std_logic;
   signal sig_parts_reg_number   : std_logic_vector(PART_NUM_CNT_WIDTH-1 downto 0);
   signal sig_counter_reg_out    : std_logic_vector(PART_NUM_CNT_WIDTH-1 downto 0);
   signal sig_counter_value      : std_logic_vector(PART_NUM_CNT_WIDTH-1 downto 0);
   
-- processing of size of parts signals  
   signal sig_part_mask          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sig_part_base          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sig_part_max           : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sig_size               : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sig_size_vld           : std_logic;

begin

sig_dwr  <= MI_DWR;
sig_addr <= MI_ADDR;

-- --------------- RECEIVING THE CONTENT OF REGISTERS FROM SOFTWARE -----
-- the register
   output_reg_p: process (CLK, sig_addr)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            for i in 0 to COUNT-1 loop
               sig_mask(i*DATA_WIDTH+(DATA_WIDTH-1) downto i*DATA_WIDTH) 
                  <= (others => '0');
               sig_base(i*DATA_WIDTH+(DATA_WIDTH-1) downto i*DATA_WIDTH) 
                  <= (others => '0');
               sig_max(i*DATA_WIDTH+(DATA_WIDTH-1) downto i*DATA_WIDTH)  
                  <= (others => '0');
            end loop;
         elsif (MI_WR = '1') then
            for i in 0 to COUNT-1 loop
              if (i = sig_addr(6 downto 4)) then 
                 case (sig_addr(3 downto 2)) is
                    when "00" 
                    => sig_mask(i*DATA_WIDTH+(DATA_WIDTH-1) downto i*DATA_WIDTH)
                          <= sig_dwr;
                    when "01"
                    => sig_base(i*DATA_WIDTH+(DATA_WIDTH-1) downto i*DATA_WIDTH)
                          <= sig_dwr;
                    when "10" 
                    => sig_max(i*DATA_WIDTH+(DATA_WIDTH-1) downto i*DATA_WIDTH)
                          <= sig_dwr;
                    when others => null;
                 end case;
              end if;   
            end loop; 
         end if;
      end if;
   end process; 

-- MI32 connection

   -- The address ready signal
   MI_ARDY <= MI_RD OR MI_WR;

   -- The data ready signal
   MI_DRDY <= MI_RD;

   -- output MI32 data
   MI_DRD <= X"00011ACA";
   
-- --------------- GENERATION OF PARTS' NUMBER --------------------------

-- sig_mask(7) = num_parts_range_mask
-- sig_base(7) = num_parts_base
-- sig_max(7)  = num_parts_max 

-- gen_proc_unit instance --
   gen_proc_unit_i : entity work.gen_proc_unit
   generic map(
      DATA_WIDTH   => DATA_WIDTH
   )
   port map(
      CLK        => CLK,
      RESET      => RESET,

      GEN_DATA   => GEN_FLOW,
      MASK       => sig_mask(6*DATA_WIDTH+(DATA_WIDTH-1) downto 6*DATA_WIDTH),
      BASE       => sig_base(6*DATA_WIDTH+(DATA_WIDTH-1) downto 6*DATA_WIDTH),
      MAX        => sig_max(6*DATA_WIDTH+(DATA_WIDTH-1) downto 6*DATA_WIDTH),
      
      -- output interface
      OUTPUT     => sig_parts_number,
      OUTPUT_VLD => sig_parts_number_vld
   );
   
   PARTS_NUM     <= sig_parts_number(2 downto 0); 
   PARTS_NUM_VLD <= sig_parts_number_vld;  

-- register for parts number
   parts_num_reg_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            sig_parts_reg_number <= (others => '0');
         elsif (sig_parts_number_vld = '1') then
            sig_parts_reg_number <= sig_parts_number(2 downto 0); 
         end if;
      end if;
   end process; 

-- register for counter values
   counter_reg_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            sig_counter_reg_out <= (others => '0');
         elsif (sig_size_vld = '1') then
            sig_counter_reg_out <= sig_counter_value; 
         end if;
      end if;
   end process;   
   
-- comparator for counter value and parts number
   part_num_comp : process (sig_counter_reg_out, sig_parts_reg_number)
   begin
      sig_counter_value <= (others => '0');

      if (sig_counter_reg_out = sig_parts_reg_number) then sig_counter_value <= (others => '0');
      else sig_counter_value <= sig_counter_reg_out + 1;
      end if;
   end process;

-- --------------- GENERATION OF PARTS' SIZES ---------------------------

-- sig_mask(0 - 6) = num_parts_range_mask
-- sig_base(0 - 6) = num_parts_base
-- sig_max(0 - 6)  = num_parts_max 

-- mask processing multiplexer
   mask_mux : process (sig_counter_reg_out, sig_mask)
   begin
      sig_part_mask <= (others => '0');

      for i in 0 to COUNT-1 loop
         if (i = sig_counter_reg_out) then 
            sig_part_mask <= sig_mask(i*32+31 downto i*32);
         end if;
      end loop;

      -- case sig_counter_reg_out is
      --   when '000'    => sig_part_mask <= sig_mask(0);
      --   when '001'    => sig_part_mask <= sig_mask(1);
      --   when '010'    => sig_part_mask <= sig_mask(2);
      --   when '011'    => sig_part_mask <= sig_mask(3);
      --   when '100'    => sig_part_mask <= sig_mask(4);
      --   when '101'    => sig_part_mask <= sig_mask(5);
      --   when '110'    => sig_part_mask <= sig_mask(6);
      -- end case;   
   end process;
   
-- base processing multiplexer
   base_mux : process (sig_counter_reg_out, sig_base)
   begin
      sig_part_base <= (others => '0');

      for i in 0 to COUNT-1 loop
         if (i = sig_counter_reg_out) then 
            sig_part_base <= sig_base(i*DATA_WIDTH+(DATA_WIDTH-1) downto i*DATA_WIDTH);
         end if;
      end loop;

      -- case sig_counter_reg_out is
      --   when '000'    => sig_part_base <= sig_base(0);
      --   when '001'    => sig_part_base <= sig_base(1);
      --   when '010'    => sig_part_base <= sig_base(2);
      --   when '011'    => sig_part_base <= sig_base(3);
      --   when '100'    => sig_part_base <= sig_base(4);
      --   when '101'    => sig_part_base <= sig_base(5);
      --   when '110'    => sig_part_base <= sig_base(6);
      -- end case;   
   end process;  
   
-- maximum processing multiplexer
   maximum_mux : process (sig_counter_reg_out, sig_max)
   begin
      sig_part_max <= (others => '0');

      for i in 0 to COUNT-1 loop
         if (i = sig_counter_reg_out) then 
            sig_part_max <= sig_max(i*DATA_WIDTH+(DATA_WIDTH-1) downto i*DATA_WIDTH);
         end if;
      end loop;

      -- case sig_counter_reg_out is
      --   when '000'    => sig_part_max <= sig_max(0);
      --   when '001'    => sig_part_max <= sig_max(1);
      --   when '010'    => sig_part_max <= sig_max(2);
      --   when '011'    => sig_part_max <= sig_max(3);
      --   when '100'    => sig_part_max <= sig_max(4);
      --   when '101'    => sig_part_max <= sig_max(5);
      --   when '110'    => sig_part_max <= sig_max(6);
      -- end case;   
   end process;    
   
-- gen_proc_unit instance --
   gen_proc_unit_ii : entity work.gen_proc_unit
   generic map(
      DATA_WIDTH   => DATA_WIDTH
   )
   port map(
      CLK        => CLK,
      RESET      => RESET,

      GEN_DATA   => GEN_FLOW,
      MASK       => sig_part_mask,
      BASE       => sig_part_base,
      MAX        => sig_part_max,
      
      -- output interface
      OUTPUT     => sig_size,
      OUTPUT_VLD => sig_size_vld
   );  
   
   PART_SIZE     <= sig_size; 
   PART_SIZE_VLD <= sig_size_vld;   
  
end architecture;
