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
entity REG_PROC_UNIT is

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
      PARTS_NUM_TAKE:  in std_logic;                      -- take signal for parts num

      PART_SIZE     : out std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0); -- Part size
      PART_SIZE_VLD : out std_logic;                     -- Part size valid
      PART_SIZE_TAKE:  in std_logic                      -- take signal for part size
   );       
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of REG_PROC_UNIT is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- the maximum number of parts in a frame
constant MAX_PARTS            : integer := 8;

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- interface signals 
signal sig_mi_dwr             : std_logic_vector(31 downto 0);
signal sig_mi_addr            : std_logic_vector(31 downto 0);
signal sig_mi_wr              : std_logic;
signal sig_mi_rd              : std_logic;

-- the RUN register
signal reg_run                : std_logic;
signal reg_run_sel            : std_logic;

-- the register with the number of transactions
signal reg_trans              : std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0);
signal reg_trans_sel          : std_logic;

-- register for numbers of parts
signal reg_num_mask           : std_logic_vector(PART_NUM_CNT_WIDTH-1 downto 0);
signal reg_num_base           : std_logic_vector(PART_NUM_CNT_WIDTH-1 downto 0);
signal reg_num_max            : std_logic_vector(PART_NUM_CNT_WIDTH-1 downto 0);
signal regs_num_sel           : std_logic;

-- registers for sizes of parts
signal reg_size_mask          : std_logic_vector(MAX_PARTS*PART_SIZE_CNT_WIDTH-1 downto 0);
signal reg_size_base          : std_logic_vector(MAX_PARTS*PART_SIZE_CNT_WIDTH-1 downto 0);
signal reg_size_max           : std_logic_vector(MAX_PARTS*PART_SIZE_CNT_WIDTH-1 downto 0);
signal regs_size_sel          : std_logic;

-- processing of part number signals        
signal sig_parts_number       : std_logic_vector(PART_NUM_CNT_WIDTH-1 downto 0);
signal sig_parts_number_vld   : std_logic;
signal sig_parts_number_take  : std_logic;

signal sig_parts_reg_number   : std_logic_vector(PART_NUM_CNT_WIDTH-1 downto 0);
signal sig_counter_reg_out    : std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0);
signal sig_counter_value      : std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0);

-- processing of size of parts signals  
signal sig_part_mask          : std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0);
signal sig_part_base          : std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0);
signal sig_part_max           : std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0);

signal sig_size               : std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0);
signal sig_size_vld           : std_logic;
signal sig_size_take          : std_logic;

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

   -- ---------- mapping of input signals -----------------------------------
   sig_mi_dwr  <= MI_DWR;
   sig_mi_addr <= MI_ADDR;
   sig_mi_wr   <= MI_WR;
   sig_mi_rd   <= MI_RD;

   -- -------- registers for the ranges of numbers of parts -----------------
   regs_num_p: process (CLK, sig_mi_addr, regs_num_sel)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_num_mask <= (others => '0');
            reg_num_base <= (others => '0');
            reg_num_max <= (others => '0');
         elsif ((regs_num_sel = '1') AND (sig_mi_wr = '1')) then
            case (sig_mi_addr(3 downto 2)) is
               when "00" => reg_num_mask <= sig_mi_dwr(PART_NUM_CNT_WIDTH-1 downto 0);
               when "01" => reg_num_base <= sig_mi_dwr(PART_NUM_CNT_WIDTH-1 downto 0);
               when "10" => reg_num_max  <= sig_mi_dwr(PART_NUM_CNT_WIDTH-1 downto 0);
               when others => null;
            end case;
         end if;
      end if;
   end process; 

   -- ------- address decoder -----------------------------------------------
   addr_dec_p: process(sig_mi_addr)
   begin
      reg_run_sel    <= '0';
      reg_trans_sel  <= '0';
      regs_num_sel   <= '0';
      regs_size_sel <= '0';

      case (sig_mi_addr(7)) is
         when '0' =>
            case (sig_mi_addr(4 downto 3)) is
               when "00" => reg_run_sel   <= '1';   -- the run register
               when "01" => reg_trans_sel <= '1';   -- count of transactions
               when "10" => regs_num_sel  <= '1';   -- numbers of parts
               when others => null;
            end case;
         when '1' => regs_size_sel <= '1';          -- sizes of parts
         when others => null;
      end case;
   end process;

   -- --------------- RECEIVING THE CONTENT OF REGISTERS FROM SOFTWARE -----
   -- the register
   regs_size_p: process (CLK, sig_mi_addr, regs_size_sel)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_size_mask <= (others => '0');
            reg_size_base <= (others => '0');
            reg_size_max <= (others => '0');
         elsif ((regs_size_sel = '1') AND (sig_mi_wr = '1')) then
            for i in 0 to MAX_PARTS-1 loop
              if (i = sig_mi_addr(6 downto 4)) then 
                 case (sig_mi_addr(3 downto 2)) is
                    when "00" =>
                     reg_size_mask((i+1)*PART_SIZE_CNT_WIDTH-1 downto i*PART_SIZE_CNT_WIDTH)
                          <= sig_mi_dwr(PART_SIZE_CNT_WIDTH-1 downto 0);
                    when "01" =>
                       reg_size_base((i+1)*PART_SIZE_CNT_WIDTH-1 downto i*PART_SIZE_CNT_WIDTH)
                          <= sig_mi_dwr(PART_SIZE_CNT_WIDTH-1 downto 0);
                    when "10" =>
                       reg_size_max((i+1)*PART_SIZE_CNT_WIDTH-1 downto i*PART_SIZE_CNT_WIDTH)
                          <= sig_mi_dwr(PART_SIZE_CNT_WIDTH-1 downto 0);
                    when others => null;
                 end case;
              end if;   
            end loop; 
         end if;
      end if;
   end process; 

-- MI32 connection

   -- The address ready signal
   MI_ARDY <= sig_mi_rd OR sig_mi_wr;

   -- The data ready signal
   MI_DRDY <= sig_mi_rd;

   -- output MI32 data
   MI_DRD <= X"00011ACA";
   
-- --------------- GENERATION OF PARTS' NUMBER --------------------------

-- gen_proc_unit instance --
   gen_proc_unit_num_i : entity work.gen_proc_unit
   generic map(
      DATA_WIDTH   => PART_NUM_CNT_WIDTH
   )
   port map(
      CLK        => CLK,
      RESET      => RESET,

      GEN_DATA   => GEN_FLOW(PART_NUM_CNT_WIDTH-1 downto 0),
      MASK       => reg_num_mask,
      BASE       => reg_num_base,
      MAX        => reg_num_max,
      
      -- output interface
      OUTPUT     => sig_parts_number,
      OUTPUT_VLD => sig_parts_number_vld,
      OUTPUT_TAKE=> sig_parts_number_take
   );
   
   PARTS_NUM             <= sig_parts_number; 
   PARTS_NUM_VLD         <= sig_parts_number_vld;  
   sig_parts_number_take <= PARTS_NUM_TAKE;

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

-- mask/base/max processing multiplexer
   mask_mux : process (sig_counter_reg_out, reg_size_mask, reg_size_base, reg_size_max)
   begin
      sig_part_mask <= (others => '0');
      sig_part_base <= (others => '0');
      sig_part_max  <= (others => '0');

      for i in 0 to MAX_PARTS-1 loop
         if (i = sig_counter_reg_out) then 
            sig_part_mask <= reg_size_mask((i+1)*PART_SIZE_CNT_WIDTH-1 downto i*PART_SIZE_CNT_WIDTH);
            sig_part_base <= reg_size_base((i+1)*PART_SIZE_CNT_WIDTH-1 downto i*PART_SIZE_CNT_WIDTH);
            sig_part_max  <= reg_size_max ((i+1)*PART_SIZE_CNT_WIDTH-1 downto i*PART_SIZE_CNT_WIDTH);
         end if;
      end loop;
   end process;
   
-- gen_proc_unit instance --
   gen_proc_unit_size_i : entity work.gen_proc_unit
   generic map(
      DATA_WIDTH   => PART_SIZE_CNT_WIDTH
   )
   port map(
      CLK        => CLK,
      RESET      => RESET,

      GEN_DATA   => GEN_FLOW(PART_SIZE_CNT_WIDTH-1 downto 0),
      MASK       => sig_part_mask,
      BASE       => sig_part_base,
      MAX        => sig_part_max,
      
      -- output interface
      OUTPUT     => sig_size,
      OUTPUT_VLD => sig_size_vld,
      OUTPUT_TAKE=> sig_size_take
   );  
   
   PART_SIZE     <= sig_size; 
   PART_SIZE_VLD <= sig_size_vld;   
   sig_size_take <= PART_SIZE_TAKE;
  
end architecture;
