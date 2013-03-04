--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Adapter
-- Description:  Processes data parts segments' sizes and generates delays
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         16.6.2013 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity DELAY_PROC_UNIT is

   generic
   (
      -- width of the data size counter
      SIZE_WIDTH  : integer := 12;
      -- data width of the output FrameLink
      DATA_WIDTH  : integer := 64
   );

   port
   (
      CLK   : in std_logic;
      RESET : in std_logic;

      -- Data Size Part processing interface
      DATA_SIZE     :  in std_logic_vector(SIZE_WIDTH-1 downto 0);  
      DATA_SIZE_VLD :  in std_logic; 
      DATA_SIZE_TAKE: out std_logic; 
      
      -- Delay interface
      DELAY_RDY     : out std_logic;
      DELAY_REM     : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      DELAY_LAST    : out std_logic;
      DELAY_TAKE    :  in std_logic 
    );       
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of DELAY_PROC_UNIT is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- size of the output word
constant BLOCK_SIZE : integer := DATA_WIDTH/8;

-- size of the DREM signal
constant DREM_WIDTH : integer := log2(DATA_WIDTH/8);

-- width of the delay counter 
constant TRIMMED_SIZE_WIDTH : integer := SIZE_WIDTH - log2(BLOCK_SIZE);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- inputs
signal sig_data_size        : std_logic_vector(SIZE_WIDTH-1 downto 0);
signal sig_data_size_vld    : std_logic;
signal sig_data_size_take   : std_logic;

-- outputs
signal sig_delay_rem         : std_logic_vector(DREM_WIDTH-1 downto 0);
signal sig_delay_rdy         : std_logic;
signal sig_delay_last        : std_logic;
signal sig_delay_take        : std_logic;

-- the register for counting the remaining words
signal reg_delay             : std_logic_vector(TRIMMED_SIZE_WIDTH-1 downto 0);
signal reg_delay_in          : std_logic_vector(TRIMMED_SIZE_WIDTH-1 downto 0);
signal reg_delay_en          : std_logic;

-- the data multiplexor
signal mux_data_out         : std_logic_vector(TRIMMED_SIZE_WIDTH-1 downto 0);
signal mux_data_sel         : std_logic;

-- the data valid register
signal reg_valid            : std_logic;
signal reg_valid_set        : std_logic;
signal reg_valid_clr        : std_logic;

-- the input decrementor
signal dec_data_size         : std_logic_vector(SIZE_WIDTH-1 downto 0);
signal dec_data_size_trimmed : std_logic_vector(TRIMMED_SIZE_WIDTH-1 downto 0);

-- the comparer
signal sig_cmp_out          : std_logic; 

-- the signal that a part was taken
signal sig_part_taken       : std_logic;

begin

   -- mapping the input signals
   sig_data_size     <= DATA_SIZE;
   sig_data_size_vld <= DATA_SIZE_VLD;
   DATA_SIZE_TAKE    <= sig_data_size_take;

   --
   dec_data_size         <= sig_data_size + (BLOCK_SIZE-1);
   dec_data_size_trimmed <= dec_data_size(SIZE_WIDTH-1 downto log2(BLOCK_SIZE));

   --
   reg_delay_in      <= mux_data_out;
   reg_delay_en      <= sig_delay_take OR (sig_data_size_vld AND (NOT reg_valid));

   -- register for the data size
   reg_data_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (reg_delay_en = '1') then
            reg_delay <= reg_delay_in;
         end if;
      end if;
   end process; 
   
   --
   mux_data_sel <= reg_valid AND (NOT sig_cmp_out);

   -- data mux
   mux_data_p : process (dec_data_size_trimmed, reg_delay, mux_data_sel)
   begin
      mux_data_out <= dec_data_size_trimmed;

      case mux_data_sel is
         when '0'    => mux_data_out <= dec_data_size_trimmed;
         when '1'    => mux_data_out <= reg_delay - BLOCK_SIZE;
         when others => null;
      end case;
   end process;  
   
   --
   reg_valid_set <= sig_data_size_vld;
   reg_valid_clr <= sig_part_taken;

   -- register for data valid signal
   reg_valid_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_valid <= '0';
         elsif (reg_valid_set = '1') then
            reg_valid <= '1';
         elsif (reg_valid_clr = '1') then
            reg_valid <= '0';
         end if;
      end if;
   end process; 

   sig_delay_rdy    <= reg_valid;
   
   -- delay size comparator
   delay_size_cmp : process (reg_delay)
   begin
      sig_cmp_out <= '0';

      if (reg_delay <= BLOCK_SIZE) then 
        sig_cmp_out <= '1';
      else 
        sig_cmp_out <= '0';
      end if;
   end process;  
   
   sig_delay_last    <= sig_cmp_out;

   sig_part_taken    <= sig_cmp_out AND sig_delay_take;
   sig_data_size_take<= sig_part_taken OR (NOT reg_valid);

   sig_delay_rem     <= reg_delay(DREM_WIDTH-1 downto 0) - 1;


   -- mapping the output signals
   DELAY_LAST     <= sig_delay_last;
   DELAY_REM      <= sig_delay_rem;
   DELAY_RDY      <= sig_delay_rdy;
   sig_delay_take <= DELAY_TAKE;

end architecture;
