--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Adapter
-- Description:  Processes data parts from data size processing unit. 
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
entity DATA_PROC_UNIT is

   generic
   (
      -- data width of the counter
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
      DATA_SIZE_REQ : out std_logic; 
      
      -- Data processing interface
      DATA_RDY      : out std_logic;
      DATA_REM      : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      DATA_COMPLETE : out std_logic;
      DATA_TAKE     :  in std_logic 
    );       
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of DATA_PROC_UNIT is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- size of the output word
constant BLOCK_SIZE : integer := DATA_WIDTH/8;

-- size of the DREM signal
constant DREM_WIDTH : integer := log2(DATA_WIDTH/8);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- inputs
signal sig_data_size        : std_logic_vector(SIZE_WIDTH-1 downto 0);
signal sig_data_size_vld    : std_logic;
signal sig_data_size_req    : std_logic;

-- outputs
signal sig_data_rem         : std_logic_vector(DREM_WIDTH-1 downto 0);
signal sig_data_rdy         : std_logic;
signal sig_data_complete    : std_logic;
signal sig_data_take        : std_logic;

-- the register for counting the remaining words
signal reg_data             : std_logic_vector(SIZE_WIDTH-1 downto 0);
signal reg_data_in          : std_logic_vector(SIZE_WIDTH-1 downto 0);
signal reg_data_en          : std_logic;

-- the data multiplexor
signal mux_data_out         : std_logic_vector(SIZE_WIDTH-1 downto 0);
signal mux_data_sel         : std_logic;

-- the data valid register
signal reg_valid            : std_logic;
signal reg_valid_set        : std_logic;
signal reg_valid_clr        : std_logic;


-- the comparer
signal sig_cmp_out          : std_logic; 

-- the signal that a part was taken
signal sig_part_taken       : std_logic;

begin

   -- mapping the input signals
   sig_data_size     <= DATA_SIZE;
   sig_data_size_vld <= DATA_SIZE_VLD;
   DATA_SIZE_REQ     <= sig_data_size_req;

   --
   reg_data_in       <= mux_data_out;
   reg_data_en       <= sig_data_take OR (sig_data_size_vld AND (NOT reg_valid));

   -- register for the data size
   reg_data_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (reg_data_en = '1') then
            reg_data <= reg_data_in;
         end if;
      end if;
   end process; 
   
   --
   mux_data_sel <= reg_valid AND (NOT sig_cmp_out);

   -- data mux
   mux_data_p : process (sig_data_size, reg_data, mux_data_sel)
   begin
      mux_data_out <= sig_data_size;

      case mux_data_sel is
         when '0'    => mux_data_out <= sig_data_size;
         when '1'    => mux_data_out <= reg_data - BLOCK_SIZE;
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

   sig_data_rdy    <= reg_valid;
   
   -- data size comparator
   data_size_cmp : process (reg_data)
   begin
      sig_cmp_out <= '0';

      if (reg_data <= BLOCK_SIZE) then 
        sig_cmp_out <= '1';
      else 
        sig_cmp_out <= '0';
      end if;
   end process;  
   
   sig_data_complete <= sig_cmp_out;

   sig_part_taken    <= sig_cmp_out AND sig_data_take;
   sig_data_size_req <= sig_part_taken OR (NOT reg_valid);

   sig_data_rem <= reg_data(DREM_WIDTH-1 downto 0) - 1;


   -- mapping the output signals
   DATA_COMPLETE <= sig_data_complete;
   DATA_REM      <= sig_data_rem;
   DATA_RDY      <= sig_data_rdy;
   sig_data_take <= DATA_TAKE;

end architecture;
