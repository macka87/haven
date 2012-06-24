--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Adapter
-- Description:  Processes sizes of data parts from FIFO. 
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         15.6.2013 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.numeric_std.all;
use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================

-- the unit splits a value from the input interface of the size IN_DATA_WIDTH
-- into (several) values at the output interface of the size OUT_DATA_WIDTH
-- such that the sum of the output values is equal the input value
entity DATA_SIZE_PROC_UNIT is

   generic
   (
      -- input data width
      IN_DATA_WIDTH  : integer := 32;
      -- the power of 2 to which the blocks will be split
      OUT_DATA_WIDTH : integer := 12
   );

   port
   (
      CLK               : in std_logic;
      RESET             : in std_logic;

      -- Input interface
      PART_SIZE         :  in std_logic_vector(IN_DATA_WIDTH-1 downto 0);
      PART_SIZE_VLD     :  in std_logic;
      PART_COMPLETE     :  out std_logic;
      
      -- Output interface
      DATA_SIZE         :  out std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      DATA_SIZE_VLD     :  out std_logic;
      DATA_SIZE_IS_LAST :  out std_logic;
      DATA_REQUEST      :  in std_logic 
    );       
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of DATA_SIZE_PROC_UNIT is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- the MSB position of the output interface
constant SPLIT_POWER     : integer := OUT_DATA_WIDTH-1;

-- the maximum value produced at the output interface
constant SPLIT_SIZE_VECTOR  : std_logic_vector(OUT_DATA_WIDTH-1 downto 0) :=
   std_logic_vector(to_unsigned(2**SPLIT_POWER, OUT_DATA_WIDTH));


-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- inputs
signal sig_part_size     : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal sig_part_size_vld : std_logic;
signal sig_part_complete : std_logic;

-- outputs
signal sig_data_size          : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal sig_data_size_vld      : std_logic;
signal sig_data_size_is_last  : std_logic;
signal sig_data_request       : std_logic;

-- the register with the data size
signal reg_data_size     : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal reg_data_size_in  : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal reg_data_size_en  : std_logic;

-- the multiplexer for the input of the register
signal mux_data_size_out : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal mux_data_size_sel : std_logic;

-- the validity register
signal reg_valid         : std_logic;
signal reg_valid_set     : std_logic;
signal reg_valid_clr     : std_logic;

-- the output data multiplexer
signal mux_output_data_out : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal mux_output_data_sel : std_logic;

-- the comparator
signal sig_cmp_out       : std_logic;

-- the ``block sent'' signal
signal sig_part_sent     : std_logic;

-- zero comparator
signal cmp_out_zero      : std_logic;


begin

   -- assertions
   assert (OUT_DATA_WIDTH < IN_DATA_WIDTH)
      report "OUT_DATA_WIDTH is not smaller than IN_DATA_WIDTH!"
      severity failure;

   -- mapping of input signals
   sig_part_size      <= PART_SIZE;
   sig_part_size_vld  <= PART_SIZE_VLD;
   PART_COMPLETE      <= sig_part_complete;

   --
   reg_data_size_in <= mux_data_size_out;
   reg_data_size_en <= sig_data_request OR (sig_part_size_vld AND (NOT reg_valid));
   
   -- register for the data size of a part
   reg_data_size_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (reg_data_size_en = '1') then
            reg_data_size <= reg_data_size_in; 
         end if;
      end if;
   end process; 

   --
   mux_data_size_sel <= sig_cmp_out AND reg_valid;

   -- data size mux
   mux_data_size_p: process (sig_part_size, reg_data_size, mux_data_size_sel)
   begin
      mux_data_size_out <= sig_part_size;

      if (mux_data_size_sel = '0') then
         mux_data_size_out <= sig_part_size;
      else 
         mux_data_size_out <= reg_data_size - SPLIT_SIZE_VECTOR;
      end if;  
   end process;

   sig_part_sent <= sig_data_request AND (NOT sig_cmp_out);
   sig_part_complete <= sig_part_sent OR (NOT reg_valid);
   
   -- data size comparator
   data_size_cmp : process (reg_data_size)
   begin
      sig_cmp_out <= '0';

      if (reg_data_size > SPLIT_SIZE_VECTOR) then
         sig_cmp_out <= '1';
      end if;
   end process;

   sig_data_size_is_last <= NOT sig_cmp_out;

   --
   mux_output_data_sel <= sig_cmp_out;

   -- output data mux
   mux_output_data_p: process (reg_data_size, mux_output_data_sel)
   begin
      mux_output_data_out <= reg_data_size(OUT_DATA_WIDTH-1 downto 0);

      if (mux_output_data_sel = '0') then
         mux_output_data_out <= reg_data_size(OUT_DATA_WIDTH-1 downto 0);
      else
         mux_output_data_out <= SPLIT_SIZE_VECTOR;
      end if;
   end process; 
   
   PART_COMPLETE <= sig_part_complete;
   
   --
   reg_valid_set     <= sig_part_size_vld;
   reg_valid_clr     <= sig_part_sent;

   -- register for validity signal
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

   sig_data_size_vld <= reg_valid;

   -- mapping output signals
   DATA_SIZE         <= mux_output_data_out;
   DATA_SIZE_VLD     <= sig_data_size_vld;
   DATA_SIZE_IS_LAST <= sig_data_size_is_last;
   sig_data_request  <= DATA_REQUEST;
   
end architecture;
