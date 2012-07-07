-- --------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    TX Asynchronous FrameLink Unit Output Register
-- Description: 
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================

-- This unit serves as the output part of TX_ASYNC_FL_UNIT. It stores the
-- desired value into the register and provides it at the output until it is
-- accepted.
entity OUTPUT_REG is
   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------- INPUT -----------
      -- the value of the ready signal (which should be put at the output
      RDY_IN         : in  std_logic;
      -- write into the register (when active, the RDY_IN signal is directly
      -- passed to SRC_RDY)
      WRITE          : in  std_logic;

      -- ----------- OUTPUT -----------
      SRC_RDY        : out std_logic;
      DST_RDY        :  in std_logic
   );
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of OUTPUT_REG is

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- input signals
signal sig_rdy_in        : std_logic;
signal sig_write         : std_logic;

-- output signals
signal sig_src_rdy       : std_logic;
signal sig_dst_rdy       : std_logic;

-- the register for the RDY signal
signal reg_out_rdy       : std_logic;
signal reg_out_rdy_en    : std_logic;
signal reg_out_rdy_in    : std_logic;

-- the validity register
signal reg_valid         : std_logic;
signal reg_valid_set     : std_logic;
signal reg_valid_clr     : std_logic;

-- the RDY multiplexer
signal mux_rdy_out       : std_logic;
signal mux_rdy_sel       : std_logic;

-- misc signals
signal sig_is_valid_from_reg   : std_logic;

-- ==========================================================================
--                           ARCHITECTURE BODY
-- ==========================================================================
begin

   -- mapping inputs
   sig_rdy_in    <= RDY_IN;
   sig_write     <= WRITE;

   --
   reg_out_rdy_in <= sig_rdy_in;
   reg_out_rdy_en <= sig_write;

   -- the register for the RDY signal
   reg_out_rdy_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (reg_out_rdy_en = '1') then
            reg_out_rdy <= reg_out_rdy_in;
         end if;
      end if;
   end process;

   --
   reg_valid_clr <= sig_dst_rdy;
   reg_valid_set <= sig_write;

   -- the register denoting validity of reg_out_rdy
   reg_valid_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_valid <= '0';
         elsif (reg_valid_clr = '1') then
            reg_valid <= '0';
         elsif (reg_valid_set = '1') then
            reg_valid <= '1';
         end if;
      end if;
   end process;

   --
   mux_rdy_sel           <= sig_write;
   sig_is_valid_from_reg <= reg_out_rdy AND reg_valid;

   -- the multiplexer switching between the RDY value from the input and from
   -- the register
   mux_rdy_p: process(mux_rdy_sel, sig_rdy_in, sig_is_valid_from_reg)
   begin
      mux_rdy_out <= sig_rdy_in;

      case (mux_rdy_sel) is
         when '0'    => mux_rdy_out <= sig_is_valid_from_reg;
         when '1'    => mux_rdy_out <= sig_rdy_in;
         when others => null;
      end case;
   end process;

   sig_src_rdy <= mux_rdy_out;

   -- mapping outputs
   SRC_RDY      <= sig_src_rdy;
   sig_dst_rdy  <= DST_RDY;

end architecture;
