--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Command Unit
-- Description:  Sends command frames for input FrameLink protocol.
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

-- This unit sends command frames for the input FrameLink protocol as set via
-- the MI32 interface.
entity FL_COMMAND_UNIT is

   generic
   (
      -- data width
      DATA_WIDTH     : integer := 64;
      -- endpoint ID
      ENDPOINT_ID    : std_logic_vector(7 downto 0);
      -- ID of the FrameLink protocol
      FL_PROTOCOL_ID : std_logic_vector(7 downto 0)
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
      
      -- Output FrameLink Interface
      TX_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM       : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N : out std_logic;
      TX_DST_RDY_N : in  std_logic;
      TX_SOP_N     : out std_logic;
      TX_EOP_N     : out std_logic;
      TX_SOF_N     : out std_logic;
      TX_EOF_N     : out std_logic
   );       
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of FL_COMMAND_UNIT is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- input signals
signal sig_mi_dwr    : std_logic_vector(31 downto 0);
signal sig_mi_addr   : std_logic_vector(31 downto 0);
signal sig_mi_rd     : std_logic;
signal sig_mi_wr     : std_logic;
signal sig_mi_be     : std_logic_vector( 3 downto 0);
signal sig_mi_drd    : std_logic_vector(31 downto 0);
signal sig_mi_ardy   : std_logic;
signal sig_mi_drdy   : std_logic;

-- output signals
signal sig_tx_data            : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_tx_rem             : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal sig_tx_sof_n           : std_logic;
signal sig_tx_eof_n           : std_logic;
signal sig_tx_sop_n           : std_logic;
signal sig_tx_eop_n           : std_logic;
signal sig_tx_src_rdy_n       : std_logic;
signal sig_tx_dst_rdy_n       : std_logic;

-- the header
signal header       : std_logic_vector(DATA_WIDTH-1 downto 0);

-- the send register
signal reg_send        : std_logic;
signal reg_send_set    : std_logic;
signal reg_send_clr    : std_logic;

begin

   assert (DATA_WIDTH = 64)
      report "Invalid DATA_WIDTH!"
      severity failure;

   -- mapping input signals
   sig_mi_dwr       <= MI_DWR;
   sig_mi_addr      <= MI_ADDR;
   sig_mi_rd        <= MI_RD;
   sig_mi_wr        <= MI_WR;
   sig_mi_be        <= MI_BE;
   MI_DRD           <= sig_mi_drd;
   MI_ARDY          <= sig_mi_ardy;
   MI_DRDY          <= sig_mi_drdy;

   -- handle MI32 signals
   sig_mi_ardy      <= sig_mi_wr OR sig_mi_rd;
   sig_mi_drdy      <= sig_mi_rd;
   sig_mi_drd       <= X"C011A1D0";

   --
   reg_send_set     <= sig_mi_dwr(0) AND sig_mi_wr;
   reg_send_clr     <= NOT sig_tx_dst_rdy_n;

   -- the register that is set when it is desired to send the control frame
   reg_send_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_send <= '0';
         elsif (reg_send_set = '1') then
            reg_send <= '1';
         elsif (reg_send_clr = '1') then
            reg_send <= '0';
         end if;
      end if;
   end process;

   -- the header
   header(63 downto 40) <= (others => '0');
   header(39 downto 32) <= X"04";    -- WAIT FOREVER
   header(31 downto 24) <= X"00";
   header(23 downto 16) <= X"00";
   header(15 downto 8)  <= FL_PROTOCOL_ID;
   header( 7 downto 0)  <= ENDPOINT_ID;

   -- FrameLink signals
   sig_tx_data        <= header;
   sig_tx_rem         <= (others => '1');
   sig_tx_sof_n       <= '0';
   sig_tx_eof_n       <= '0';
   sig_tx_sop_n       <= '0';
   sig_tx_eop_n       <= '0';
   sig_tx_src_rdy_n   <= NOT reg_send;

   -- mapping output signals
   TX_DATA          <= sig_tx_data;
   TX_REM           <= sig_tx_rem;
   TX_SOF_N         <= sig_tx_sof_n;
   TX_SOP_N         <= sig_tx_sop_n;
   TX_EOF_N         <= sig_tx_eof_n; 
   TX_EOP_N         <= sig_tx_eop_n;
   TX_SRC_RDY_N     <= sig_tx_src_rdy_n;
   sig_tx_dst_rdy_n <= TX_DST_RDY_N;

end architecture;
