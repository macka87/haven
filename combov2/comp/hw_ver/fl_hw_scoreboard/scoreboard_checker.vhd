--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Scoreboard Checker
-- Description: 
-- Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================

-- This component of the HW scoreboard performs checking of equality of
-- FrameLink words on all of input interfaces.
entity SCOREBOARD_CHECKER is

   generic
   (
      -- data width
      DATA_WIDTH  : integer := 64;
      -- number of input interfaces
      INTERFACES     : integer := 2
   );

   port
   (
      -- common signals
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input FrameLink interfaces
      RX_DATA        : in  std_logic_vector(INTERFACES*DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(INTERFACES*log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP_N       : in  std_logic_vector(INTERFACES-1 downto 0);
      RX_EOP_N       : in  std_logic_vector(INTERFACES-1 downto 0);
      RX_SOF_N       : in  std_logic_vector(INTERFACES-1 downto 0);
      RX_EOF_N       : in  std_logic_vector(INTERFACES-1 downto 0);

      -- enable signal
      EN             : in  std_logic;
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- '1' each time there is a mismatch
      MISMATCH       : out std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of SCOREBOARD_CHECKER is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

constant DREM_WIDTH       : integer := log2(DATA_WIDTH/8);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- input signals
signal sig_rx_data        : std_logic_vector(INTERFACES*DATA_WIDTH-1 downto 0);
signal sig_rx_rem         : std_logic_vector(INTERFACES*DREM_WIDTH-1 downto 0);
signal sig_rx_sop_n       : std_logic_vector(INTERFACES-1 downto 0);
signal sig_rx_eop_n       : std_logic_vector(INTERFACES-1 downto 0);
signal sig_rx_sof_n       : std_logic_vector(INTERFACES-1 downto 0);
signal sig_rx_eof_n       : std_logic_vector(INTERFACES-1 downto 0);

signal sig_en             : std_logic;

-- output signals
signal sig_mismatch       : std_logic;

-- the SOF_N equivalence checker
signal equiv_sof_n        : std_logic;
signal equiv_sof_n_in     : std_logic_vector(INTERFACES-1 downto 0);

-- the EOF_N equivalence checker
signal equiv_eof_n        : std_logic;
signal equiv_eof_n_in     : std_logic_vector(INTERFACES-1 downto 0);


-- the SOP_N equivalence checker
signal equiv_sop_n        : std_logic;
signal equiv_sop_n_in     : std_logic_vector(INTERFACES-1 downto 0);

-- the EOP_N equivalence checker
signal equiv_eop_n        : std_logic;
signal equiv_eop_n_in     : std_logic_vector(INTERFACES-1 downto 0);

-- the REM equivalence checker
signal equiv_rem          : std_logic;
signal equiv_rem_in       : std_logic_vector(INTERFACES*DREM_WIDTH-1 downto 0);

-- the DATA equivalence checker (for each byte)
signal equiv_data         : std_logic_vector(DATA_WIDTH/8-1 downto 0);
signal equiv_data_in      : std_logic_vector(INTERFACES*DATA_WIDTH-1 downto 0);

-- the DATA equivalence AND
signal equiv_data_and_no_eop     : std_logic;
signal equiv_data_and_no_eop_in  : std_logic_vector(DATA_WIDTH/8-1 downto 0);

-- the REM decoder
signal rem_decoder               : std_logic_vector(DATA_WIDTH/8-1 downto 0);
signal rem_decoder_in            : std_logic_vector(DREM_WIDTH-1 downto 0);

-- the DATA equivalence (wrt. REM)
signal equiv_data_with_rem       : std_logic_vector(DATA_WIDTH/8-1 downto 0);

-- the DATA equivalence (wrt. REM) AND
signal equiv_data_and_with_eop     : std_logic;
signal equiv_data_and_with_eop_in  : std_logic_vector(DATA_WIDTH/8-1 downto 0);

-- the multiplexer of DATA equivalence signals
signal mux_equiv_data_out          : std_logic;
signal mux_equiv_data_sel          : std_logic;

-- misc signals
signal sig_eop         : std_logic;
signal sig_rem         : std_logic_vector(DREM_WIDTH-1 downto 0);
signal big_and         : std_logic;
signal rem_is_ok       : std_logic;

begin

   -- mapping input signals
   sig_rx_data        <= RX_DATA;
   sig_rx_rem         <= RX_REM;
   sig_rx_sof_n       <= RX_SOF_N;
   sig_rx_eof_n       <= RX_EOF_N;
   sig_rx_sop_n       <= RX_SOP_N;
   sig_rx_eop_n       <= RX_EOP_N;

   sig_en             <= EN;

   --
   equiv_sof_n_in     <= sig_rx_sof_n;

   -- the equivalence checker for SOF_N signals
   equiv_sof_n_p: process (equiv_sof_n_in)
   begin
      equiv_sof_n <= '1';

      for i in 1 to INTERFACES-1 loop
         if (equiv_sof_n_in(i) /= equiv_sof_n_in(0)) then
            equiv_sof_n <= '0';
         end if;
      end loop;
   end process;

   --
   equiv_eof_n_in     <= sig_rx_eof_n;

   -- the equivalence checker for EOF_N signals
   equiv_eof_n_p: process (equiv_eof_n_in)
   begin
      equiv_eof_n <= '1';

      for i in 1 to INTERFACES-1 loop
         if (equiv_eof_n_in(i) /= equiv_eof_n_in(0)) then
            equiv_eof_n <= '0';
         end if;
      end loop;
   end process;

   --
   equiv_sop_n_in     <= sig_rx_sop_n;

   -- the equivalence checker for SOP_N signals
   equiv_sop_n_p: process (equiv_sop_n_in)
   begin
      equiv_sop_n <= '1';

      for i in 1 to INTERFACES-1 loop
         if (equiv_sop_n_in(i) /= equiv_sop_n_in(0)) then
            equiv_sop_n <= '0';
         end if;
      end loop;
   end process;

   --
   equiv_eop_n_in     <= sig_rx_eop_n;

   -- the equivalence checker for EOP_N signals
   equiv_eop_n_p: process (equiv_eop_n_in)
   begin
      equiv_eop_n <= '1';

      for i in 1 to INTERFACES-1 loop
         if (equiv_eop_n_in(i) /= equiv_eop_n_in(0)) then
            equiv_eop_n <= '0';
         end if;
      end loop;
   end process;

   --
   equiv_rem_in     <= sig_rx_rem;

   -- the equivalence checker for REM signals
   equiv_rem_p: process (equiv_rem_in)
   begin
      equiv_rem <= '1';

      for i in 1 to INTERFACES-1 loop
         if (equiv_rem_in((i+1)*DREM_WIDTH-1 downto i*DREM_WIDTH) /=
            equiv_rem_in(DREM_WIDTH-1 downto 0)) then
            equiv_rem <= '0';
         end if;
      end loop;
   end process;

   --
   equiv_data_in      <= sig_rx_data;

   -- the equivalence checker for data words
   equiv_data_p: process (equiv_data_in)
   begin
      equiv_data <= (others => '1');

      for i in 0 to DATA_WIDTH/8-1 loop
         for j in 1 to INTERFACES-1 loop
            if (equiv_data_in(j*DATA_WIDTH+i*8+7 downto j*DATA_WIDTH+i*8) /=
                equiv_data_in(             i*8+7 downto              i*8)) then
               equiv_data(i) <= '0';
            end if;
         end loop;
      end loop;

   end process;

   --
   equiv_data_and_no_eop_in   <= equiv_data;

   -- the and of equivalence signal for all data bytes
   equiv_data_and_no_eop_p: process(equiv_data_and_no_eop_in)
   begin
      equiv_data_and_no_eop <= '1';

      for i in 0 to DATA_WIDTH/8-1 loop
         if (equiv_data_and_no_eop_in(i) = '0') then
            equiv_data_and_no_eop <= '0';
         end if;
      end loop;
   end process;

   --
   rem_decoder_in <= sig_rem;

   -- the decoder of the REM signal into the mask
   rem_decoder_p: process(rem_decoder_in)
   begin
      rem_decoder <= (others => '0');

      for i in 0 to DATA_WIDTH/8-1 loop
         if (rem_decoder_in = i) then
            rem_decoder(i downto 0) <= (others => '1'); 
         end if; 
      end loop;
   end process;

   equiv_data_with_rem <= (NOT rem_decoder) OR equiv_data;

   --
   equiv_data_and_with_eop_in   <= equiv_data_with_rem;

   -- the and of equivalence signal for all data bytes 
   equiv_data_and_with_eop_p: process(equiv_data_and_with_eop_in)
   begin
      equiv_data_and_with_eop <= '1';

      for i in 0 to DATA_WIDTH/8-1 loop
         if (equiv_data_and_with_eop_in(i) = '0') then
            equiv_data_and_with_eop <= '0';
         end if;
      end loop;
   end process;

   --
   mux_equiv_data_sel  <= sig_eop;

   -- the multiplexor for data equivalence signals
   mux_equiv_data_p: process (mux_equiv_data_sel, equiv_data_and_no_eop,
      equiv_data_and_with_eop)
   begin
      mux_equiv_data_out <= equiv_data_and_no_eop;

      case (mux_equiv_data_sel) is
         when '0'    => mux_equiv_data_out <= equiv_data_and_no_eop;
         when '1'    => mux_equiv_data_out <= equiv_data_and_with_eop;
         when others => null;
      end case;
   end process;

   -- the signal denotes that there is no problem with REM
   rem_is_ok          <= equiv_rem AND sig_eop;

   -- the global EOP signal
   sig_eop            <= NOT sig_rx_eop_n(0);

   -- the global REM signal
   sig_rem            <= sig_rx_rem(DREM_WIDTH-1 downto 0);

   -- the big AND of all equalities
   big_and <=     mux_equiv_data_out
              AND rem_is_ok
              AND equiv_sof_n
              AND equiv_eof_n
              AND equiv_sop_n
              AND equiv_eop_n;

   sig_mismatch <= (NOT big_and) AND sig_en;

   -- mapping output signals
   MISMATCH           <= sig_mismatch;

end architecture;

