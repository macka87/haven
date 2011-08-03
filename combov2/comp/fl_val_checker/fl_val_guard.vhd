--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Validity Guard
-- Description: 
-- Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
-- Date:         15.4.2011 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing the log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_VAL_GUARD is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      SOF_N          : in std_logic;
      EOF_N          : in std_logic;
      SOP_N          : in std_logic;
      EOP_N          : in std_logic;
      DST_RDY_N      : in std_logic;
      SRC_RDY_N      : in std_logic;      

      INVALID        : out std_logic;
      ERROR_BITMAP   : out std_logic_vector(15 downto 0)
 );
end entity;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture full of FL_VAL_GUARD is

-- ----------------------------------------------------------------------------
--                                Constants
-- ----------------------------------------------------------------------------

constant SOF_WITHOUT_SOP           : integer := 0;
constant EOF_WITHOUT_EOP           : integer := 1;
constant DATA_BETWEEN_EOP_AND_SOP  : integer := 2;
constant DATA_BETWEEN_EOF_AND_SOF  : integer := 3;
constant NO_EOP_BEFORE_SOP         : integer := 4;
constant NO_EOF_BEFORE_SOF         : integer := 4;


-- ----------------------------------------------------------------------------
--                                 Signals
-- ----------------------------------------------------------------------------

signal reg_eof_n  : std_logic;
signal reg_eop_n  : std_logic;

signal reg_was_sof: std_logic;
signal reg_was_sop: std_logic;
signal reg_fend   : std_logic;

signal invld      : std_logic;
signal reg_invld  : std_logic;

signal sig_error_bitmap : std_logic_vector(15 downto 0);
signal reg_error_bitmap : std_logic_vector(15 downto 0);

begin

-- Register EOF_N to get desired SOF_N
reg_eof_n_p : process(CLK, RESET)
begin
   if rising_edge(CLK) then
      if RESET = '1' then
         reg_eof_n <= '0';
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' then
         reg_eof_n <= EOF_N;
      end if;
   end if;
end process;

-- Register EOP_N to get desired SOP_N
reg_eop_n_p : process(CLK, RESET)
begin
   if rising_edge(CLK) then
      if RESET = '1' then
         reg_eop_n <= '0';
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' then
         reg_eop_n <= EOP_N;
      end if;
   end if;
end process;

-- Set to 1 when SOF_N is active, set to 0 when EOF_N is active.
reg_was_sof_p : process(CLK)
begin
   if rising_edge(CLK) then
      if RESET = '1' then
         reg_was_sof <= '0';
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' then
         if EOF_N = '0' then
            reg_was_sof <= '0';
         elsif SOF_N = '0' then
            reg_was_sof <= '1';
         end if;
      end if;
   end if;
end process;

-- Set to 1 when SOP_N is active, set to 0 when EOP_N is active.
reg_was_sop_p : process(CLK)
begin
   if rising_edge(CLK) then
      if RESET = '1' then
         reg_was_sop <= '0';
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' then
         if EOP_N = '0' then
            reg_was_sop <= '0';
         elsif SOP_N = '0' then
            reg_was_sop <= '1';
         end if;
      end if;
   end if;
end process;

-- Used to determine end of frame more exactly. (In situation when 
-- protocol is violated, it can be difficult)
reg_fend_p : process(CLK)
begin
   if (rising_edge(CLK)) then
      if RESET = '1' then
         reg_fend <= '0';
      elsif SRC_RDY_N = '0' and DST_RDY_N = '0' and (EOF_N = '0' or
         (SOF_N = '0' and reg_was_sof = '1')) then
         reg_fend <= '1';
      else
         reg_fend <= '0';
      end if;
   end if;
end process;


detect_invld : process(SOF_N, EOF_N, SOP_N, EOP_N, DST_RDY_N, SRC_RDY_N,
                       reg_eof_n, reg_eop_n, reg_was_sof, reg_was_sop)
begin
   sig_error_bitmap <= (others => '0');
   invld <= '0';

   if SRC_RDY_N = '0' and DST_RDY_N = '0' then  -- Transfer valid

      if SOF_N = '0' and SOP_N = '1' then
         invld <= '1';  -- With every SOF, SOP must also come
         sig_error_bitmap(SOF_WITHOUT_SOP) <= '1';
      end if;
      
      if EOF_N = '0' and EOP_N = '1' then
         invld <= '1';  -- With every EOF, EOP must also come
         sig_error_bitmap(EOF_WITHOUT_EOP) <= '1';
      end if;

      if reg_eop_n /= SOP_N then
         invld <= '1';  -- SOP must come immediately after EOP
         sig_error_bitmap(DATA_BETWEEN_EOP_AND_SOP) <= '1';
      end if;

      if reg_eof_n /= SOF_N then
         invld <= '1';  -- SOF must come immediately after EOF
         sig_error_bitmap(DATA_BETWEEN_EOF_AND_SOF) <= '1';
      end if;

      if reg_was_sop /= SOP_N then
         invld <= '1';  -- before SOP, EOP needs to come
         sig_error_bitmap(NO_EOP_BEFORE_SOP) <= '1';
      end if;

      if reg_was_sof /= SOF_N then
         invld <= '1';  -- before SOF, EOF needs to come
         sig_error_bitmap(NO_EOF_BEFORE_SOF) <= '1';
      end if;

   end if;
end process;

-- register invld
reg_invld_p : process(CLK, RESET)
begin
   if (rising_edge(CLK)) then
      if RESET = '1' then
         reg_invld <= '0';
         reg_error_bitmap <= (others => '0');
      elsif reg_fend = '1' then
         reg_invld <= '0';
         reg_error_bitmap <= (others => '0');
      else
         reg_invld <= reg_invld OR invld;
         reg_error_bitmap <= reg_error_bitmap OR sig_error_bitmap;
      end if;
   end if;
end process;

INVALID <= reg_invld when reg_fend = '1' else
           '0';

ERROR_BITMAP <= reg_error_bitmap;

end architecture;
