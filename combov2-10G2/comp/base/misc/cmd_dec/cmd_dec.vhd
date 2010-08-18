--
-- cmd_dec.vhd: Command Decoder
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas <martinek@liberouter.org>
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
-- 1. Redistributions of source code must retain the above copyright
--    notice, this list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright
--    notice, this list of conditions and the following disclaimer in
--    the documentation and/or other materials provided with the
--    distribution.
-- 3. Neither the name of the Company nor the names of its contributors
--    may be used to endorse or promote products derived from this
--    software without specific prior written permission.
--
-- This software is provided ``as is'', and any express or implied
-- warranties, including, but not limited to, the implied warranties of
-- merchantability and fitness for a particular purpose are disclaimed.
-- In no event shall the company or contributors be liable for any
-- direct, indirect, incidental, special, exemplary, or consequential
-- damages (including, but not limited to, procurement of substitute
-- goods or services; loss of use, data, or profits; or business
-- interruption) however caused and on any theory of liability, whether
-- in contract, strict liability, or tort (including negligence or
-- otherwise) arising in any way out of the use of this software, even
-- if advised of the possibility of such damage.
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
use work.commands.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cmd_dec is
   generic(
      NUM_PATHS   : integer := 4
   );
   port(
      -- Input interface
      DI          : in    std_logic_vector((NUM_PATHS*8)-1 downto 0); -- Input Data
      DI_CMD      : in    std_logic_vector((NUM_PATHS-1) downto 0);
      EN          : in    std_logic;

      -- Output interface
      DO          : out   std_logic_vector((NUM_PATHS*8)-1 downto 0); -- Output Data
      CMD_SOP     : out   std_logic;
      CMD_SOC     : out   std_logic;
      CMD_PCKREC  : out   std_logic;
      CMD_IDLE    : out   std_logic;
      CMD_TERM    : out   std_logic;
      CMD_DATA    : out   std_logic;
      LEN         : out   std_logic_vector(log2(NUM_PATHS+1)-1 downto 0)
   );
end entity cmd_dec;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of cmd_dec is

   signal di_i          : std_logic_vector((NUM_PATHS*8)-1 downto 0);
   signal cmd_sop_i     : std_logic;
   signal cmd_soc_i     : std_logic;
   signal cmd_idle_i    : std_logic;
   signal cmd_pckrec_i  : std_logic;
   signal cmd_term_i    : std_logic;
   signal cmd_term_vec_i : std_logic_vector(NUM_PATHS-1 downto 0);
   signal len_i          : std_logic_vector(log2(NUM_PATHS+1)-1 downto 0);

begin

di_i <= DI;

-- Data Output Multiplexor
MX_U : for i in 0 to (NUM_PATHS-1) generate
   DO(((i+1)*8)-1 downto i*8) <= di_i(((i+1)*8)-1 downto i*8)
         when (DI_CMD(i)='0') else "00000000";
end generate;

-- Command Comparators
-- cmd_sop_i <= '1' when (di_i(7 downto 0) = C_CMD_SOP) else '0';
-- cmd_soc_i <= '1' when (di_i(7 downto 0) = C_CMD_SOC) else '0';
-- cmd_idle_i <= '1' when (di_i(7 downto 0) = C_CMD_IDLE) else '0';
-- cmd_pckrec_i <= '1' when (di_i(7 downto 0) = C_CMD_PCKREC) else '0';


-- CMD_SOP Decoder
CMD_SOP_CMP_U : entity work.cmd_dec_cmp
generic map(
   CMP_VAL => C_CMD_SOP
)
port map(
   DIN      => di_i(7 downto 0),
   RESULT   => cmd_sop_i
);

-- CMD_SOC Decoder
CMD_SOC_CMP_U : entity work.cmd_dec_cmp
generic map(
   CMP_VAL => C_CMD_SOC
)
port map(
   DIN      => di_i(7 downto 0),
   RESULT   => cmd_soc_i
);

-- CMD_IDLE Decoder
CMD_IDLE_CMP_U : entity work.cmd_dec_cmp
generic map(
   CMP_VAL => C_CMD_IDLE
)
port map(
   DIN      => di_i(7 downto 0),
   RESULT   => cmd_idle_i
);

-- CMD_PCKREC Decoder
CMD_PCKREC_CMP_U : entity work.cmd_dec_cmp
generic map(
   CMP_VAL => C_CMD_PCKREC
)
port map(
   DIN      => di_i(7 downto 0),
   RESULT   => cmd_pckrec_i
);

-- Terminate command evaluation
TERM_U : for i in 0 to (NUM_PATHS-1) generate
   -- CMD_TERM Decoder
   CMD_PCKREC_CMP_U : entity work.cmd_dec_cmp
   generic map(
      CMP_VAL => C_CMD_TERM
   )
   port map(
      DIN      => di_i(((i+1)*8)-1 downto i*8),
      RESULT   => cmd_term_vec_i(i)
   );
--    cmd_term_vec_i(i) <= '1' when (di_i(((i+1)*8)-1 downto i*8) = C_CMD_TERM) else '0';
end generate;

process(cmd_term_vec_i, DI_CMD, cmd_term_i)
   variable cmd_term_vec_aux  : std_logic_vector(NUM_PATHS downto 0);
begin
   cmd_term_vec_aux := (others => '0');

   -- cmd_term_i evaluation
   for i in 0 to (NUM_PATHS-1) loop
      cmd_term_vec_aux(i+1) := (cmd_term_vec_i(i) and DI_CMD(i)) or
                               cmd_term_vec_aux(i);
   end loop;

   cmd_term_i <= cmd_term_vec_aux(NUM_PATHS);

   -- len_i vector generating -------------------------------------------------
   len_i <= conv_std_logic_vector(0, len_i'length);
   for i in 0 to NUM_PATHS-1 loop
      if (DI_CMD(i)='0') then
	 len_i <= conv_std_logic_vector(i+1, len_i'length);
      else
	 exit;
      end if;
   end loop;

end process;

-- Output Commands Mapping
CMD_SOP     <= cmd_sop_i   when ((DI_CMD(0)='1') and (EN='1')) else '0';
CMD_SOC     <= cmd_soc_i   when ((DI_CMD(0)='1') and (EN='1')) else '0';
CMD_IDLE    <= cmd_idle_i  when ((DI_CMD(0)='1') and (EN='1')) else '0';
CMD_PCKREC  <= cmd_pckrec_i when ((DI_CMD(0)='1') and (EN='1')) else '0';
CMD_TERM    <= cmd_term_i  when                      (EN='1')  else '0';
CMD_DATA    <= '1'         when ((DI_CMD(0)='0') and (EN='1')) else '0';
LEN         <= len_i;

end architecture behavioral;

