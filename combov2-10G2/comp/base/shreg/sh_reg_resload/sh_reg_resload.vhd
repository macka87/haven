--
-- sh_reg_resload.vhd: Shift Register With Reset
-- Copyright (C) 2006 CESNET
-- Author(s): Michal Spacek <xspace14@stud.fit.vutbr.cz>
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
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use WORK.cnt_types.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity sh_reg_resload is
   generic(
      NUM_BITS    : integer := 16;
      INIT        : std_logic_vector(15 downto 0) := X"0000";
      INIT_EXT00  : std_logic_vector(63 downto 0) := X"0000000000000000"      
   );
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;
      DIN      : in  std_logic;
      CE       : in  std_logic;
      DOUT     : out std_logic
   );
end entity sh_reg_resload;
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of sh_reg_resload is

-- ------------------ Signals declaration -------------------------------------
   type fsm_state is (working, load, wait_reset);

   signal r_din    : std_logic;
   signal r_ce     : std_logic;

   signal WAITFORRESET : std_logic;
   signal SE       : std_logic;
   signal CLR_CNTR : std_logic;
   signal CNT_OUT  : std_logic_vector(NUM_BITS-1 downto 0);
   signal AADREQCNTR : std_logic;

   signal pstate   : fsm_state;
   signal nstate   : fsm_state;

   signal DOUT2    : std_logic;

begin

    r_ce <= ((SE or CE) and (not WAITFORRESET));

    r_din <= DIN when SE='0' else
                   DOUT2 when SE='1';

    AADREQCNTR <= '1' when (NUM_BITS-1 = CNT_OUT) else '0';




--sh_reg
SH_REG_U : entity work.sh_reg
      generic map(
         NUM_BITS  => NUM_BITS,
         INIT => INIT,
         INIT_EXT00 => INIT_EXT00
      )
      port map(
         CLK      => CLK,
         DIN      => r_din,
         CE       => r_ce,
         DOUT     => DOUT
      );

--sh_reg - keeps the reseting value
SH_REG_U2 : entity work.sh_reg
      generic map(
         NUM_BITS  => NUM_BITS,
         INIT => INIT,
         INIT_EXT00 => INIT_EXT00
      )
      port map(
         CLK      => CLK,
         DIN      => DOUT2,
         CE       => SE,
         DOUT     => DOUT2
      );



--FSM present state
fsm_pstate: process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         pstate <= nstate;
      end if;
   end process;



--FSM next state logic
nsl: process(pstate, AADREQCNTR, RESET)
   begin

      SE <= '0';
      CLR_CNTR <= '0';
      WAITFORRESET <= '0';

      case pstate is
         when working =>
            CLR_CNTR <= '1';
            if (RESET='1') then nstate <= load;
            end if;

         when load =>
            SE <= '1';
            if (AADREQCNTR='1') then nstate <= wait_reset;
            end if;

         when wait_reset =>
            WAITFORRESET <='1';
            if (RESET='0') then nstate <= working;
            end if;
         when others =>
      end case;
   end process;

--counter
count: entity work.cnt
      generic map(
         WIDTH => NUM_BITS,
         DIR   => up,
         CLEAR => true
      )
      port map(
         RESET => '0',
         CLK   => CLK,
         DO    => CNT_OUT,
         CLR   => CLR_CNTR,
         CE    => SE
);

end architecture behavioral;

