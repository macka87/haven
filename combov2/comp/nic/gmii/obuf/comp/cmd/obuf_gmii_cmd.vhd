--
-- obuf_gmii_cmd.vhd: Output buffer for GMII - command protocol part
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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

-- library containing log2 function
--use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_gmii_cmd is
   generic(
      DATA_PATHS : integer := 4;
      CTRL_CMD   : boolean := true
   );
   port(
      RESET       : in  std_logic;
      CLK         : in  std_logic;

      -- command input interface
      WR           : in  std_logic;
      DI           : in  std_logic_vector(DATA_PATHS*8-1 downto 0);
      DI_CMD       : in  std_logic_vector(DATA_PATHS-1   downto 0);
      FULL         : out std_logic;

      -- obuf_gmii_buf interface
      DFIFO_DO     : out std_logic_vector(DATA_PATHS*9-1 downto 0);
      DFIFO_WR     : out std_logic;
      DFIFO_FULL   : in  std_logic;

      SFIFO_DO     : out std_logic_vector(0 downto 0);
      SFIFO_WR     : out std_logic;
      SFIFO_FULL   : in  std_logic
   );
end entity obuf_gmii_cmd;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_gmii_cmd is

signal data       : std_logic_vector(DATA_PATHS*8-1 downto 0);
signal cmd_data   : std_logic;
signal cmd_term   : std_logic;
signal dv         : std_logic_vector(DATA_PATHS-1 downto 0);
signal en         : std_logic;
signal reg_ctrl   : std_logic;
signal full_i     : std_logic;

begin

   -- ------ command decoder instantination -----------------------------------
   CMD_DEC_U : entity work.cmd_dec
   generic map(
      NUM_PATHS => DATA_PATHS
   )
   port map(
      -- Input interface
      DI       => DI,
      DI_CMD   => DI_CMD,
      EN       => WR,

      -- Output interface
      DO       => data,
      CMD_SOP  => open,
      CMD_SOC  => open,
      CMD_IDLE => open,
      CMD_TERM => cmd_term,
      CMD_DATA => cmd_data,
      LEN      => open
   );

   
   gen_ctrl_cmd_true: if (CTRL_CMD=true) generate
      SFIFO_DO <= data(0 downto 0);
      SFIFO_WR <= cmd_data and reg_ctrl;
      DFIFO_WR <= (cmd_data or cmd_term) and (not reg_ctrl);

      reg_ctrl_p: process(CLK, RESET)
      begin
         if (RESET='1') then
            reg_ctrl <= '0';
         elsif (CLK'event and CLK='1') then
            if (cmd_term='1') then
               reg_ctrl <= not reg_ctrl;
            end if;
         end if;
      end process;
   end generate;

   gen_ctrl_cmd_false: if (CTRL_CMD=false) generate
      SFIFO_DO <= "1";
      SFIFO_WR <= cmd_term;
      DFIFO_WR <= cmd_data or cmd_term;
   end generate;

   en <= not full_i and WR;

   full_i <= DFIFO_FULL or SFIFO_FULL;

   dv_gen : for i in 0 to DATA_PATHS-1 generate
   	 dv(i) <= not DI_CMD(i);
   end generate;
   
   -- output signal assignment
   DFIFO_DO <= dv & data;
   FULL     <= full_i;

end architecture full;

