--
-- obuf_gmii_cmd.vhd: Output buffer for GMII - FrameLink part
-- Copyright (C) 2005 CESNET
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_gmii_fl is
   generic(
      DATA_PATHS : integer := 4;
      CTRL_CMD   : boolean := true
   );
   port(
      RESET       : in  std_logic;
      CLK         : in  std_logic;

      -- FrameLink input interface
      DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      SRC_RDY_N  : in std_logic;
      SOF_N      : in std_logic;
      SOP_N      : in std_logic;
      EOF_N      : in std_logic;
      EOP_N      : in std_logic;
      DST_RDY_N  : out std_logic;

      -- obuf_gmii_buf interface
      DFIFO_DO     : out std_logic_vector(DATA_PATHS*9-1 downto 0);
      DFIFO_WR     : out std_logic;
      DFIFO_FULL   : in  std_logic;

      SFIFO_DO     : out std_logic_vector(1 downto 0);
      SFIFO_WR     : out std_logic;
      SFIFO_FULL   : in  std_logic
   );
end entity obuf_gmii_fl;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_gmii_fl is

--signal reverse_data  : std_logic_vector(DATA_PATHS*8-1 downto 0);
signal dv_i       : std_logic_vector(DATA_PATHS-1 downto 0);
signal dv         : std_logic_vector(DATA_PATHS-1 downto 0);
signal reg_ctrl   : std_logic;
signal full_i     : std_logic;

begin

   
--   gen_reverse_data: for i in 0 to DATA_PATHS-1 generate
--      reverse_data(((i+1)*8)-1 downto (i*8)) <= DATA(((DATA_PATHS-i)*8)-1 downto ((DATA_PATHS-i-1)*8));
--   end generate;
   
   gen_ctrl_cmd_true: if (CTRL_CMD=true) generate
      SFIFO_DO <= DATA(1 downto 0);
      SFIFO_WR <= (not SRC_RDY_N) and (not full_i) and reg_ctrl;
      DFIFO_WR <= (not SRC_RDY_N) and (not full_i) and (not reg_ctrl);

      reg_ctrl_p: process(CLK, RESET)
      begin
         if (RESET='1') then
            reg_ctrl <= '0';
         elsif (CLK'event and CLK='1') then
            if (EOP_N='0') then
               reg_ctrl <= not reg_ctrl;
            end if;
         end if;
      end process;
   end generate;

   gen_ctrl_cmd_false: if (CTRL_CMD=false) generate
      SFIFO_DO <= "01";
      SFIFO_WR <= (not SRC_RDY_N) and (not full_i) and (not EOP_N);
      DFIFO_WR <= (not SRC_RDY_N) and (not full_i);
   end generate;

   full_i <= DFIFO_FULL or SFIFO_FULL;

   dv_gen : for i in 0 to DATA_PATHS-1 generate
       dv_i(i) <= '0' when ((conv_std_logic_vector(i,log2(DATA_PATHS))) <= DREM) else
                  '1';
       dv(i) <= '1' when EOP_N = '1' else
                dv_i(i);
   end generate;

   -- output signal assignment
   DFIFO_DO <= dv & DATA;
   DST_RDY_N <= full_i;

end architecture full;

