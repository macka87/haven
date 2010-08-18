-- async.vhd: Unit gets write or read requests at input frequency and creates
--            write enables for an register as output on another frequency.
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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
-- TODO: resets
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- Async is unit for assynchrounous requests. When RQST is set to high, then 
-- it must keep state until RDY signal also gets high else request may be lost.
-- After RDY is set, then RQST may be unset. Next RQST can be generated
-- after RQST was set to low.
entity async is
   port (
      -- input clk
      IN_CLK     : in std_logic;
      -- data write request
      RQST       : in std_logic; -- request
      -- address ready signal - when we are ready for another transaction
      RDY        : out std_logic; -- data are ready

      -- output clk and write enable
      OUT_CLK    : in std_logic;
      OUT_RQST   : out std_logic  -- output write enable
   );
end async;

architecture behavioral of async is

   signal out_reg_we          : std_logic;
   signal out_reg_we_delay    : std_logic;
   signal rqst_pipe           : std_logic;
   signal rqst_pipe_reg       : std_logic;
   signal rdy_pipe            : std_logic;
   signal rdy_pipe0_reg       : std_logic;
   signal rdy_pipe1_reg       : std_logic;
   signal served              : std_logic;

begin

   -- -------------------------------------------------------------------------
   -- R-S latch for RQST signal to enable write into OUT_DATA
   process(RQST, out_reg_we, served)
   begin
      if (out_reg_we = '1' or served = '1') then
         rqst_pipe <= '0';
      elsif (RQST = '1') then
         rqst_pipe <= '1';
      end if;
   end process;

   -- -------------------------------------------------------------------------
   -- register pipe for RQST signal to enable write into OUT_DATA
   rqst_pipe_register : process(OUT_CLK)
   begin
      if (OUT_CLK'event and OUT_CLK = '1') then
         if (out_reg_we = '1') then
            rqst_pipe_reg <= '0';
            out_reg_we <= '0';
         else
            rqst_pipe_reg <= rqst_pipe;
            out_reg_we <= rqst_pipe_reg;
         end if;
      end if;
   end process;

   out_reg_we_delay_p : process(OUT_CLK)
   begin
      if (OUT_CLK'event and OUT_CLK = '1') then
         out_reg_we_delay <= out_reg_we;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   -- R-S latch that indicates if current request was already served or not
   process (rdy_pipe1_reg, out_reg_we)
   begin
      if (rdy_pipe1_reg = '1') then
         served <= '0';
      elsif (out_reg_we = '1') then
         served <= '1';
      end if;
   end process;

   -- -------------------------------------------------------------------------
   -- R-S latch for ARDY signal to acknowledge that data were wrote
   process(out_reg_we_delay, rdy_pipe1_reg, served)
   begin
      if (rdy_pipe1_reg = '1') then
         rdy_pipe <= '0';
      elsif (out_reg_we_delay = '1' and served = '1') then
         rdy_pipe <= '1';
      end if;
   end process;

   -- -------------------------------------------------------------------------
   -- Register pipe for signal for ardy output
   rdy_pipe_register : process(IN_CLK)
   begin
      if (IN_CLK'event and IN_CLK = '1') then
         if (rdy_pipe1_reg = '1') then
            rdy_pipe0_reg <= '0';
            rdy_pipe1_reg <= '0';
         else
            rdy_pipe0_reg <= rdy_pipe;
            rdy_pipe1_reg <= rdy_pipe0_reg;
         end if;
      end if;
   end process;

RDY <= rdy_pipe1_reg;
OUT_RQST <= out_reg_we;

end architecture behavioral;
