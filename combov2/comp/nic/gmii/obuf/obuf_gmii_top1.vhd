--
-- obuf_gmii_top1.vhd:  Output Buffer - obuf + LB entity
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
library ieee;
use ieee.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_gmii_top1 is

   --signal reset    : std_logic;
   
   signal adc_rd   : std_logic;
   signal adc_wr   : std_logic;
   signal adc_addr : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal adc_di   : std_logic_vector(31 downto 0);
   signal adc_do   : std_logic_vector(31 downto 0);
   signal adc_drdy : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

-- OBUF instantination --------------------------------------------------------
OBUF_U : entity work.obuf_gmii
generic map (
   ADDR_BASE  => ADDR_BASE,
   ADDR_WIDTH => ADDR_WIDTH,
   DATA_PATHS => DATA_PATHS,
   DFIFO_SIZE => DFIFO_SIZE,
   SFIFO_SIZE => SFIFO_SIZE,
   CTRL_CMD   => CTRL_CMD
)
port map (
   RESET => reset,

   -- FrameLink input interface
   DATA       => DATA,
   DREM       => DREM,
   SRC_RDY_N  => SRC_RDY_N,
   SOF_N      => SOF_N,
   SOP_N      => SOP_N,
   EOF_N      => EOF_N,
   EOP_N      => EOP_N,
   DST_RDY_N  => DST_RDY_N,

   -- gmii interface
   REFCLK   => REFCLK,
   TXCLK    => TXCLK,
   TXD      => TXD,
   TXEN     => TXDV,
   TXER     => TXER,

   ADC_RD   => '0',--adc_rd,
   ADC_WR   => '0',--adc_wr,
   ADC_ADDR => (others=>'0'),--adc_addr,
   ADC_DI   => (others=>'0'),--adc_di,
   ADC_DO   => open,--adc_do,
   ADC_DRDY => open,--adc_drdy
);

-- LBCONN_MEM instantination --------------------------------------------------
LBCONN_MEM_U : entity work.lbconn_mem
generic map(
   ADDR_WIDTH     => ADDR_WIDTH, -- address bus width
   BASE           => ADDR_BASE,  -- base address
)
port map(
   DATA_OUT => open,
   DATA_IN  => (others=>'0'),--reg_data_to_lb,
   ADDR     => open,--adc_addr,
   EN       => open,
   RW       => open,
   SEL      => open,
   DRDY     => '1',
   ARDY     => '1',

   RESET    => RESET,
   LBCLK    => LBCLK,
   LBFRAME  => LBFRAME,
   LBAS     => LBAS,
   LBRW     => LBRW,
   LBLAST   => LBLAST,
   LBAD     => LBAD,
   LBHOLDA  => LBHOLDA,
   LBRDY    => LBRDY
);

end architecture full;
