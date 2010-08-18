-- aurvc4x4_fl32.vhd: FrameLink via RIO (aurora based)
-- Copyright (C) 2006 CESNET
-- Author(s): Jiri Tobola <tobola@liberouter.org>
--            Lukas Solanka <solanka@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
use work.fl_pkg.all;
use work.aurvc_pkg.all;  

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity aurvc4x4_fl32 is
   generic(
      BUFFERS_PARAM        : t_aurvc_buffers_param;   -- Buffers' parameters
      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      LOOPBACK   : std_logic_vector := "00"
   ); 
   port(
   
      -- Common Input
      RESET       : in std_logic;      -- Design reset
      REFCLK      : in std_logic;      -- RocketIO clock (connected to xtal directly - no BUFGs or DCMs)
      USRCLK      : in std_logic;      -- Clock to clock transmit and receive logic
      USRCLK2     : in std_logic;      -- Clock to clock transmit and receive logic (USRCLK halfrated and shifted)
      FLCLK       : in std_logic;      -- Clock to clock FrameLink interface 
      
      -- FrameLink Interface
      TX0         : inout t_fl32;
      TX1         : inout t_fl32;
      TX2         : inout t_fl32;
      TX3         : inout t_fl32;
      RX0         : inout t_fl32;
      RX1         : inout t_fl32;
      RX2         : inout t_fl32;
      RX3         : inout t_fl32;

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR  : out std_logic;     -- Hard error detected. (Active-high, asserted until Aurora core resets).
      SOFT_ERROR  : out std_logic;     -- Soft error detected in the incoming serial stream. (Active-high, 
                                          -- asserted for a single clock).
      FRAME_ERROR : out std_logic;     -- Channel frame/protocol error detected. This port is active-high 
                                          -- and is asserted for a single clock.
      -- MGT Interface
      RXN         : in  std_logic_vector(1 downto 0);
      RXP         : in  std_logic_vector(1 downto 0);
      TXN         : out std_logic_vector(1 downto 0);
      TXP         : out std_logic_vector(1 downto 0)

   );
end entity aurvc4x4_fl32;

architecture full of aurvc4x4_fl32 is

   constant DATA_WIDTH : integer := 32*4;
   signal rx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal rx_drem      : std_logic_vector(7 downto 0);
   signal rx_src_rdy_n : std_logic_vector(3 downto 0);
   signal rx_dst_rdy_n : std_logic_vector(3 downto 0);
   signal rx_sof_n     : std_logic_vector(3 downto 0);
   signal rx_eof_n     : std_logic_vector(3 downto 0);
   signal rx_sop_n     : std_logic_vector(3 downto 0);
   signal rx_eop_n     : std_logic_vector(3 downto 0);

   signal tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal tx_drem      : std_logic_vector(7 downto 0);
   signal tx_src_rdy_n : std_logic_vector(3 downto 0);
   signal tx_dst_rdy_n : std_logic_vector(3 downto 0);
   signal tx_sof_n     : std_logic_vector(3 downto 0);
   signal tx_eof_n     : std_logic_vector(3 downto 0);
   signal tx_sop_n     : std_logic_vector(3 downto 0);
   signal tx_eop_n     : std_logic_vector(3 downto 0);

begin

   tx_src_rdy_n(0)         <= TX0.SRC_RDY_N;
   tx_sof_n(0)             <= TX0.SOF_N;
   tx_eof_n(0)             <= TX0.EOF_N;
   tx_sop_n(0)             <= TX0.SOP_N;
   tx_eop_n(0)             <= TX0.EOP_N;
   tx_drem(1 downto 0)     <= TX0.DREM;
   tx_data(31 downto 0)    <= TX0.DATA;

   tx_src_rdy_n(1)         <= TX1.SRC_RDY_N;
   tx_sof_n(1)             <= TX1.SOF_N;
   tx_eof_n(1)             <= TX1.EOF_N;
   tx_sop_n(1)             <= TX1.SOP_N;
   tx_eop_n(1)             <= TX1.EOP_N;
   tx_drem(3 downto 2)     <= TX1.DREM;
   tx_data(63 downto 32)   <= TX1.DATA;

   tx_src_rdy_n(2)         <= TX2.SRC_RDY_N;
   tx_sof_n(2)             <= TX2.SOF_N;
   tx_eof_n(2)             <= TX2.EOF_N;
   tx_sop_n(2)             <= TX2.SOP_N;
   tx_eop_n(2)             <= TX2.EOP_N;
   tx_drem(5 downto 4)     <= TX2.DREM;
   tx_data(95 downto 64)   <= TX2.DATA;

   tx_src_rdy_n(3)         <= TX3.SRC_RDY_N;
   tx_sof_n(3)             <= TX3.SOF_N;
   tx_eof_n(3)             <= TX3.EOF_N;
   tx_sop_n(3)             <= TX3.SOP_N;
   tx_eop_n(3)             <= TX3.EOP_N;
   tx_drem(7 downto 6)     <= TX3.DREM;
   tx_data(127 downto 96)  <= TX3.DATA;

   TX0.DST_RDY_N     <= tx_dst_rdy_n(0);
   TX1.DST_RDY_N     <= tx_dst_rdy_n(1);
   TX2.DST_RDY_N     <= tx_dst_rdy_n(2);
   TX3.DST_RDY_N     <= tx_dst_rdy_n(3);

   -- interface mapping
   RX3.DREM       <= rx_drem(7 downto 6);
   RX2.DREM       <= rx_drem(5 downto 4);
   RX1.DREM       <= rx_drem(3 downto 2);
   RX0.DREM       <= rx_drem(1 downto 0);

   RX3.SRC_RDY_N  <= rx_src_rdy_n(3);
   RX2.SRC_RDY_N  <= rx_src_rdy_n(2);
   RX1.SRC_RDY_N  <= rx_src_rdy_n(1);
   RX0.SRC_RDY_N  <= rx_src_rdy_n(0);

   RX3.SOF_N      <= rx_sof_n(3);
   RX2.SOF_N      <= rx_sof_n(2);
   RX1.SOF_N      <= rx_sof_n(1);
   RX0.SOF_N      <= rx_sof_n(0);

   RX3.EOF_N      <= rx_eof_n(3);
   RX2.EOF_N      <= rx_eof_n(2);
   RX1.EOF_N      <= rx_eof_n(1);
   RX0.EOF_N      <= rx_eof_n(0);

   RX3.SOP_N      <= rx_sop_n(3);
   RX2.SOP_N      <= rx_sop_n(2);
   RX1.SOP_N      <= rx_sop_n(1);
   RX0.SOP_N      <= rx_sop_n(0);

   RX3.EOP_N      <= rx_eop_n(3);
   RX2.EOP_N      <= rx_eop_n(2);
   RX1.EOP_N      <= rx_eop_n(1);
   RX0.EOP_N      <= rx_eop_n(0);

   rx_dst_rdy_n   <= RX3.DST_RDY_N & RX2.DST_RDY_N & RX1.DST_RDY_N 
                     & RX0.DST_RDY_N;

   -- process to remove X signals in simulations
   process(rx_data)
   begin
      RX0.DATA <= rx_data(31  downto 0);
      RX1.DATA <= rx_data(63  downto 32);
      RX2.DATA <= rx_data(95  downto 64);
      RX3.DATA <= rx_data(127 downto 96);
      -- for simulations only:
      -- pragma translate_off 
      for aux in 0 to 31 loop
         if (rx_data(aux) = 'X') then
            RX0.DATA(aux) <= '0';
         else
            RX0.DATA(aux) <= rx_data(aux);
         end if;
      end loop;
      for aux in 32 to 63 loop
         if (rx_data(aux) = 'X') then
            RX1.DATA(aux-32) <= '0';
         else
            RX1.DATA(aux-32) <= rx_data(aux);
         end if;
      end loop;
      for aux in 64 to 95 loop
         if (rx_data(aux) = 'X') then
            RX2.DATA(aux-64) <= '0';
         else
            RX2.DATA(aux-64) <= rx_data(aux);
         end if;
      end loop;
      for aux in 96 to 127 loop
         if (rx_data(aux) = 'X') then
            RX3.DATA(aux-96) <= '0';
         else
            RX3.DATA(aux-96) <= rx_data(aux);
         end if;
      end loop;
      -- pragma translate_on 
   end process; 

   AURVC_I: entity work.aurvc
   generic map(
      LANES          => 2,
      DATA_PATHS     => 4,
      TX_CHANNELS    => 4,
      RX_CHANNELS    => 4,
      BUFFERS_PARAM  => BUFFERS_PARAM,
      LOOPBACK       => LOOPBACK
   )
   port map (
      -- Common Input
      RESET          => reset,
      REFCLK         => refclk,
      USRCLK         => usrclk,
      USRCLK2        => usrclk2,
      FLCLK          => flclk,
      
      -- FrameLink TX Interface
      TX_D             => tx_data,
      TX_REM           => tx_drem,
      TX_SRC_RDY_N     => tx_src_rdy_n,
      TX_SOF_N         => tx_sof_n,
      TX_SOP_N         => tx_sop_n,
      TX_EOF_N         => tx_eof_n,
      TX_EOP_N         => tx_eop_n,
      TX_DST_RDY_N     => tx_dst_rdy_n,

      -- FrameLink RX Interface
      RX_D             => rx_data,
      RX_REM           => rx_drem,
      RX_SRC_RDY_N     => rx_src_rdy_n,
      RX_SOF_N         => rx_sof_n,
      RX_SOP_N         => rx_sop_n,
      RX_EOF_N         => rx_eof_n,
      RX_EOP_N         => rx_eop_n,
      RX_DST_RDY_N     => rx_dst_rdy_n,

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     => HARD_ERROR,
      SOFT_ERROR     => SOFT_ERROR,
      FRAME_ERROR    => FRAME_ERROR,

      -- MGT Interface
      RXN            => RXN,
      RXP            => RXP,
      TXN            => TXN,
      TXP            => TXP
   );

end architecture full; 

