-- obuf_emac_top4.vhd:  Output Buffer - 4 obufs + LB entity
-- Copyright (C) 2008 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--            Libor Polcak <polcak_l@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.lb_pkg.all;
use work.emac_pkg.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_emac_top4_mi32 is
   generic(
      DATA_PATHS     : integer;
      DFIFO_SIZE     : integer;
      SFIFO_SIZE     : integer;
      CTRL_CMD       : boolean;
      EMAC0_USECLKEN : boolean;
      EMAC1_USECLKEN : boolean;
      EMAC2_USECLKEN : boolean;
      EMAC3_USECLKEN : boolean
   );
   port(

      -- ---------------- Control signal -----------------
      RESET         : in  std_logic;
      WRCLK         : in  std_logic;

      -- -------------- Buffer interface -----------------
      -- Interface 0
      OBUF0_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      OBUF0_DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      OBUF0_SRC_RDY_N  : in std_logic;
      OBUF0_SOF_N      : in std_logic;
      OBUF0_SOP_N      : in std_logic;
      OBUF0_EOF_N      : in std_logic;
      OBUF0_EOP_N      : in std_logic;
      OBUF0_DST_RDY_N  : out std_logic;
      -- Interface 1 
      OBUF1_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      OBUF1_DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      OBUF1_SRC_RDY_N  : in std_logic;
      OBUF1_SOF_N      : in std_logic;
      OBUF1_SOP_N      : in std_logic;
      OBUF1_EOF_N      : in std_logic;
      OBUF1_EOP_N      : in std_logic;
      OBUF1_DST_RDY_N  : out std_logic;
      -- Interface 0
      OBUF2_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      OBUF2_DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      OBUF2_SRC_RDY_N  : in std_logic;
      OBUF2_SOF_N      : in std_logic;
      OBUF2_SOP_N      : in std_logic;
      OBUF2_EOF_N      : in std_logic;
      OBUF2_EOP_N      : in std_logic;
      OBUF2_DST_RDY_N  : out std_logic;
      -- Interface 0
      OBUF3_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      OBUF3_DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      OBUF3_SRC_RDY_N  : in std_logic;
      OBUF3_SOF_N      : in std_logic;
      OBUF3_SOP_N      : in std_logic;
      OBUF3_EOF_N      : in std_logic;
      OBUF3_EOP_N      : in std_logic;
      OBUF3_DST_RDY_N  : out std_logic;

      -- -------------- TX interface -----------------
      -- Interface 0
      OBUF0_EMAC_CLK          : in std_logic;
      OBUF0_EMAC_CE           : in std_logic;
      OBUF0_EMAC_D            : out std_logic_vector(7 downto 0);
      OBUF0_EMAC_DVLD         : out std_logic;
      OBUF0_EMAC_ACK          : in  std_logic;
      OBUF0_EMAC_FIRSTBYTE    : out std_logic;
      OBUF0_EMAC_UNDERRUN     : out std_logic;
      OBUF0_EMAC_COLLISION    : in  std_logic;
      OBUF0_EMAC_RETRANSMIT   : in  std_logic;
      OBUF0_EMAC_IFGDELAY     : out std_logic_vector(7 downto 0);
      OBUF0_EMAC_STATS        : in  std_logic;
      OBUF0_EMAC_STATSVLD     : in  std_logic;
      OBUF0_EMAC_STATSBYTEVLD : in  std_logic;
      OBUF0_EMAC_SPEEDIS10100 : in  std_logic;

      -- Interface 1
      OBUF1_EMAC_CLK          : in std_logic;
      OBUF1_EMAC_CE           : in std_logic;
      OBUF1_EMAC_D            : out std_logic_vector(7 downto 0);
      OBUF1_EMAC_DVLD         : out std_logic;
      OBUF1_EMAC_ACK          : in  std_logic;
      OBUF1_EMAC_FIRSTBYTE    : out std_logic;
      OBUF1_EMAC_UNDERRUN     : out std_logic;
      OBUF1_EMAC_COLLISION    : in  std_logic;
      OBUF1_EMAC_RETRANSMIT   : in  std_logic;
      OBUF1_EMAC_IFGDELAY     : out std_logic_vector(7 downto 0);
      OBUF1_EMAC_STATS        : in  std_logic;
      OBUF1_EMAC_STATSVLD     : in  std_logic;
      OBUF1_EMAC_STATSBYTEVLD : in  std_logic;
      OBUF1_EMAC_SPEEDIS10100 : in  std_logic;

      -- Interface 2
      OBUF2_EMAC_CLK          : in std_logic;
      OBUF2_EMAC_CE           : in std_logic;
      OBUF2_EMAC_D            : out std_logic_vector(7 downto 0);
      OBUF2_EMAC_DVLD         : out std_logic;
      OBUF2_EMAC_ACK          : in  std_logic;
      OBUF2_EMAC_FIRSTBYTE    : out std_logic;
      OBUF2_EMAC_UNDERRUN     : out std_logic;
      OBUF2_EMAC_COLLISION    : in  std_logic;
      OBUF2_EMAC_RETRANSMIT   : in  std_logic;
      OBUF2_EMAC_IFGDELAY     : out std_logic_vector(7 downto 0);
      OBUF2_EMAC_STATS        : in  std_logic;
      OBUF2_EMAC_STATSVLD     : in  std_logic;
      OBUF2_EMAC_STATSBYTEVLD : in  std_logic;
      OBUF2_EMAC_SPEEDIS10100 : in  std_logic;

      -- Interface 3
      OBUF3_EMAC_CLK          : in std_logic;
      OBUF3_EMAC_CE           : in std_logic;
      OBUF3_EMAC_D            : out std_logic_vector(7 downto 0);
      OBUF3_EMAC_DVLD         : out std_logic;
      OBUF3_EMAC_ACK          : in  std_logic;
      OBUF3_EMAC_FIRSTBYTE    : out std_logic;
      OBUF3_EMAC_UNDERRUN     : out std_logic;
      OBUF3_EMAC_COLLISION    : in  std_logic;
      OBUF3_EMAC_RETRANSMIT   : in  std_logic;
      OBUF3_EMAC_IFGDELAY     : out std_logic_vector(7 downto 0);
      OBUF3_EMAC_STATS        : in  std_logic;
      OBUF3_EMAC_STATSVLD     : in  std_logic;
      OBUF3_EMAC_STATSBYTEVLD : in  std_logic;
      OBUF3_EMAC_SPEEDIS10100 : in  std_logic;

      -- ---------- MI_32 bus signals ----------------
      MI_DWR      	: in  std_logic_vector(31 downto 0);   -- Input Data
      MI_ADDR     	: in  std_logic_vector(31 downto 0);   -- Address
      MI_RD       	: in  std_logic;                       -- Read Request
      MI_WR       	: in  std_logic;                       -- Write Request
      MI_BE       	: in  std_logic_vector(3  downto 0);   -- Byte Enable
      MI_DRD      	: out std_logic_vector(31 downto 0);   -- Output Data
      MI_ARDY     	: out std_logic;                       -- Address Ready
      MI_DRDY     	: out std_logic                        -- Data Ready
   );
end entity obuf_emac_top4_mi32;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_emac_top4_mi32 is

   signal obuf0_adc_clk  : std_logic;
   signal obuf1_adc_clk  : std_logic;
   signal obuf2_adc_clk  : std_logic;
   signal obuf3_adc_clk  : std_logic;

   signal addr_sel       : std_logic_vector(1 downto 0);

   signal mi_m0_dwr      : std_logic_vector(31 downto 0);
   signal mi_m0_addr     : std_logic_vector(31 downto 0);
   signal mi_m0_rd       : std_logic;                    
   signal mi_m0_wr       : std_logic;                    
   signal mi_m0_be       : std_logic_vector(3  downto 0);
   signal mi_m0_drd      : std_logic_vector(31 downto 0);
   signal mi_m0_ardy     : std_logic;                    
   signal mi_m0_drdy     : std_logic;                    

   signal mi_s0_dwr      : std_logic_vector(31 downto 0);
   signal mi_s0_addr     : std_logic_vector(31 downto 0);
   signal mi_s0_rd       : std_logic;                    
   signal mi_s0_wr       : std_logic;                    
   signal mi_s0_be       : std_logic_vector(3  downto 0);
   signal mi_s0_drd      : std_logic_vector(31 downto 0);
   signal mi_s0_ardy     : std_logic;                    
   signal mi_s0_drdy     : std_logic;

   signal mi_m1_dwr      : std_logic_vector(31 downto 0);
   signal mi_m1_addr     : std_logic_vector(31 downto 0);
   signal mi_m1_rd       : std_logic;                    
   signal mi_m1_wr       : std_logic;                    
   signal mi_m1_be       : std_logic_vector(3  downto 0);
   signal mi_m1_drd      : std_logic_vector(31 downto 0);
   signal mi_m1_ardy     : std_logic;                    
   signal mi_m1_drdy     : std_logic;                    

   signal mi_s1_dwr      : std_logic_vector(31 downto 0);
   signal mi_s1_addr     : std_logic_vector(31 downto 0);
   signal mi_s1_rd       : std_logic;                    
   signal mi_s1_wr       : std_logic;                    
   signal mi_s1_be       : std_logic_vector(3  downto 0);
   signal mi_s1_drd      : std_logic_vector(31 downto 0);
   signal mi_s1_ardy     : std_logic;                    
   signal mi_s1_drdy     : std_logic;

   signal mi_m2_dwr      : std_logic_vector(31 downto 0);
   signal mi_m2_addr     : std_logic_vector(31 downto 0);
   signal mi_m2_rd       : std_logic;                    
   signal mi_m2_wr       : std_logic;                    
   signal mi_m2_be       : std_logic_vector(3  downto 0);
   signal mi_m2_drd      : std_logic_vector(31 downto 0);
   signal mi_m2_ardy     : std_logic;                    
   signal mi_m2_drdy     : std_logic;                    

   signal mi_s2_dwr      : std_logic_vector(31 downto 0);
   signal mi_s2_addr     : std_logic_vector(31 downto 0);
   signal mi_s2_rd       : std_logic;                    
   signal mi_s2_wr       : std_logic;                    
   signal mi_s2_be       : std_logic_vector(3  downto 0);
   signal mi_s2_drd      : std_logic_vector(31 downto 0);
   signal mi_s2_ardy     : std_logic;                    
   signal mi_s2_drdy     : std_logic;

   signal mi_m3_dwr      : std_logic_vector(31 downto 0);
   signal mi_m3_addr     : std_logic_vector(31 downto 0);
   signal mi_m3_rd       : std_logic;                    
   signal mi_m3_wr       : std_logic;                    
   signal mi_m3_be       : std_logic_vector(3  downto 0);
   signal mi_m3_drd      : std_logic_vector(31 downto 0);
   signal mi_m3_ardy     : std_logic;                    
   signal mi_m3_drdy     : std_logic;                    

   signal mi_s3_dwr      : std_logic_vector(31 downto 0);
   signal mi_s3_addr     : std_logic_vector(31 downto 0);
   signal mi_s3_rd       : std_logic;                    
   signal mi_s3_wr       : std_logic;                    
   signal mi_s3_be       : std_logic_vector(3  downto 0);
   signal mi_s3_drd      : std_logic_vector(31 downto 0);
   signal mi_s3_ardy     : std_logic;                    
   signal mi_s3_drdy     : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- OBUF 0 instantination ---------------------------------------------------
   OBUF0_U : entity work.obuf_emac
      generic map(
         DATA_PATHS => DATA_PATHS,
         DFIFO_SIZE => DFIFO_SIZE,
         SFIFO_SIZE => SFIFO_SIZE,
         CTRL_CMD   => CTRL_CMD,
         USECLKEN   => EMAC0_USECLKEN
      )
      port map(
         RESET      => RESET,
   
         -- FrameLink input interface
         WRCLK      => WRCLK,
         DATA       => OBUF0_DATA,
         DREM       => OBUF0_DREM,
         SRC_RDY_N  => OBUF0_SRC_RDY_N,
         SOF_N      => OBUF0_SOF_N,
         SOP_N      => OBUF0_SOP_N,
         EOF_N      => OBUF0_EOF_N,
         EOP_N      => OBUF0_EOP_N,
         DST_RDY_N  => OBUF0_DST_RDY_N,
   
         -- Transmit interface
         EMAC_CLK   => OBUF0_EMAC_CLK,
         EMAC_CE    => OBUF0_EMAC_CE,
         TX_EMAC_D            => OBUF0_EMAC_D,
         TX_EMAC_DVLD         => OBUF0_EMAC_DVLD,
         TX_EMAC_ACK          => OBUF0_EMAC_ACK,
         TX_EMAC_FIRSTBYTE    => OBUF0_EMAC_FIRSTBYTE,
         TX_EMAC_UNDERRUN     => OBUF0_EMAC_UNDERRUN,
         TX_EMAC_COLLISION    => OBUF0_EMAC_COLLISION,
         TX_EMAC_RETRANSMIT   => OBUF0_EMAC_RETRANSMIT,
         TX_EMAC_IFGDELAY     => OBUF0_EMAC_IFGDELAY,
         TX_EMAC_STATS        => OBUF0_EMAC_STATS,
         TX_EMAC_STATSVLD     => OBUF0_EMAC_STATSVLD,
         TX_EMAC_STATSBYTEVLD => OBUF0_EMAC_STATSBYTEVLD,
         TX_EMAC_SPEEDIS10100 => OBUF0_EMAC_SPEEDIS10100,
   
         -- address decoder interface
         ADC_CLK    => obuf0_adc_clk,
         ADC_RD     => mi_s0_rd,
         ADC_WR     => mi_s0_wr,
         ADC_ADDR   => mi_s0_addr(7 downto 2),
         ADC_DI     => mi_s0_dwr,
         ADC_DO     => mi_s0_drd,
         ADC_DRDY   => mi_s0_drdy
      );

   -- OBUF 1 instantination ---------------------------------------------------
   OBUF1_U : entity work.obuf_emac
      generic map(
         DATA_PATHS => DATA_PATHS,
         DFIFO_SIZE => DFIFO_SIZE,
         SFIFO_SIZE => SFIFO_SIZE,
         CTRL_CMD   => CTRL_CMD,
         USECLKEN   => EMAC1_USECLKEN
      )
      port map(
         RESET      => RESET,
   
         -- FrameLink input interface
         WRCLK      => WRCLK,
         DATA       => OBUF1_DATA,
         DREM       => OBUF1_DREM,
         SRC_RDY_N  => OBUF1_SRC_RDY_N,
         SOF_N      => OBUF1_SOF_N,
         SOP_N      => OBUF1_SOP_N,
         EOF_N      => OBUF1_EOF_N,
         EOP_N      => OBUF1_EOP_N,
         DST_RDY_N  => OBUF1_DST_RDY_N,
   
         -- Transmit interface
         EMAC_CLK   => OBUF1_EMAC_CLK,
         EMAC_CE    => OBUF1_EMAC_CE,
         TX_EMAC_D            => OBUF1_EMAC_D,
         TX_EMAC_DVLD         => OBUF1_EMAC_DVLD,
         TX_EMAC_ACK          => OBUF1_EMAC_ACK,
         TX_EMAC_FIRSTBYTE    => OBUF1_EMAC_FIRSTBYTE,
         TX_EMAC_UNDERRUN     => OBUF1_EMAC_UNDERRUN,
         TX_EMAC_COLLISION    => OBUF1_EMAC_COLLISION,
         TX_EMAC_RETRANSMIT   => OBUF1_EMAC_RETRANSMIT,
         TX_EMAC_IFGDELAY     => OBUF1_EMAC_IFGDELAY,
         TX_EMAC_STATS        => OBUF1_EMAC_STATS,
         TX_EMAC_STATSVLD     => OBUF1_EMAC_STATSVLD,
         TX_EMAC_STATSBYTEVLD => OBUF1_EMAC_STATSBYTEVLD,
         TX_EMAC_SPEEDIS10100 => OBUF1_EMAC_SPEEDIS10100,
   
         -- address decoder interface
         ADC_CLK    => obuf1_adc_clk,
         ADC_RD     => mi_s1_rd,
         ADC_WR     => mi_s1_wr,
         ADC_ADDR   => mi_s1_addr(7 downto 2),
         ADC_DI     => mi_s1_dwr,
         ADC_DO     => mi_s1_drd,
         ADC_DRDY   => mi_s1_drdy
      );

   -- OBUF 2 instantination ---------------------------------------------------
   OBUF2_U : entity work.obuf_emac
      generic map(
         DATA_PATHS => DATA_PATHS,
         DFIFO_SIZE => DFIFO_SIZE,
         SFIFO_SIZE => SFIFO_SIZE,
         CTRL_CMD   => CTRL_CMD,
         USECLKEN   => EMAC2_USECLKEN
      )
      port map(
         RESET      => RESET,
   
         -- FrameLink input interface
         WRCLK      => WRCLK,
         DATA       => OBUF2_DATA,
         DREM       => OBUF2_DREM,
         SRC_RDY_N  => OBUF2_SRC_RDY_N,
         SOF_N      => OBUF2_SOF_N,
         SOP_N      => OBUF2_SOP_N,
         EOF_N      => OBUF2_EOF_N,
         EOP_N      => OBUF2_EOP_N,
         DST_RDY_N  => OBUF2_DST_RDY_N,
   
         -- Transmit interface
         EMAC_CLK   => OBUF2_EMAC_CLK,
         EMAC_CE    => OBUF2_EMAC_CE,
         TX_EMAC_D            => OBUF2_EMAC_D,
         TX_EMAC_DVLD         => OBUF2_EMAC_DVLD,
         TX_EMAC_ACK          => OBUF2_EMAC_ACK,
         TX_EMAC_FIRSTBYTE    => OBUF2_EMAC_FIRSTBYTE,
         TX_EMAC_UNDERRUN     => OBUF2_EMAC_UNDERRUN,
         TX_EMAC_COLLISION    => OBUF2_EMAC_COLLISION,
         TX_EMAC_RETRANSMIT   => OBUF2_EMAC_RETRANSMIT,
         TX_EMAC_IFGDELAY     => OBUF2_EMAC_IFGDELAY,
         TX_EMAC_STATS        => OBUF2_EMAC_STATS,
         TX_EMAC_STATSVLD     => OBUF2_EMAC_STATSVLD,
         TX_EMAC_STATSBYTEVLD => OBUF2_EMAC_STATSBYTEVLD,
         TX_EMAC_SPEEDIS10100 => OBUF2_EMAC_SPEEDIS10100,
   
         -- address decoder interface
         ADC_CLK    => obuf2_adc_clk,
         ADC_RD     => mi_s2_rd,
         ADC_WR     => mi_s2_wr,
         ADC_ADDR   => mi_s2_addr(7 downto 2),
         ADC_DI     => mi_s2_dwr,
         ADC_DO     => mi_s2_drd,
         ADC_DRDY   => mi_s2_drdy
      );

   -- OBUF 3 instantination ---------------------------------------------------
   OBUF3_U : entity work.obuf_emac
      generic map(
         DATA_PATHS => DATA_PATHS,
         DFIFO_SIZE => DFIFO_SIZE,
         SFIFO_SIZE => SFIFO_SIZE,
         CTRL_CMD   => CTRL_CMD,
         USECLKEN   => EMAC3_USECLKEN
      )
      port map(
         RESET      => RESET,
   
         -- FrameLink input interface
         WRCLK      => WRCLK,
         DATA       => OBUF3_DATA,
         DREM       => OBUF3_DREM,
         SRC_RDY_N  => OBUF3_SRC_RDY_N,
         SOF_N      => OBUF3_SOF_N,
         SOP_N      => OBUF3_SOP_N,
         EOF_N      => OBUF3_EOF_N,
         EOP_N      => OBUF3_EOP_N,
         DST_RDY_N  => OBUF3_DST_RDY_N,
   
         -- Transmit interface
         EMAC_CLK   => OBUF3_EMAC_CLK,
         EMAC_CE    => OBUF3_EMAC_CE,
         TX_EMAC_D            => OBUF3_EMAC_D,
         TX_EMAC_DVLD         => OBUF3_EMAC_DVLD,
         TX_EMAC_ACK          => OBUF3_EMAC_ACK,
         TX_EMAC_FIRSTBYTE    => OBUF3_EMAC_FIRSTBYTE,
         TX_EMAC_UNDERRUN     => OBUF3_EMAC_UNDERRUN,
         TX_EMAC_COLLISION    => OBUF3_EMAC_COLLISION,
         TX_EMAC_RETRANSMIT   => OBUF3_EMAC_RETRANSMIT,
         TX_EMAC_IFGDELAY     => OBUF3_EMAC_IFGDELAY,
         TX_EMAC_STATS        => OBUF3_EMAC_STATS,
         TX_EMAC_STATSVLD     => OBUF3_EMAC_STATSVLD,
         TX_EMAC_STATSBYTEVLD => OBUF3_EMAC_STATSBYTEVLD,
         TX_EMAC_SPEEDIS10100 => OBUF3_EMAC_SPEEDIS10100,
   
         -- address decoder interface
         ADC_CLK    => obuf3_adc_clk,
         ADC_RD     => mi_s3_rd,
         ADC_WR     => mi_s3_wr,
         ADC_ADDR   => mi_s3_addr(7 downto 2),
         ADC_DI     => mi_s3_dwr,
         ADC_DO     => mi_s3_drd,
         ADC_DRDY   => mi_s3_drdy
      );

   -- MI32 --------------------------------------------------------------------
   mi32_async_u0: entity work.MI32_ASYNC_NOREC
      port map(
         RESET          => reset,
         -- Master interface
         CLK_M          => WRCLK,
         MI_M_DWR      	=> mi_m0_dwr,
         MI_M_ADDR     	=> mi_m0_addr,
         MI_M_RD       	=> mi_m0_rd,
         MI_M_WR       	=> mi_m0_wr,
         MI_M_BE       	=> mi_m0_be,
         MI_M_DRD      	=> mi_m0_drd,
         MI_M_ARDY     	=> mi_m0_ardy,
         MI_M_DRDY     	=> mi_m0_drdy,
         -- Slave interface
         CLK_S          => obuf0_adc_clk,
         MI_S_DWR      	=> mi_s0_dwr,
         MI_S_ADDR     	=> mi_s0_addr,
         MI_S_RD       	=> mi_s0_rd,
         MI_S_WR       	=> mi_s0_wr,
         MI_S_BE       	=> mi_s0_be,
         MI_S_DRD      	=> mi_s0_drd,
         MI_S_ARDY     	=> mi_s0_ardy,
         MI_S_DRDY     	=> mi_s0_drdy
      );
   mi32_async_u1: entity work.MI32_ASYNC_NOREC
      port map(
         RESET          => reset,
         -- Master interface
         CLK_M          => WRCLK,
         MI_M_DWR      	=> mi_m1_dwr,
         MI_M_ADDR     	=> mi_m1_addr,
         MI_M_RD       	=> mi_m1_rd,
         MI_M_WR       	=> mi_m1_wr,
         MI_M_BE       	=> mi_m1_be,
         MI_M_DRD      	=> mi_m1_drd,
         MI_M_ARDY     	=> mi_m1_ardy,
         MI_M_DRDY     	=> mi_m1_drdy,
         -- Slave interface
         CLK_S          => obuf1_adc_clk,
         MI_S_DWR      	=> mi_s1_dwr,
         MI_S_ADDR     	=> mi_s1_addr,
         MI_S_RD       	=> mi_s1_rd,
         MI_S_WR       	=> mi_s1_wr,
         MI_S_BE       	=> mi_s1_be,
         MI_S_DRD      	=> mi_s1_drd,
         MI_S_ARDY     	=> mi_s1_ardy,
         MI_S_DRDY     	=> mi_s1_drdy
      );
   mi32_async_u2: entity work.MI32_ASYNC_NOREC
      port map(
         RESET          => reset,
         -- Master interface
         CLK_M          => WRCLK,
         MI_M_DWR      	=> mi_m2_dwr,
         MI_M_ADDR     	=> mi_m2_addr,
         MI_M_RD       	=> mi_m2_rd,
         MI_M_WR       	=> mi_m2_wr,
         MI_M_BE       	=> mi_m2_be,
         MI_M_DRD      	=> mi_m2_drd,
         MI_M_ARDY     	=> mi_m2_ardy,
         MI_M_DRDY     	=> mi_m2_drdy,
         -- Slave interface
         CLK_S          => obuf2_adc_clk,
         MI_S_DWR      	=> mi_s2_dwr,
         MI_S_ADDR     	=> mi_s2_addr,
         MI_S_RD       	=> mi_s2_rd,
         MI_S_WR       	=> mi_s2_wr,
         MI_S_BE       	=> mi_s2_be,
         MI_S_DRD      	=> mi_s2_drd,
         MI_S_ARDY     	=> mi_s2_ardy,
         MI_S_DRDY     	=> mi_s2_drdy
      );
   mi32_async_u3: entity work.MI32_ASYNC_NOREC
      port map(
         RESET          => reset,
         -- Master interface
         CLK_M          => WRCLK,
         MI_M_DWR      	=> mi_m3_dwr,
         MI_M_ADDR     	=> mi_m3_addr,
         MI_M_RD       	=> mi_m3_rd,
         MI_M_WR       	=> mi_m3_wr,
         MI_M_BE       	=> mi_m3_be,
         MI_M_DRD      	=> mi_m3_drd,
         MI_M_ARDY     	=> mi_m3_ardy,
         MI_M_DRDY     	=> mi_m3_drdy,
         -- Slave interface
         CLK_S          => obuf3_adc_clk,
         MI_S_DWR      	=> mi_s3_dwr,
         MI_S_ADDR     	=> mi_s3_addr,
         MI_S_RD       	=> mi_s3_rd,
         MI_S_WR       	=> mi_s3_wr,
         MI_S_BE       	=> mi_s3_be,
         MI_S_DRD      	=> mi_s3_drd,
         MI_S_ARDY     	=> mi_s3_ardy,
         MI_S_DRDY     	=> mi_s3_drdy
      );
   
   addr_sel  <= MI_ADDR(9 downto 8);
   
   mi_s0_ardy <= mi_s0_rd or mi_s0_wr;
   mi_s1_ardy <= mi_s1_rd or mi_s1_wr;
   mi_s2_ardy <= mi_s2_rd or mi_s2_wr;
   mi_s3_ardy <= mi_s3_rd or mi_s3_wr;
   
   -- MI_DWR connection
   mi_m0_dwr <= MI_DWR;
   mi_m1_dwr <= MI_DWR;
   mi_m2_dwr <= MI_DWR;
   mi_m3_dwr <= MI_DWR;
   
   -- MI_ADDR connection
   mi_m0_addr <= MI_ADDR;
   mi_m1_addr <= MI_ADDR;
   mi_m2_addr <= MI_ADDR;
   mi_m3_addr <= MI_ADDR;
   
   -- MI_RD demultiplexor -----------------------------------------------------
   mi_m0_rd <= MI_RD when (addr_sel="00") else '0';
   mi_m1_rd <= MI_RD when (addr_sel="01") else '0';
   mi_m2_rd <= MI_RD when (addr_sel="10") else '0';
   mi_m3_rd <= MI_RD when (addr_sel="11") else '0';
   
   -- MI_WR demultiplexor -----------------------------------------------------
   mi_m0_wr <= MI_WR when (addr_sel="00") else '0';
   mi_m1_wr <= MI_WR when (addr_sel="01") else '0';
   mi_m2_wr <= MI_WR when (addr_sel="10") else '0';
   mi_m3_wr <= MI_WR when (addr_sel="11") else '0';
   
   -- MI_BE connection
   mi_m0_be <= MI_BE;
   mi_m1_be <= MI_BE;
   mi_m2_be <= MI_BE;
   mi_m3_be <= MI_BE;
   
   -- MI_DRD multiplexor ------------------------------------------------------
   MI_DRD   <= mi_m0_drd when (addr_sel="00") else
               mi_m1_drd when (addr_sel="01") else
               mi_m2_drd when (addr_sel="10") else
               mi_m3_drd when (addr_sel="11") else
   	         (others=>'X');
   
   -- MI_ARDY control --------------------------------------------------------
   MI_ARDY   <= mi_m0_ardy when (addr_sel="00") else
                mi_m1_ardy when (addr_sel="01") else
                mi_m2_ardy when (addr_sel="10") else
                mi_m3_ardy when (addr_sel="11") else
   	          '0';
   
   -- MI_DRDY multiplexor -----------------------------------------------------
   MI_DRDY   <= mi_m0_drdy when (addr_sel="00") else
                mi_m1_drdy when (addr_sel="01") else
                mi_m2_drdy when (addr_sel="10") else
                mi_m3_drdy when (addr_sel="11") else
   	          '0';

end architecture full;
