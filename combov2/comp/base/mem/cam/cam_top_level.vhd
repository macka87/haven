--
-- cam_top_level.vhd: Top level wrapper for CAM + communication via LB
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity CAM_TOP_LEVEL is
   generic (
      BASE              : integer;
      -- Width of localbus address bus 
      -- should be greater or equal 5
      ADDR_WIDTH        : integer;
      ADC_FREQUENCY     : integer;
      -- Data row width (bits, should be a multiple of 4)
      CAM_ROW_WIDTH     : integer;
      -- Number of data rows (depth of the CAM - should be greater than 1)
      CAM_ROW_COUNT     : integer
   );
   port (
      --global signals
      CLK               : in std_logic;
      RESET             : in std_logic;
      
      -- CAM interface
      ADDR              : in std_logic_vector(log2(CAM_ROW_COUNT)-1 downto 0);
      DATA_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      MASK_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      WRITE_EN          : in std_logic;
      MATCH_EN          : in std_logic;
      MATCH_RST         : in std_logic;
      MATCH_BUS         : out std_logic_vector((CAM_ROW_COUNT - 1) downto 0);
      MATCH_BUS_VLD     : out std_logic;
      
      -- control signals between SW and HW side
      -- request from SW to hardware side so that SW can control CAM
      RQ                : out std_logic;
      -- Acknowledge from hardware side to software, that it can use CAM
      ACK               : in std_logic;
      -- CAM is busy (sw side is working with CAM)
      BUSY              : out std_logic;
      
      -- local bus interface
      LBCLK             : in    std_logic;
      LBFRAME           : in    std_logic;
      LBHOLDA           : out   std_logic;
      LBAD              : inout std_logic_vector(15 downto 0);
      LBAS              : in    std_logic;
      LBRW              : in    std_logic;
      LBRDY             : out   std_logic;
      LBLAST            : in    std_logic
   );
end entity CAM_TOP_LEVEL;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of CAM_TOP_LEVEL is

   -- assertions

   -- ------------------ Constant declaration ----------------------------------
   constant CAM_ADDR_WIDTH      : integer := log2(CAM_ROW_COUNT);
   
   -- ------------------ Signals declaration ----------------------------------
   -- lbconn_mem signals
   signal lb_data_out      : std_logic_vector(31 downto 0);
   signal lb_data_in       : std_logic_vector(31 downto 0);
   signal lb_addr          : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal lb_rd            : std_logic;
   signal lb_wr            : std_logic;
   signal lb_drdy          : std_logic;

   signal lb_en            : std_logic;

   -- CAM signals
   signal cam_addr          : std_logic_vector(CAM_ADDR_WIDTH-1 downto 0);
   signal cam_data_in       : std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
   signal cam_mask_in       : std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
   signal cam_write_en      : std_logic;
   signal cam_match_en      : std_logic;
   signal cam_match_rst     : std_logic;
   signal cam_reset         : std_logic;
   signal cam_clk           : std_logic;
   signal cam_match_bus     : std_logic_vector(CAM_ROW_COUNT-1 downto 0);
   signal cam_match_bus_vld : std_logic;

begin
   -- assertions
   assert CAM_ROW_COUNT > 1
      report "CAM: There has to be at least two rows in CAM!"
   severity error;

   lb_en <= lb_rd or lb_wr;

   -- ------------------ Local bus connection ---------------------------------
   LB_CONNECT_I : entity work.lb_connect
   generic map(
      BASE_ADDR   => BASE,
      ADDR_WIDTH  => ADDR_WIDTH,
      FREQUENCY   => ADC_FREQUENCY
   )
   port map(
      -- Control signals
      RESET       => RESET,

      -- LB signals
      LBCLK       => LBCLK,
      LBFRAME     => LBFRAME,
      LBHOLDA     => LBHOLDA,
      LBAD        => LBAD,
      LBAS        => LBAS,
      LBRW        => LBRW,
      LBRDY       => LBRDY,
      LBLAST      => LBLAST,

      -- Address decoder interface
      CLK         => CLK,
      ADC_RD      => lb_rd,
      ADC_WR      => lb_wr,
      ADC_ADDR    => lb_addr,
      ADC_DI      => lb_data_in,
      ADC_DO      => lb_data_out,
      ADC_DRDY    => lb_drdy
   );
   
   -- ------------------ CAM localbus bridge ----------------------------------
   CAM_LB_BRIDGE_I : entity work.cam_lb_bridge
   generic map(
      LB_ADDR_WIDTH     => (ADDR_WIDTH - 2),
      CAM_ADDR_WIDTH    => CAM_ADDR_WIDTH,
      CAM_ROW_WIDTH     => CAM_ROW_WIDTH,
      CAM_ROW_COUNT     => CAM_ROW_COUNT
      )
   port map(
      -- Connected hardware signals
      HW_ADDR           => ADDR,
      HW_DATA_IN        => DATA_IN,
      HW_MASK_IN        => MASK_IN,
      HW_WRITE_EN       => WRITE_EN,
      HW_MATCH_EN       => MATCH_EN,
      HW_MATCH_RST      => MATCH_RST,
      HW_RESET          => RESET,
      HW_CLK            => CLK,
      HW_MATCH_BUS      => MATCH_BUS,
      HW_MATCH_BUS_VLD  => MATCH_BUS_VLD,
      
      RQ                => RQ,
      ACK               => ACK,
      BUSY              => BUSY,

      -- Address decoder interface (component between lb_bridge and lb)
      ADC_WR            => lb_wr,
      ADC_ADDR          => lb_addr(ADDR_WIDTH-1 downto 2),
      ADC_DI            => lb_data_in,
      ADC_DO            => lb_data_out,
      ADC_DRDY          => lb_drdy,

      EN                => lb_en,
      LBCLK             => LBCLK,
      
      -- CAM side signals
      CAM_ADDR          => cam_addr,
      CAM_DATA_IN       => cam_data_in,
      CAM_MASK_IN       => cam_mask_in,
      CAM_WRITE_EN      => cam_write_en,
      CAM_MATCH_EN      => cam_match_en,
      CAM_MATCH_RST     => cam_match_rst,
      CAM_RESET         => cam_reset,
      CAM_CLK           => cam_clk,
      CAM_MATCH_BUS     => cam_match_bus,
      CAM_MATCH_BUS_VLD => cam_match_bus_vld
   );

   -- ------------------ CAM --------------------------------------------------
   CAM_I : entity work.CAM
   generic map(
      CAM_ROW_WIDTH     => CAM_ROW_WIDTH,
      CAM_ROW_COUNT     => CAM_ROW_COUNT,
      CAM_ADDR_WIDTH    => CAM_ADDR_WIDTH
   )
   port map(
      ADDR              => cam_addr,
      DATA_IN           => cam_data_in,
      MASK_IN           => cam_mask_in,
      WRITE_EN          => cam_write_en,
      MATCH_EN          => cam_match_en,
      MATCH_RST         => cam_match_rst,
      RESET             => cam_reset,
      CLK               => cam_clk,
      MATCH_BUS         => cam_match_bus,
      MATCH_BUS_VLD     => cam_match_bus_vld
   );

end architecture full;
