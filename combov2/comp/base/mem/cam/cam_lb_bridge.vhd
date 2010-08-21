--
-- lb_bridge.vhd: CAM localbus bridge.
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

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cam_lb_bridge is
   generic(
      -- Localbus bridge data width
      LB_ADDR_WIDTH     : integer;
      -- CAM address width - should be greater or equal log2(CAM_ROW_COUNT)
      CAM_ADDR_WIDTH     : integer;
      -- CAM data row width (bits, should be a multiple of 4)
      CAM_ROW_WIDTH     : integer;
      -- Number of CAM data rows (depth of the CAM)
      CAM_ROW_COUNT     : integer
      );
   port(
      -- Connected hardware signals
      HW_ADDR           : in std_logic_vector(CAM_ADDR_WIDTH-1 downto 0);
      HW_DATA_IN        : in std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
      HW_MASK_IN        : in std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
      HW_WRITE_EN       : in std_logic;
      HW_MATCH_EN       : in std_logic;
      HW_MATCH_RST      : in std_logic;
      HW_RESET          : in std_logic;
      HW_CLK            : in std_logic;
      HW_MATCH_BUS      : out std_logic_vector(CAM_ROW_COUNT-1 downto 0);
      HW_MATCH_BUS_VLD  : out std_logic;
      
      RQ                : out std_logic;
      ACK               : in std_logic;
      BUSY              : out std_logic;

      -- Address decoder interface (component between lb_bridge and lb)
      ADC_WR            : in std_logic;
      ADC_ADDR          : in std_logic_vector(LB_ADDR_WIDTH-1 downto 0);
      ADC_DI            : in std_logic_vector(31 downto 0);
      ADC_DO            : out std_logic_vector(31 downto 0);
      ADC_DRDY          : out std_logic;

      EN                : in std_logic;
      LBCLK             : in  std_logic;
      
      -- CAM side signals
      CAM_ADDR          : out std_logic_vector(CAM_ADDR_WIDTH-1 downto 0);
      CAM_DATA_IN       : out std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
      CAM_MASK_IN       : out std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
      CAM_WRITE_EN      : out std_logic;
      CAM_MATCH_EN      : out std_logic;
      CAM_MATCH_RST     : out std_logic;
      CAM_RESET         : out std_logic;
      CAM_CLK           : out std_logic;
      CAM_MATCH_BUS     : in std_logic_vector(CAM_ROW_COUNT-1 downto 0);
      CAM_MATCH_BUS_VLD : in std_logic
   );
end entity cam_lb_bridge;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture lb_bridge_arch of cam_lb_bridge is
   
   -- ------------------ Constant declaration ----------------------------------
   -- number of registers (filled from LB) needed to fit CAM_ROW_WIDTH
   constant LB_REG_COUNT      : integer := (CAM_ROW_WIDTH / 32) + 1;
   -- width of registers (filled from LB)
   constant LB_REG_WIDTH      : integer := LB_REG_COUNT * 32;

   -- ---------------- Distributed Shift Register Component Declaration -------
   component SRL16E is
      generic (
         INIT : bit_vector := X"0000"
      );
      port    (
         d   : in  std_logic;
         ce  : in  std_logic;
         clk : in  std_logic;
         a0  : in  std_logic;
         a1  : in  std_logic;
         a2  : in  std_logic;
         a3  : in  std_logic;
         q   : out std_logic
      ); 
   end component;

   -- ---------------------- cam_dec1fn Component Declaration -----------------
   component cam_dec1fn is
      generic(
         ITEMS       : integer
      );
      port(
         ADDR        : in std_logic_vector(log2(ITEMS)-1 downto 0);
         ENABLE      : in std_logic;
         DO          : out std_logic_vector(ITEMS-1 downto 0)
      );
   end component cam_dec1fn;

   -- ------------------ Signals declaration ----------------------------------
   -- hw_sw: '0' -> HW connected, '1' -> SW connected
   signal hw_sw         : std_logic;
   -- multiplexer signals
   signal mux_addr      : std_logic_vector(CAM_ADDR_WIDTH-1 downto 0);
   signal mux_data_in   : std_logic_vector(CAM_ROW_WIDTH - 1 downto 0);
   signal mux_mask_in   : std_logic_vector(CAM_ROW_WIDTH - 1 downto 0);
   signal mux_match_en  : std_logic;
   signal mux_write_en  : std_logic;
   signal mux_lbaddr    : std_logic_vector(LB_ADDR_WIDTH-1 downto 0);
   signal sw_addr       : std_logic_vector(log2(CAM_ROW_COUNT) - 1 downto 0);
   signal sw_data_in    : std_logic_vector(CAM_ROW_WIDTH - 1 downto 0);
   signal sw_mask_in    : std_logic_vector(CAM_ROW_WIDTH - 1 downto 0);
   signal sw_match_en   : std_logic;
   signal sw_write_en   : std_logic;

   -- tcam signal: '1' -> we want to write data into CAM
   signal tcam          : std_logic;
   signal tcam_dly      : std_logic;

   -- Registers & WE signals
   signal reg_cmd       : std_logic_vector(31 downto 0);
   signal reg_cmd_we    : std_logic;
   signal reg_status    : std_logic_vector(31 downto 0);
   signal reg_data_in   : std_logic_vector(LB_REG_WIDTH-1 downto 0);
   signal reg_data_in_we : std_logic_vector(15 downto 0);   -- width: 512 /32
   signal reg_data_in_we_en : std_logic;
   signal reg_mask_in   : std_logic_vector(LB_REG_WIDTH-1 downto 0);
   signal reg_mask_in_we : std_logic_vector(15 downto 0);   -- width: 512 /32
   signal reg_mask_in_we_en : std_logic;
   signal reg_addr      : std_logic_vector(log2(CAM_ROW_COUNT)-1 downto 0);
   signal reg_addr_we   : std_logic;
   signal reg_write_en  : std_logic;
   signal reg_drdy      : std_logic;
   signal reg_lbaddr    : std_logic_vector(LB_ADDR_WIDTH-1 downto 0);
   signal reg_lbaddr_we : std_logic;
   
begin

   -- connecting signals directly between CAM and connected hardware
   CAM_MATCH_RST     <= HW_MATCH_RST;
   CAM_CLK           <= HW_CLK;
   CAM_RESET         <= HW_RESET;
   CAM_ADDR          <= mux_addr;
   CAM_DATA_IN       <= mux_data_in;
   CAM_MASK_IN       <= mux_mask_in;
   CAM_MATCH_EN      <= mux_match_en;
   CAM_WRITE_EN      <= mux_write_en;
   HW_MATCH_BUS      <= CAM_MATCH_BUS;
   HW_MATCH_BUS_VLD  <= CAM_MATCH_BUS_VLD;

  
-- --------------------------- MUX SECTION ------------------------------------

-- multiplexor mux_addr -------------------------------------------------------
   mux_addrp: process(hw_sw, HW_ADDR, sw_addr)
   begin
      case hw_sw is
         when '0' => mux_addr <= HW_ADDR;
         when '1' => mux_addr <= sw_addr;
         when others => mux_addr <= (others => 'X');
      end case;
   end process;

-- multiplexor mux_data_in ----------------------------------------------------
   mux_data_inp: process(hw_sw, HW_DATA_IN, sw_data_in)
   begin
      case hw_sw is
         when '0' => mux_data_in <= HW_DATA_IN;
         when '1' => mux_data_in <= sw_data_in;
         when others => mux_data_in <= (others => 'X');
      end case;
   end process;

-- multiplexor mux_mask_in ----------------------------------------------------
   mux_mask_inp: process(hw_sw, HW_MASK_IN, sw_mask_in)
   begin
      case hw_sw is
         when '0' => mux_mask_in <= HW_MASK_IN;
         when '1' => mux_mask_in <= sw_mask_in;
         when others => mux_mask_in <= (others => 'X');
      end case;
   end process;

-- multiplexor mux_match_en ---------------------------------------------------
   mux_match_enp: process(hw_sw, HW_MATCH_EN, sw_match_en)
   begin
      case hw_sw is
         when '0' => mux_match_en <= HW_MATCH_EN;
         when '1' => mux_match_en <= sw_match_en;
         when others => mux_match_en <= 'X';
      end case;
   end process;

-- multiplexor mux_write_en ---------------------------------------------------
   mux_write_enp: process(hw_sw, HW_WRITE_EN, sw_write_en)
   begin
      case hw_sw is
         when '0' => mux_write_en <= HW_WRITE_EN;
         when '1' => mux_write_en <= sw_write_en;
         when others => mux_write_en <= 'X';
      end case;
   end process;

-- ------------------------------- SW_REGS ------------------------------------

-- -------- Directly mapped signals -------------------------------------------
   RQ          <= reg_cmd(0);
   BUSY        <= reg_cmd(1);
   hw_sw       <= reg_cmd(1);
   
   reg_lbaddr_we <= (EN and (not reg_drdy)) or ADC_WR;

   -- mapping registers to correct sw_* signals -------------------------------
   sw_addr     <= reg_addr;
   sw_match_en <= '0';  --matching from sw is disabled
   sw_write_en <= reg_write_en;
   
   -- -------- Mapping reg_data_in to correct size ----------------------------
   MAP_REG_DATA_IN: for i in 0 to (CAM_ROW_WIDTH - 1) generate
      sw_data_in(i) <= reg_data_in(i);
   end generate;

   -- -------- Mapping reg_mask_in to correct size ----------------------------
   MAP_REG_MASK_IN: for i in 0 to (CAM_ROW_WIDTH - 1) generate
      sw_mask_in(i) <= reg_mask_in(i);
   end generate;

   -- ------------------ ADC --------------------------------------------------
   adcp: process (ADC_DI, ADC_WR, EN, ADC_ADDR, mux_lbaddr, reg_drdy, reg_cmd, 
                  reg_status, reg_mask_in, reg_data_in, reg_addr)
   begin
      ADC_DO            <= (others => '0');
      reg_cmd_we        <= '0';
      reg_addr_we       <= '0';
      tcam              <= '0';
      reg_data_in_we_en <= '0';
      reg_mask_in_we_en <= '0';

      ADC_DRDY          <= reg_drdy;

      case mux_lbaddr(6 downto 4) is
         when "000"    => -- command register: R/W
            ADC_DO      <= reg_cmd;
            reg_cmd_we  <= ADC_WR;
         when "001"    => -- status register: R
            ADC_DO      <= reg_status;
         when "010"    => -- mask register: R/W
            reg_mask_in_we_en <= ADC_WR;
         when "011"    => -- data_in register
            reg_data_in_we_en <= ADC_WR;
         when "100"    => -- address register: R/W
            ADC_DO(log2(CAM_ROW_COUNT)-1 downto 0) <= reg_addr;
            reg_addr_we <= ADC_WR;
         when "101"    => -- Write data into CAM
            tcam  <= ADC_WR;
         when others => null;
      end case;
   end process;

   -- --------- Generating and maping generic decoder cam_dec1fn --------------
   MASK_DEC1FN : cam_dec1fn
      generic map (
         ITEMS       => 16    -- 512 / 32
      )
      port map (
         ADDR        => mux_lbaddr(3 downto 0),
         ENABLE      => reg_mask_in_we_en,
         DO          => reg_mask_in_we
      );
   
   -- --------- Generating and maping generic decoder cam_dec1fn --------------
   DATA_DEC1FN : cam_dec1fn
      generic map (
         ITEMS       => 16    -- 512 / 32
      )
      port map (
         ADDR        => mux_lbaddr(3 downto 0),
         ENABLE      => reg_data_in_we_en,
         DO          => reg_data_in_we
      );

   -- register reg_lbaddr -----------------------------------------------------
   reg_lbaddrp: process(HW_RESET, LBCLK)
   begin
      if (HW_RESET = '1') then
         reg_lbaddr <= (others => '0');
      elsif (LBCLK'event AND LBCLK = '1') then
         if (reg_lbaddr_we = '1') then
            reg_lbaddr <= ADC_ADDR(LB_ADDR_WIDTH-1 downto 0);
         end if;
      end if;
   end process;

   -- register reg_drdy -------------------------------------------------------
   reg_drdyp: process(HW_RESET, HW_CLK)
   begin
      if (HW_RESET = '1') then
         reg_drdy <= '0';
      elsif (HW_CLK'event AND HW_CLK = '1') then
         reg_drdy <= EN and (not ADC_WR) and (not reg_drdy) ;
      end if;
   end process;

   -- ------------------ Multiplexer ------------------------------------------
   mux_lbaddrp: process( reg_lbaddr_we, reg_lbaddr, ADC_ADDR )
   begin
      case reg_lbaddr_we is
         when '0'  =>  mux_lbaddr <= reg_lbaddr;
         when '1'  =>  mux_lbaddr <= ADC_ADDR(LB_ADDR_WIDTH-1 downto 0);
         when others =>  mux_lbaddr <= (others => '0');
      end case;
   end process;

-- shift register SRL16E ------------------------------------------------------
   DELAY_REG : SRL16E
   -- synthesis translate_off
   generic map (INIT => X"0000")
   -- synthesis translate_on
   port map (
      d => tcam,
      ce => '1',
      clk => HW_CLK,
      a0 => '1',
      a1 => '1',
      a2 => '1',
      a3 => '1',
      q => tcam_dly
   );

   -- register reg_cmd --------------------------------------------------------
   reg_cmdp: process(HW_RESET, LBCLK)
   begin
      if (HW_RESET = '1') then
         reg_cmd <= (others => '0');
      elsif (LBCLK'event AND LBCLK = '1') then
         if (reg_cmd_we = '1') then
            reg_cmd <= ADC_DI;
         end if;
      end if;
   end process;
   
   -- register reg_status(0) (ACK) --------------------------------------------
   reg_statusp0: process(HW_RESET, HW_CLK)
   begin
      if (HW_RESET = '1') then
         reg_status(0) <= '0';
      elsif (HW_CLK'event AND HW_CLK = '1') then
         reg_status(0) <= ACK;
      end if;
   end process;

   -- register reg_status(1) (cam_busy) ---------------------------------------
   reg_statusp1: process(HW_RESET, HW_CLK)
   begin
      if (HW_RESET = '1') then
         reg_status(1) <= '0';
      elsif (HW_CLK'event AND HW_CLK = '1') then
         if (tcam = '1' or tcam_dly = '1') then
            reg_status(1) <= tcam and (not tcam_dly);
         end if;
      end if;
   end process;

   -- register reg_status(7 downto 2) (reserved) ------------------------------
   reg_status7_2: process(HW_RESET, HW_CLK)
   begin
      if (HW_RESET = '1') then
         reg_status(7 downto 2) <= (others => '0');
      elsif (HW_CLK'event AND HW_CLK = '1') then
         reg_status(7 downto 2) <= (others => '0');
      end if;
   end process;

   -- register reg_status(15 downto 8) (log2(CAM_ROW_COUNT)) ------------------
   reg_status15_8: process(HW_RESET, HW_CLK)
   begin
      if (HW_RESET = '1') then
         reg_status(15 downto 8) <= (others => '0');
      elsif (HW_CLK'event AND HW_CLK = '1') then
         if (tcam = '1' or tcam_dly = '1') then
            reg_status(15 downto 8) <=
               conv_std_logic_vector(log2(CAM_ROW_COUNT), 8);
         end if;
      end if;
   end process;

   -- register reg_status(31 downto 16) (reserved) ----------------------------
   reg_status31_16: process(HW_RESET, HW_CLK)
   begin
      if (HW_RESET = '1') then
         reg_status(31 downto 16) <= (others => '0');
      elsif (HW_CLK'event AND HW_CLK = '1') then
         reg_status(31 downto 16) <= (others => '0');
      end if;
   end process;

   -- data_in register mapping ------------------------------------------------
   GEN_DATA_IN: for i in 0 to LB_REG_COUNT-1 generate

      -- register reg_data_in -------------------------------------------------
      reg_data_inp: process(HW_RESET, LBCLK)
      begin
         if (HW_RESET = '1') then
            reg_data_in(((i+1) * 32) - 1 downto i*32) <= (others => '0');
         elsif (LBCLK'event AND LBCLK = '1') then
            if (reg_data_in_we(i) = '1') then
               reg_data_in(((i+1) * 32) - 1 downto i*32) <= ADC_DI;
            end if;
         end if;
      end process;

   end generate;

   -- mask_in register mapping ------------------------------------------------
   GEN_MASK_IN: for i in 0 to LB_REG_COUNT-1 generate

      -- register reg_mask_in -------------------------------------------------
      reg_mask_inp: process(HW_RESET, LBCLK)
      begin
         if (HW_RESET = '1') then
            reg_mask_in(((i+1) * 32) - 1 downto i*32) <= (others => '0');
         elsif (LBCLK'event AND LBCLK = '1') then
            if (reg_mask_in_we(i) = '1') then
               reg_mask_in(((i+1) * 32) - 1 downto i*32) <= ADC_DI;
            end if;
         end if;
      end process;

   end generate;

   -- register reg_addr -------------------------------------------------------
   reg_addrp: process(HW_RESET, LBCLK)
   begin
      if (HW_RESET = '1') then
         reg_addr <= (others => '0');
      elsif (LBCLK'event AND LBCLK = '1') then
         if (reg_addr_we = '1') then
            reg_addr <= ADC_DI(log2(CAM_ROW_COUNT)-1 downto 0);
         end if;
      end if;
   end process;

   -- register reg_write_en ---------------------------------------------------
   reg_write_enp: process(HW_RESET, LBCLK)
   begin
      if (HW_RESET = '1') then
         reg_write_en <= '0';
      elsif (LBCLK'event AND LBCLK = '1') then
         reg_write_en <= tcam;
      end if;
   end process;

end architecture lb_bridge_arch;
