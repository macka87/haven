--
-- sp3.vhd: Top level for ComboV2 Spartan3E FPGA 
-- Copyright (C) 2009  CESNET
-- Author: Stepan Friedl <friedl@liberouter.org>
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

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;
use work.ib_pkg.all; -- Internal Bus Package

architecture behavioral of fpga_u16 is

constant REVISION   : std_logic_vector(31 downto 0) := X"6d050107";
-- constant BUILD_TIME : std_logic_vector(31 downto 0) := X"8C131400";

-- component test_top
-- port (
--    sys_clk_pin                                : IN std_logic;
--    CLED_pin                                   : OUT std_logic_vector(3 downto 0);
--    -- RS232
--    fpga_0_RS232_RX_pin                        : IN std_logic;
--    fpga_0_RS232_TX_pin                        : OUT std_logic;
--    -- FLASH/PSRAM inteface
--    fpga_0_Generic_External_Memory_Mem_A_pin   : OUT std_logic_vector(25 downto 0);
--    fpga_0_Generic_External_Memory_Mem_BEN_pin : OUT std_logic_vector(1 downto 0);
--    fpga_0_Generic_External_Memory_Mem_WEN_pin : OUT std_logic;
--    fpga_0_Generic_External_Memory_Mem_OEN_pin : OUT std_logic;
--    fpga_0_Generic_External_Memory_Mem_CEN_pin : OUT std_logic_vector(1 downto 0);
--    Generic_External_Memory_Mem_DQ_I_pin       : IN std_logic_vector(15 downto 0);
--    Generic_External_Memory_Mem_DQ_T_pin       : OUT std_logic_vector(15 downto 0);
--    Generic_External_Memory_Mem_DQ_O_pin       : OUT std_logic_vector(15 downto 0);
--    FBYTE_N                                    : OUT std_logic;
--    FZZ_N                                      : OUT std_logic;
--    FRY                                        : IN std_logic;
--    -- FIFO
--    ifc_bridge_0_ifc_fifo_read_data_pin        : OUT std_logic_vector(31 downto 0);
--    ifc_bridge_0_ifc_fifo_empty_pin            : OUT std_logic;
--    ifc_bridge_0_ifc_fifo_almost_empty_pin     : OUT std_logic;
--    ifc_bridge_0_ifc_fifo_full_pin             : OUT std_logic;
--    ifc_bridge_0_ifc_fifo_almost_full_pin      : OUT std_logic;
--    ifc_bridge_0_ifc_fifo_ren_pin              : IN std_logic;
--    ifc_bridge_0_ifc_fifo_write_data_pin       : IN std_logic_vector(31 downto 0);
--    ifc_bridge_0_ifc_fifo_wen_pin              : IN std_logic;
--    ifc_bridge_0_ifc_fifo_start_transaction_pin: IN std_logic;
--    ifc_bridge_0_ifc_fifo_clk_pin              : IN std_logic
-- );
-- end component;

  -------------------------------------------------------------------
  --  ILA core component declaration
  -------------------------------------------------------------------
  component sp3_ll64_ila
    port
    (
      control     : in    std_logic_vector(35 downto 0);
      clk         : in    std_logic;
      trig0       : in    std_logic_vector(63 downto 0);
      trig1       : in    std_logic_vector( 7 downto 0)
    );
  end component;
   
  component sp3_icon2
    port
    (
      control0    :   out std_logic_vector(35 downto 0);
      control1    :   out std_logic_vector(35 downto 0)
      );
  end component;

  signal control0 : std_logic_vector(35 downto 0);
  signal control1 : std_logic_vector(35 downto 0);
  signal rx_trig0 : std_logic_vector(63 downto 0);
  signal rx_trig1 : std_logic_vector( 7 downto 0);
  signal tx_trig0 : std_logic_vector(63 downto 0);
  signal tx_trig1 : std_logic_vector( 7 downto 0);
  
  attribute noopt : boolean;
  attribute dont_touch : boolean;
--  attribute preserve_driver : boolean;  
 
  attribute noopt of sp3_icon2 : component is TRUE;
  attribute noopt of sp3_ll64_ila   : component is TRUE;
  attribute dont_touch of sp3_icon2 : component is TRUE;
  attribute dont_touch of sp3_ll64_ila : component is TRUE;  
  

signal led_cntr : std_logic_vector(23 downto 0);

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 
signal reset       : std_logic;
signal sw_reset    : std_logic;
signal soft_reset  : std_logic;
signal rxreset     : std_logic;
--signal rst_cntr    : std_logic_vector(17 downto 0); -- ~ 1.2us reset pulse
signal rst_cntr    : std_logic_vector(23 downto 0); -- ~ 67ms reset pulse
signal sysclk      : std_logic;
signal cclk_ifc    : std_logic;
signal clkman_locked: std_logic;
signal ifcboot_rst : std_logic;
signal xrd_boot    : std_logic_vector( 7 downto 0);
signal xrcs_n_boot : std_logic;
signal sw_reconfig : std_logic;
signal sw_revsel   : std_logic_vector( 4 downto 0);
signal cfg_addr    : std_logic_vector(25 downto 0);
signal cfg_flash_sel : std_logic;
signal boot_done     : std_logic;
signal boot_timeout  : std_logic;

signal ib_clk    : std_logic;
signal rxdcm_locked : std_logic;
signal ib         : t_internal_bus64;
signal wen        : std_logic;
signal en         : std_logic;
signal drd_vld    : std_logic;
signal drd_rd     : std_logic;
signal drd_rdy    : std_logic;
signal drd_xfer   : std_logic;
signal rxdebug    : std_logic_vector(15 downto 0);

-- Data/Address buses
signal addr_wr    : std_logic_vector(31 downto 0);
signal addr_rd    : std_logic_vector(31 downto 0);
signal drd        : std_logic_vector(63 downto 0);
signal dwr        : std_logic_vector(63 downto 0);
signal dwr_be     : std_logic_vector( 7 downto 0);
signal wr_rdy     : std_logic;

signal cs_boot         : std_logic;
-- Flash interface -- "boot" component
signal fa_boot         : std_logic_vector(25 downto 0);
signal fwe_n_boot      : std_logic;
signal fcsflash_n_boot : std_logic;
signal fcsram_n_boot   : std_logic;
signal foe_n_boot      : std_logic;
signal fbyte_n_boot    : std_logic;
signal flb_n_boot      : std_logic;
signal fub_n_boot      : std_logic;
signal fzz_n_boot      : std_logic;
signal config_led      : std_logic_vector( 3 downto 0);
-- Flash interface -- MicroBlaze
signal mb_fd_oen       : std_logic;
signal fd_mb           : std_logic_vector(15 downto 0);
signal fa_mb           : std_logic_vector(25 downto 0);
signal fwe_n_mb        : std_logic;
signal fcsflash_n_mb   : std_logic;
signal fcsram_n_mb     : std_logic;
signal foe_n_mb        : std_logic;
signal fbyte_n_mb      : std_logic;
signal flb_n_mb        : std_logic;
signal fub_n_mb        : std_logic;
signal fzz_n_mb        : std_logic;
--
signal mb_mem_cen : std_logic_vector(1 downto 0);
signal mb_cmd     : std_logic;
signal mb_cmd_ack : std_logic;
signal mb_dwr     : std_logic_vector(31 downto 0);
signal mb_wen     : std_logic;
signal mb_ffull   : std_logic;
signal mb_afull   : std_logic;
                 
signal mb_drd     : std_logic_vector(31 downto 0);
signal mb_rd_req  : std_logic;
signal mb_rd_ack  : std_logic;
signal mb_empty   : std_logic;

signal flash_cmd_write  : std_logic;
signal flash_cmd_read   : std_logic;
signal flash_cmd_erase  : std_logic;
signal flash_addr : std_logic_vector(25 downto 0);
signal flash_cmd_set : std_logic;
signal next_flash_addr : std_logic_vector(25 downto 0);
signal flash_ren  : std_logic;
signal flash_wen  : std_logic;
signal flash_init : std_logic;
signal flash_erase : std_logic;
signal flash_dwr  : std_logic_vector(31 downto 0);
signal psram_sel  : std_logic;
signal flash_state : std_logic_vector(7 downto 0);
signal flash_busy : std_logic;
signal flash_rdy  : std_logic;
-- 
signal if1stat    : std_logic_vector(7 downto 0);
signal if2stat    : std_logic_vector(7 downto 0);
signal if1boot_data : std_logic_vector(31 downto 0);
signal if1boot_wen  : std_logic;
signal if1boot_prog : std_logic;
signal if1boot_rdy  : std_logic;        
signal if2boot_data : std_logic_vector(31 downto 0);
signal if2boot_wen  : std_logic;
signal if2boot_prog : std_logic;
signal if2boot_rdy  : std_logic;

begin

   -- Led
   CLED(3) <= led_cntr(led_cntr'high); -- Blink
   CLED(2) <= rxdcm_locked;            -- Should not shine
   CLED(1) <= XRHSH(11);               -- Should not shine 
   CLED(0) <= RESET_N;                 -- Should not shine
   --CLED <= config_led;
   
   -- Reset V5 after boot
   V5_RST: process(sysclk)
   begin
      if sysclk'event and sysclk = '1' then

         if (boot_done = '1') then
            rst_cntr  <= (others => '0');
         elsif (rst_cntr(rst_cntr'high) = '0') then
            rst_cntr  <= rst_cntr + 1;
         end if;

         XRHSH(10) <= PCIRST_N and rst_cntr(rst_cntr'high);

      end if;
   end process;

   V5_BOOT: entity work.fpga_config
   port map ( 
      -- Oscilator (U17)
      CCLK          => CCLK,
      CCLK_O        => sysclk,
      -- Reset (BT1)
      RESET_N       => RESET_N,
      -- Led
      CLED          => open, --CLED,
      START         => sw_reconfig,
      START_ADDRESS => cfg_addr,
      FLASH_SEL     => cfg_flash_sel,
      BOOT_DONE     => boot_done,
      BOOT_TIMEOUT  => boot_timeout,
      -- Virtex 5
      -- Config
      XRCCLK      => XRCCLK,
      XDONE       => XDONE,
      XPROGRAM_N  => XPROGRAM_N,
      XM0         => XM0,
      XRRDWR_N    => XRRDWR_N,
      XRDIN       => XRDIN,
      XRCS_N      => xrcs_n_boot,
      XRDOUT      => XRDOUT,
      XINIT_N     => XINIT_N,
      -- 
      XRD         => xrd_boot,
      -- PSRAM & Flash (U13 & U14)
      FA          => fa_boot,
      FD          => FD,
      FWE_N       => fwe_n_boot,
      FCSFLASH_N  => fcsflash_n_boot,
      FCSRAM_N    => fcsram_n_boot,
      FOE_N       => foe_n_boot,
      FBYTE_N     => fbyte_n_boot,
      FRY         => FRY,
      FLB_N       => flb_n_boot,
      FUB_N       => fub_n_boot,
      FZZ_N       => fzz_n_boot
   );
   
   XRD     <= xrd_boot when xrcs_n_boot = '0' else (others => 'Z');
   XRCS_N  <= xrcs_n_boot;
   
   PCIEN   <= '1';
   
   cs_boot <= '1' when ((fcsflash_n_boot = '0') or (fcsram_n_boot = '0')) else '0';
   --cs_boot <= '0';
   
   FA         <= fa_boot         when (cs_boot = '1') else fa_mb;
   FWE_N      <= fwe_n_boot      when (cs_boot = '1') else fwe_n_mb;
   FCSFLASH_N <= fcsflash_n_boot when (cs_boot = '1') else fcsflash_n_mb;
   FCSRAM_N   <= fcsram_n_boot   when (cs_boot = '1') else fcsram_n_mb;
   FOE_N      <= foe_n_boot      when (cs_boot = '1') else foe_n_mb;
   FBYTE_N    <= fbyte_n_boot    when (cs_boot = '1') else fbyte_n_mb;
   FLB_N      <= flb_n_boot      when (cs_boot = '1') else flb_n_mb;
   FUB_N      <= fub_n_boot      when (cs_boot = '1') else fub_n_mb;
   FZZ_N      <= fzz_n_boot      when (cs_boot = '1') else fzz_n_mb;
   
   -- Data tristate buffers
   GEN_FD_ZBUF: for i in 0 to FD'high generate
      FD(i) <= fd_mb(i) when ((mb_fd_oen = '1') and (cs_boot = '0')) else 'Z';
   end generate;
                              
   -- Global reset (including IB)
   reset   <= (not RESET_N) or (not PCIRST_N) or (not XRHSH(11)) or (not rxdcm_locked); -- resets are active low
   rxreset <= (not RESET_N) or (not PCIRST_N) or (not XRHSH(11));
     
--    flb_n_mb      <= '1';
--    fub_n_mb      <= '1';
        
   IB_SP_TX: entity work.ib_tx8
   generic map (TXCLK_PHASE_REV => true)
   port map (
      CLK            => ib_clk,
      RESET          => reset,
      -- RX interface
      TX_DATA        => ib.up.data,
      TX_SOP_N       => ib.up.sop_n,
      TX_EOP_N       => ib.up.eop_n,
      TX_SRC_RDY_N   => ib.up.src_rdy_n,
      TX_DST_RDY_N   => ib.up.dst_rdy_n,
      -- TX interface
      TX_PAD         => XRHSH(8 downto 1),
      TX_RDY_N_PAD   => XRHSH(9)
   );

   IB_SP_RX: entity work.ib_rx8_dcm
   port map (
      CLK            => ib_clk,
      RXCLK          => ib_clk,
      RESET          => reset,
      DCM_RESET      => rxreset,
      DCM_LOCKED     => rxdcm_locked,
      -- RX interface
      RX_DATA        => ib.down.data,
      RX_SOP_N       => ib.down.sop_n,
      RX_EOP_N       => ib.down.eop_n,
      RX_SRC_RDY_N   => ib.down.src_rdy_n,
      RX_DST_RDY_N   => ib.down.dst_rdy_n,
      -- TX interface
      RX_PAD         => XRD(7 downto 0),
      RX_RDY_N_PAD   => XRHSH(0),
      DEBUG          => rxdebug
   );
   
-- -------------------------------------------------------------------------
-- Internal bus endpoint
-- -------------------------------------------------------------------------
IB_ENDPOINT0: entity work.IB_ENDPOINT_TOP
generic map (
   LIMIT               => X"FFFFFFFF",
   INPUT_BUFFER_SIZE   => 0,    -- 
   OUTPUT_BUFFER_SIZE  => 0,    -- 
   READ_REORDER_BUFFER => false, -- 
   STRICT_EN           => false  -- 
)
port map (
   -- Common Interface
   IB_CLK       => ib_clk,
   IB_RESET     => reset,
   -- Internal Bus Interface
   INTERNAL_BUS => ib,
   -- Write Interface
   WR_ADDR      => addr_wr,
   WR_DATA      => dwr,
   WR_BE        => dwr_be,
   WR_REQ       => wen,
   WR_RDY       => wr_rdy,
   WR_LENGTH    => open,
   WR_SOF       => open,
   WR_EOF       => open,
   -- Read Interface
   RD_ADDR      => addr_rd,
   RD_BE        => open,
   RD_REQ       => drd_rd,
   RD_ARDY      => drd_xfer,
   RD_SOF_IN    => open,
   RD_EOF_IN    => open,
   -- Output    
   RD_DATA      => drd,
   RD_SRC_RDY   => drd_vld,
   RD_DST_RDY   => drd_rdy -- out
);

-- Software system control
SYSTEM_CONTROL: entity work.sysctrl_cv2 
   generic map (
      REVISION   => REVISION,
      BUILD_TIME => BUILD_TIME
   )
   port map (
      RESET      => reset,
      ICS_CLK    => ib_clk,
      CCLK       => sysclk,
      SW_RESET   => sw_reset,
      -- Write port
      DWR        => dwr,
      DWR_BE     => dwr_be,
      WEN        => wen,
      WR_ADDR    => addr_wr(17 downto 0),
      WR_RDY     => wr_rdy,
      -- Read port
      DRD        => drd,
      DRD_VLD    => drd_vld,
      RD_ARDY    => drd_xfer,
      DRD_RDY    => drd_rdy,
      RD_ADDR    => addr_rd(17 downto 0),
      RD_REQ     => drd_rd,
      -- MicroBlaze data/command FIFO interface
      MB_CMD     => mb_cmd,
      MB_CMD_ACK => mb_cmd_ack,
      MB_DWR     => mb_dwr,
      MB_WEN     => mb_wen,
      --
      MB_DRD     => mb_drd,
      MB_RD_REQ  => mb_rd_req,
      MB_RD_ACK  => mb_rd_ack,
      MB_BUSY    => flash_busy,
      MB_DRDY    => flash_rdy,
      -- IFC1 boot data
      IF1BOOT_DATA => if1boot_data,
      IF1BOOT_WEN  => if1boot_wen,
      IF1BOOT_PROG => if1boot_prog,
      IF1BOOT_RDY  => if1boot_rdy,
      -- IFC2 boot data
      IF2BOOT_DATA => if2boot_data,
      IF2BOOT_WEN  => if2boot_wen, 
      IF2BOOT_PROG => if2boot_prog,
      IF2BOOT_RDY  => if2boot_rdy, 
      -- System control ports
      RECONFIG   => sw_reconfig,
      RECFG_REV  => sw_revsel,
      RECFG_ERR  => boot_timeout,
      -- Crypto chip I2C bus 
      CSDA       => CSDA,
      CSCL       => CSCL,
      -- Interface I2C
      IF1SDA     => IF1SDA,
      IF1SCLK    => IF1SCLK,
      IF2SDA     => IF2SDA,
      IF2SCLK    => IF2SCLK,
      -- PLL control
      PLLM       => PLCLK(5 downto 0),
      PLLN       => PLCLK(10 downto 9),
      PLLOAD0_N  => PLLOAD_N(0),
      PLLOAD1_N  => PLLOAD_N(1),
      -- Other status signals
      IF1STAT    => if1stat,
      IF2STAT    => if2stat,
      SWITCH     => SWITCH_N
   );
   
   PLCLK(8 downto 6) <= (others => '0');
   
   if1stat <= "00000" & IF1DONE & IF1JTAGEN_N & IF1EN_N;
   if2stat <= "00000" & IF2DONE & IF2JTAGEN_N & IF2EN_N;
   
   soft_reset <= sw_reset or reset;
   
   cfg_addr      <= sw_revsel(3 downto 0) & "00" & X"00000"; -- 25 downto 22: block select
   cfg_flash_sel <= sw_revsel(4) or (not XDONE);
   
--    mb_rd_ack  <= not mb_empty;

-- Zmeny: BR space, offset 0x100
-- Flash select - bit 27. in the commnad register, '0' = PSRAM, '1' = FLASH
-- 

   ADDRESS_REG: process(ib_clk)
   begin
      if ib_clk'event and ib_clk = '1' then
         flash_ren   <= '0';
         flash_wen   <= '0';
         flash_init  <= '0';
         flash_erase <= '0';
         mb_cmd_ack  <= '0';
         if (soft_reset = '1') then
            psram_sel       <= '0';
            flash_cmd_write <= '0';
            flash_cmd_read  <= '0';
            flash_cmd_erase <= '0';
         else
            if (flash_cmd_set = '1') then
               flash_ren   <= flash_cmd_read;
               flash_erase <= flash_cmd_erase;
            end if;
            if (flash_busy = '0') then
               flash_cmd_set <= '0';
            end if;
            if (mb_cmd = '1') and (mb_wen = '1') then  -- Write to the command register
               mb_cmd_ack      <= '1';
               psram_sel       <= not mb_dwr(27);
               flash_cmd_write <= '0';
               flash_cmd_read  <= '0';
               flash_cmd_erase <= '0';
               flash_addr      <= mb_dwr(25 downto 0);
               if (mb_dwr(31 downto 28) = "0000") then -- Read command
                  flash_cmd_read  <= '1';
                  next_flash_addr <= mb_dwr(25 downto 0) + 2;
                  if (flash_busy = '1') then
                     flash_cmd_set <= '1'; -- Wait until FLASH ready
                  else
                     flash_ren <= '1';
                  end if;
               elsif (mb_dwr(31 downto 28) = "0001") then -- Write Command
                  flash_cmd_write <= '1';
                  next_flash_addr <= mb_dwr(25 downto 0);
--               elsif (mb_dwr(31 downto 28) = "0011") then -- Write Buffer Command
--                  flash_cmd_write <= '1';
               elsif (mb_dwr(31 downto 28) = "0100") then -- Sector erase command
                  flash_cmd_erase <= '1';
                  if (flash_busy = '1') then
                     flash_cmd_set <= '1'; -- Wait until FLASH ready
                  else
                     flash_erase <= '1';
                  end if;
               elsif (mb_dwr(31 downto 28) = "1111") then -- INIT (Reset) Command
                  flash_init <= '1';
               end if;
            -- Write to the TX register or read from RX register
            elsif (((mb_cmd = '0') and (mb_wen = '1')) or (mb_rd_req = '1')) and 
                     (flash_rdy = '1') then 
               flash_dwr       <= mb_dwr;
               flash_wen       <= (flash_cmd_write and mb_wen);
               flash_ren       <= (flash_cmd_read and mb_rd_req);
               flash_addr      <= next_flash_addr;
               next_flash_addr <= next_flash_addr + 2;
            end if;
         end if;
      end if;
   end process;
   
   FLASH_CONTROL: entity work.flashctrl 
   port map (
      RESET      => soft_reset,
      CLK        => ib_clk,
      -- 
      INIT       => flash_init,
      ERASE      => flash_erase,
      WRITE      => flash_cmd_write,
      ADDR       => flash_addr,
      DRD        => mb_drd,
      DRD_VAL    => mb_rd_ack,
      DWR        => flash_dwr,
      WEN        => flash_wen,
      REN        => flash_ren,
      PSRAM_SEL  => psram_sel,
      RDY        => flash_rdy, -- Ready for new data
      BUSY       => flash_busy,
      -- FLASH interface --
      FA         => fa_mb,
      FD_I       => FD,
      FD_O       => fd_mb,
      FD_OE      => mb_fd_oen,
      FWE_N      => fwe_n_mb,
      FCSFLASH_N => fcsflash_n_mb,
      FCSRAM_N   => fcsram_n_mb,
      FOE_N      => foe_n_mb,
      FBYTE_N    => fbyte_n_mb,
      FRY        => FRY,
      FLB_N      => flb_n_mb,
      FUB_N      => fub_n_mb,
      FZZ_N      => fzz_n_mb,
      --
      STATE      => flash_state
   );

--    IFCCCLK_GEN: entity work.clkman_sp3 
--    port map ( 
--       CLKIN_IN   => cclk,
--       RST_IN     => reset,
--       CLKDV_OUT  => cclk_ifc,
--       CLK0_OUT   => open,
--       LOCKED_OUT => clkman_locked
--    );
   cclk_ifc <= cclk;
   clkman_locked <= '1';

   ifcboot_rst <= reset or (not clkman_locked);
   
   -- IFC1 FPGA boot
   IF1_BOOT: entity work.ifcboot 
   port map (
      RESET     => ifcboot_rst,
      ICS_CLK   => ib_clk,
      CCLK      => cclk_ifc,
      --
      BOOT_DATA => if1boot_data,
      BOOT_WEN  => if1boot_wen,
      BOOT_PROG => if1boot_prog,
      BOOT_RDY  => if1boot_rdy,
      --
      PROG_N   => IF1PROG_N,
      INIT_N   => IF1INIT_N,
      D_O      => IF1DIN,
      CFG_N    => IF1CFG_N,
      CCLK_O   => IF1CCLK,
      DONE     => IF1DONE
   );
   
   -- IFC1 FPGA boot
   IF2_BOOT: entity work.ifcboot 
   port map (
      RESET     => ifcboot_rst,
      ICS_CLK   => ib_clk,
      CCLK      => cclk_ifc,
      --
      BOOT_DATA => if2boot_data,
      BOOT_WEN  => if2boot_wen,
      BOOT_PROG => if2boot_prog,
      BOOT_RDY  => if2boot_rdy,
      --
      PROG_N   => IF2PROG_N,
      INIT_N   => IF2INIT_N,
      D_O      => IF2DIN,
      CFG_N    => IF2CFG_N,
      CCLK_O   => IF2CCLK,
      DONE     => IF2DONE
   );
   
--    -- MicroBlaze system control component
--    INST_TEST_TOP: test_top 
--    PORT MAP (
--       sys_clk_pin                                 => sysclk,
--       CLED_pin                                    => CLED,
--       fpga_0_RS232_TX_pin                         => open,
--       fpga_0_RS232_RX_pin                         => '1',   
--       fpga_0_Generic_External_Memory_Mem_A_pin    => fa_mb,
--       fpga_0_Generic_External_Memory_Mem_BEN_pin  => open,
--       fpga_0_Generic_External_Memory_Mem_WEN_pin  => fwe_n_mb,
--       fpga_0_Generic_External_Memory_Mem_OEN_pin  => foe_n_mb,
--       fpga_0_Generic_External_Memory_Mem_CEN_pin  => mb_mem_cen,
--       Generic_External_Memory_Mem_DQ_I_pin        => FD,
--       Generic_External_Memory_Mem_DQ_T_pin(0)     => mb_fd_oen,
--       Generic_External_Memory_Mem_DQ_O_pin        => fd_mb,
--       FBYTE_N                                     => fbyte_n_mb,
--       FZZ_N                                       => fzz_n_mb,
--       FRY                                         => FRY,
--       -- FIFO interface
--       ifc_bridge_0_ifc_fifo_clk_pin               => ib_clk,
--       ifc_bridge_0_ifc_fifo_write_data_pin        => mb_dwr,
--       ifc_bridge_0_ifc_fifo_wen_pin               => mb_wen,
--       ifc_bridge_0_ifc_fifo_start_transaction_pin => mb_cmd,
--       ifc_bridge_0_ifc_fifo_ren_pin               => mb_rd_req,   
--       ifc_bridge_0_ifc_fifo_read_data_pin         => mb_drd,
--       ifc_bridge_0_ifc_fifo_empty_pin             => mb_empty,
--       ifc_bridge_0_ifc_fifo_almost_empty_pin      => open,
--       ifc_bridge_0_ifc_fifo_full_pin              => mb_ffull,
--       ifc_bridge_0_ifc_fifo_almost_full_pin       => mb_afull
--    );
   
--    fcsflash_n_mb <= mb_mem_cen(0);
--    fcsram_n_mb   <= mb_mem_cen(1);
 
   LED_CNTR_PROC: process(CCLK)
   begin
     if ib_clk'event and ib_clk = '1' then
        led_cntr <= led_cntr + 1;
     end if;
   end process;
   
-- -------------------------------------------------------------------------
-- Debug - Chipscope
-- -------------------------------------------------------------------------

--   ICON_U: sp3_icon2
--   port map (
--      control0    => control0,
--      control1    => control1
--   );

--   RX_ILA : sp3_ll64_ila 
--   port map (
--      control     => control0,
--      clk         => ib_clk,
--      trig0       => rx_trig0, 
--      trig1       => rx_trig1
--   );
--     
--   TX_ILA : sp3_ll64_ila 
--   port map (
--      control     => control1,
--      clk         => ib_clk,
--      trig0       => tx_trig0, 
--      trig1       => tx_trig1
--   );    
--   
-- -- rx_trig0 <= ib.down.data(63 downto 0);
-- -- rx_trig1 <= "0000" & ib.down.dst_rdy_n & ib.down.src_rdy_n & ib.down.eop_n & ib.down.sop_n;

-- rx_trig0 <= FD(7 downto 0) & fa_mb(23 downto 0) & flash_state & mb_drd(23 downto 0);
-- rx_trig1 <= "0" & fcsram_n_mb & mb_cmd & mb_wen & FRY & fwe_n_mb & foe_n_mb & fcsflash_n_mb;

-- tx_trig0 <= ib.up.data;
-- tx_trig1 <= "0000" & ib.up.dst_rdy_n & ib.up.src_rdy_n & ib.up.eop_n & ib.up.sop_n;

end behavioral;