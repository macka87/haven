-- mdio_emac.vhd: Connection from implemented I2C and MDIO controller to the
--                EMAC Core Host Bus
--
-- Copyright (C) 2009 CESNET
-- Author(s): Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity mdio_emac is
    port(
      ---------- Common signals ----------
      -- Input clock (max. fequency = 125 MHz because of HOSTCLK)
      CLK            : in std_logic;
      -- Reset signal
      RESET          : in std_logic;
    
      ---------- I2C and MDIO controller interface ----------
      -- write enable = start of MDIO transaction
      WE             : in std_logic;
      -- read enable for reading Configuration register
      RE             : in std_logic;
      -- MDIO frame to be transmitted
      FRAME          : in std_logic_vector(31 downto 0);
      -- read data (after MDIO read operation)
      RD_DATA        : out std_logic_vector(31 downto 0);
      -- indication of activity on MDIO bus
      BUSY           : out std_logic;
      -- selection of EMAC within EMAC block (1 means EMAC1)
      EMAC1          : in std_logic;
      -- Controls accessing Configuration registers (1) od PCS/PMA sublayer
      -- registers (0)
      CONFREGS       : in std_logic;
      -- address of configuration register
      ADDR           : in std_logic_vector(9 downto 0);
      
      ---------- Host Bus interface ----------
      -- clock signal for Host Bus (also used for deriving MDC signal)
      HOSTCLK        : out std_logic;
      -- code of MDIO transaction
      HOSTOPCODE     : out std_logic_vector(1 downto 0);
      -- address of device and its register
      HOSTADDR       : out std_logic_vector(9 downto 0);
      -- data to be written (for MDIO transactions only bits 15 downto 0 are considered)
      HOSTWRDATA     : out std_logic_vector(31 downto 0);
      -- read data (for MDIO transactions only bits 15 downto 0 are considered)
      HOSTRDDATA     : in std_logic_vector(31 downto 0);
      -- selection of using MDIO bus ('1' means use MDIO Bus)
      HOSTMIIMSEL    : out std_logic;
      -- selection of EMAC within EMAC block as a communication partner('1' means select EMAC1)
      HOSTEMAC1SEL   : out std_logic;
      -- request for transaction on MDIO bus
      HOSTREQ        : out std_logic;
      -- ready for next communication over MDIO bus
      HOSTMIIMRDY    : in std_logic
   );
end mdio_emac;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

architecture mdio_emac_arch of mdio_emac is

   ---------- Constants declaration ----------
   constant mcr_addr    : std_logic_vector(9 downto 0) := "1101000000";
   constant clkdiv_value: std_logic_vector(31 downto 0) := X"000000" & "01011001";
   constant init_delay  : integer := 10;

   -- guessed value: restart initialization once after this time
   constant long_delay  : std_logic_vector(15 downto 0) := X"8000"; 

   ---------- Signals declaration ----------
   -- Initialization registers
   signal init          : std_logic;
   signal init1         : std_logic;
   -- Initialization delay register (triggers write of CLOCK_DIVIDE into Management Configuration Register)
   signal init_reg      : std_logic_vector(init_delay downto 0);
   -- Counter to delay initialization for longer time
   signal cnt_init_delay: std_logic_vector(15 downto 0);
   -- Restart initialization after longer time
   signal init_restart  : std_logic;
   
   -- address register for accessing Configuration registers
   signal addr_reg      : std_logic_vector(9 downto 0);
   
   -- Controller -> Host Bus registers signal
   signal we_reg        : std_logic;
   signal re_reg        : std_logic;
   signal frame_reg     : std_logic_vector(31 downto 0);
   signal emac1_reg     : std_logic;
   signal confregs_reg  : std_logic;
   
   -- Host Bus -> controller registers signal
   signal busy_reg      : std_logic;
   signal rd_data_reg   : std_logic_vector(31 downto 0);

begin

   -- propagation of clock signal
   HOSTCLK <= CLK;

   -- -------------------------------------------------------------------------
   --                      Controller -> Host Bus registers
   -- -------------------------------------------------------------------------
   
   -- write enable register
   we_reg_p : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RESET='1') then
            we_reg <= '0';
         else
            we_reg <= WE;
         end if;
      end if;
   end process we_reg_p;
   
   -- read enable register
   re_reg_p : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RESET='1') then
            re_reg <= '0';
         else
            re_reg <= RE;
         end if;
      end if;
   end process re_reg_p;

   -- frame register
   frame_reg_p : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RESET='1') then
            frame_reg <= (others => '0');
         elsif (WE='1') then
            frame_reg <= FRAME;
         end if;
      end if;
   end process frame_reg_p;
   
   -- emac1 register
   emac1_reg_p : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RESET='1') then
            emac1_reg <= '0';
         else
            emac1_reg <= EMAC1;
         end if;
      end if;
   end process emac1_reg_p;
   
   -- confregs register
   confregs_reg_p : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RESET='1') then
            confregs_reg <= '0';
         else
            confregs_reg <= CONFREGS;
         end if;
      end if;
   end process confregs_reg_p;
   
   -- address register
   addr_reg_p : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RESET='1') then
            addr_reg <= (others => '0');
         else
            addr_reg <= ADDR;
         end if;
      end if;
   end process addr_reg_p;

   -- -------------------------------------------------------------------------
   --                     Init signal and delay register
   -- -------------------------------------------------------------------------
   -- create signals which control write of CLOCK_DIVIDE 
   -- into Management configuration registers (EMAC0 and EMAC1)
   init_p : process(init_reg)
   begin
      if ((init_reg(init_delay-1) = '0' and init_reg(init_delay) = '1') or 
          (init_reg(init_delay-3) = '0' and init_reg(init_delay-2) = '1')) then
         init <= '1';
      else
         init <= '0';
      end if;
   end process;

   init1_p : process(init_reg)
   begin
      if (init_reg(init_delay-1) = '0' and init_reg(init_delay) = '1') then
         init1 <= '1';
      else
         init1 <= '0';
      end if;
   end process;

   -- Counter for delayed start of initialization
   cnt_init_delay_p : process(CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RESET = '1') then
            cnt_init_delay <= (others => '0');
         else
            if (cnt_init_delay = long_delay) then
               cnt_init_delay <= cnt_init_delay;
            else
               cnt_init_delay <= cnt_init_delay+1;
            end if;
         end if;
      end if;
   end process;

   -- Trigger for delayed initialization
   init_restart_p : process(cnt_init_delay)
   begin
      if (cnt_init_delay = long_delay-1) then
         init_restart <= '1';
      else
         init_restart <= '0';
      end if;
   end process;

   -- delay register
   init_reg_p : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RESET = '1' or init_restart = '1') then
            init_reg(0) <= '1';
         else
            init_reg(0) <= '0';
         end if;
      end if;
   end process init_reg_p;

   init_gen : for i in 1 to init_delay generate
      init_shift_p : process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1' or init_restart = '1') then
               init_reg(i) <= '1';
            else
               init_reg(i) <= init_reg(i-1);
            end if;
         end if;
      end process;
   end generate;
   
   -- -------------------------------------------------------------------------
   --             Setting of Host Bus signals (start of transaction)
   -- -------------------------------------------------------------------------
   -- when init is active, write CLOCK_DIVIDE on address 0x340, bits 5 downto 0

   init_mux_p : process(init, init1, we_reg, frame_reg, addr_reg, emac1_reg, confregs_reg, re_reg)
   begin

      -- Default values for some output signals to avoid latches
      HOSTOPCODE <= "10";
      HOSTWRDATA <= (others => '0');
   
      if (init = '1') then
         HOSTOPCODE <= "01";
         HOSTADDR <= mcr_addr;
         HOSTWRDATA <= clkdiv_value;
         HOSTMIIMSEL <= '0';
         HOSTREQ <= '0';
         if (init1 = '0') then
            HOSTEMAC1SEL <= '0';
         else
            HOSTEMAC1SEL <= '1';
         end if;
      elsif (confregs_reg = '1') then
         if (we_reg = '1') then
            -- write transaction
            HOSTOPCODE <= "01";
            HOSTWRDATA <= frame_reg;
         elsif (re_reg = '1') then
            -- read transaction
            HOSTOPCODE <= "11";
	 end if;
         HOSTADDR <= addr_reg;
         HOSTMIIMSEL <= '0';
         HOSTREQ <= '0';
         HOSTEMAC1SEL   <= emac1_reg;  -- choose EMAC0 or EMAC1
      else
         if (we_reg = '0') then
            HOSTOPCODE <= "11";
            HOSTADDR <= "1000000000";
         else
            HOSTOPCODE <= frame_reg(3 downto 2);
            HOSTADDR <= frame_reg(8 downto 4) & frame_reg(13 downto 9);
         end if;
         HOSTWRDATA <= X"0000" & frame_reg(31 downto 16);
         HOSTMIIMSEL <= '1';
         HOSTREQ <= we_reg;
         HOSTEMAC1SEL   <= emac1_reg;  -- choose EMAC0 or EMAC1
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                      Host Bus -> Controller registers
   -- -------------------------------------------------------------------------

   -- busy register
   busy_reg_p : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RESET='1') then
            busy_reg <= '0';
         else
            busy_reg <= not HOSTMIIMRDY;
         end if;
      end if;
   end process busy_reg_p;
   
   -- read data register
   rd_data_reg_p : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RESET='1') then
            rd_data_reg <= (others => '0');
         else
            rd_data_reg <= HOSTRDDATA;
         end if;
      end if;
   end process rd_data_reg_p;
   
   -- -------------------------------------------------------------------------
   --               Setting of output controller interface signals
   -- -------------------------------------------------------------------------

   RD_DATA <= rd_data_reg;
   BUSY <= busy_reg;

end mdio_emac_arch;
