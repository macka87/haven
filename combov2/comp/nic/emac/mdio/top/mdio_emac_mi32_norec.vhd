-- mdio_emac_mi32_norec.vhd: Envelope with 2 mdio_emac components and mi32
--                           interface without record
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

entity mdio_emac_mi32_norec is
    port(
    
      -- ----------------------------------------------------------------------
      --                           Common signals
      -- ----------------------------------------------------------------------
      
      -- Input clock (max. fequency = 125 MHz because of HOSTCLK)
      CLK            : in std_logic;
      -- Reset signal
      RESET          : in std_logic;
      
      -- ----------------------------------------------------------------------
      --                            MDIO EMAC 0
      -- ----------------------------------------------------------------------
      -- EMAC block 0
    
      ---------- Host Bus interface ----------
      EMAC0HOSTCLK         : out std_logic;
      EMAC0HOSTOPCODE      : out std_logic_vector(1 downto 0);
      EMAC0HOSTADDR        : out std_logic_vector(9 downto 0);
      EMAC0HOSTWRDATA      : out std_logic_vector(31 downto 0);
      EMAC0HOSTRDDATA      : in std_logic_vector(31 downto 0);
      EMAC0HOSTMIIMSEL     : out std_logic;
      EMAC0HOSTEMAC1SEL    : out std_logic;
      EMAC0HOSTREQ         : out std_logic;
      EMAC0HOSTMIIMRDY     : in std_logic;
      
      -- ----------------------------------------------------------------------
      --                            MDIO EMAC 1
      -- ----------------------------------------------------------------------
      -- EMAC block 1
      
      ---------- Host Bus interface ----------
      EMAC1HOSTCLK         : out std_logic;
      EMAC1HOSTOPCODE      : out std_logic_vector(1 downto 0);
      EMAC1HOSTADDR        : out std_logic_vector(9 downto 0);
      EMAC1HOSTWRDATA      : out std_logic_vector(31 downto 0);
      EMAC1HOSTRDDATA      : in std_logic_vector(31 downto 0);
      EMAC1HOSTMIIMSEL     : out std_logic;
      EMAC1HOSTEMAC1SEL    : out std_logic;
      EMAC1HOSTREQ         : out std_logic;
      EMAC1HOSTMIIMRDY     : in std_logic;
      
      -- ----------------------------------------------------------------------
      --                            MI32 interface
      -- ----------------------------------------------------------------------
      
      MI32_DWR          :  in std_logic_vector(31 downto 0); -- Input Data
      MI32_ADDR         :  in std_logic_vector(31 downto 0); -- Address
      MI32_RD           :  in std_logic;                     -- Read Request
      MI32_WR           :  in std_logic;                     -- Write Request
      MI32_BE           :  in std_logic_vector(3  downto 0); -- Byte Enable
      MI32_DRD          : out std_logic_vector(31 downto 0); -- Output Data
      MI32_ARDY         : out std_logic;                     -- Address Ready
      MI32_DRDY         : out std_logic                      -- Data Ready
   );
end mdio_emac_mi32_norec;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

architecture mdio_emac_mi32_norec_arch of mdio_emac_mi32_norec is

   -- accessing EMAC configuration registers (1) or PCS/PMA sublayer registers
   -- (0)
   signal conf_regs        : std_logic;
   -- delayed signal MI32_RD of MI32 interface
   signal mi32_rd_delayed  : std_logic;
   -- appropriate data read signal (direct or delayed for 1 CLK period)
   signal data_rd          : std_logic;

   signal emac0_cs         : std_logic;
   signal emac0_we         : std_logic;
   signal emac0_re         : std_logic;
   signal emac0emac1       : std_logic;
   
   signal emac1_cs         : std_logic;
   signal emac1_we         : std_logic;
   signal emac1_re         : std_logic;
   signal emac1emac1       : std_logic;

   signal emac0rd_data     : std_logic_vector(31 downto 0);
   signal emac0busy        : std_logic;
   
   signal emac1rd_data     : std_logic_vector(31 downto 0);
   signal emac1busy        : std_logic;

   signal mx_output_data   : std_logic_vector(31 downto 0);

begin

   -- mi32_rd_delayed register
   mi32_rd_delayed_p : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         mi32_rd_delayed <= MI32_RD;
      end if;
   end process mi32_rd_delayed_p;

   -- -------------------------------------------------------------------------
   --                              Address decoder
   -- -------------------------------------------------------------------------

   -- Choose appropriate data read signal (direct when mdio transaction,
   -- delayed when conf. registers transaction)
   data_rd  <= mi32_rd_delayed when (conf_regs = '1') else
               MI32_RD;

   -- Set MI_32 output signals
   MI32_ARDY   <= data_rd or MI32_WR;
   MI32_DRDY   <= data_rd;
   MI32_DRD    <= mx_output_data;

   -- Set write enable signals
   emac0_we    <= emac0_cs and MI32_WR;
   emac1_we    <= emac1_cs and MI32_WR;
   
   -- Set read enable signals
   emac0_re    <= emac0_cs and MI32_RD;
   emac1_re    <= emac1_cs and MI32_RD;

   -- Set chip select signals and EMAC1 signals
   cs_p : process (MI32_ADDR(11 downto 2))
   begin
      emac0_cs    <= '0';
      emac1_cs    <= '0';
      emac0emac1  <= '0';
      emac1emac1  <= '0';

      if (MI32_ADDR(9) = '1') then
         -- accessing Configuration registers
         conf_regs <= '1';
         case (MI32_ADDR(11 downto 10)) is
            when "00" => emac0_cs <= '1';
            when "01" => emac0_cs <= '1';
                         emac0emac1 <= '1';
            when "10" => emac1_cs <= '1';
            when "11" => emac1_cs <= '1';
                         emac1emac1 <= '1';
            when others => null;
         end case;
      else
         -- accessing PCS/PMA sublayer registers
         conf_regs <= '0';
         case (MI32_ADDR(5 downto 2)) is
            when "0000" | "0001" => emac0_cs    <= '1';
            when "0100" | "0101" => emac0_cs    <= '1';
                                    emac0emac1  <= '1';
            when "1000" | "1001" => emac1_cs    <= '1';
            when "1100" | "1101" => emac1_cs    <= '1';
                                    emac1emac1  <= '1';
            when others => null;
         end case;
      end if;
   end process cs_p;

   -- Output data selection
   mx_output_data_p : process (MI32_ADDR(11 downto 2), emac0rd_data, emac0busy,
                               emac1rd_data, emac1busy)
   begin
      if (MI32_ADDR(9) = '1') then
         case (MI32_ADDR(11 downto 10)) is
            when "00" | "01" => mx_output_data <= emac0rd_data;
            when "10" | "11" => mx_output_data <= emac1rd_data;
            when others => mx_output_data <= (others => '0');
         end case;
      else
         case (MI32_ADDR(5 downto 2)) is
            when "0010" | "0110" => -- EMAC0 RD_DATA
               mx_output_data <= emac0rd_data;
            when "0011" | "0111" => -- EMAC0 BUSY
               mx_output_data <= X"0000000" & "000" & emac0busy;
            when "1010" | "1110" => -- EMAC1 RD_DATA
               mx_output_data <= emac1rd_data;
            when "1011" | "1111" => -- EMAC1 BUSY
               mx_output_data <= X"0000000" & "000" & emac1busy;
            when others => mx_output_data <= (others => '0');
         end case;
      end if;
   end process mx_output_data_p;

   -- -------------------------------------------------------------------------
   --                              mdio_emac_top2
   -- -------------------------------------------------------------------------
   
   mdio_emac_i : entity work.mdio_emac_top2
      port map(
         ---------- Common signals ----------
         -- Input clock (max. fequency = 125 MHz because of HOSTCLK)
         CLK                  => CLK,
         RESET                => RESET,
         
         CONFREGS             => conf_regs,
         ADDR                 => MI32_ADDR(9 downto 0),

         ---------- MDIO EMAC 0 ----------
         -- I2C and MDIO controller interface
         EMAC0WE              => emac0_we,
         EMAC0RE              => emac0_re,
         EMAC0FRAME           => MI32_DWR,
         EMAC0RD_DATA         => emac0rd_data,
         EMAC0BUSY            => emac0busy,
         EMAC0EMAC1           => emac0emac1,

         -- Host Bus interface
         EMAC0HOSTCLK         => EMAC0HOSTCLK,
         EMAC0HOSTOPCODE      => EMAC0HOSTOPCODE,
         EMAC0HOSTADDR        => EMAC0HOSTADDR,
         EMAC0HOSTWRDATA      => EMAC0HOSTWRDATA,
         EMAC0HOSTRDDATA      => EMAC0HOSTRDDATA,
         EMAC0HOSTMIIMSEL     => EMAC0HOSTMIIMSEL,
         EMAC0HOSTEMAC1SEL    => EMAC0HOSTEMAC1SEL,
         EMAC0HOSTREQ         => EMAC0HOSTREQ,
         EMAC0HOSTMIIMRDY     => EMAC0HOSTMIIMRDY,
         
         ---------- MDIO EMAC 1 ----------
         -- I2C and MDIO controller interface
         EMAC1WE              => emac1_we,
         EMAC1RE              => emac1_re,
         EMAC1FRAME           => MI32_DWR,
         EMAC1RD_DATA         => emac1rd_data,
         EMAC1BUSY            => emac1busy,
         EMAC1EMAC1           => emac1emac1,

         -- Host Bus interface
         EMAC1HOSTCLK         => EMAC1HOSTCLK,
         EMAC1HOSTOPCODE      => EMAC1HOSTOPCODE,
         EMAC1HOSTADDR        => EMAC1HOSTADDR,
         EMAC1HOSTWRDATA      => EMAC1HOSTWRDATA,
         EMAC1HOSTRDDATA      => EMAC1HOSTRDDATA,
         EMAC1HOSTMIIMSEL     => EMAC1HOSTMIIMSEL,
         EMAC1HOSTEMAC1SEL    => EMAC1HOSTEMAC1SEL,
         EMAC1HOSTREQ         => EMAC1HOSTREQ,
         EMAC1HOSTMIIMRDY     => EMAC1HOSTMIIMRDY
      );

end mdio_emac_mi32_norec_arch;
