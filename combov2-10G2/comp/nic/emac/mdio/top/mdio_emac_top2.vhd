-- mdio_emac_top2.vhd: Envelope for 2 mdio_emac components
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

entity mdio_emac_top2 is
    port(
    
      -- ----------------------------------------------------------------------
      --                           Common signals
      -- ----------------------------------------------------------------------
      
      -- Input clock (max. fequency = 125 MHz because of HOSTCLK)
      CLK            : in std_logic;
      -- Reset signal
      RESET          : in std_logic;
      
      -- Controls accessing Configuration registers (1) od PCS/PMA sublayer
      -- registers (0)
      CONFREGS             : in std_logic;
      -- MI32_ADDR(9 downto 0) - possible address of Configuration register
      ADDR                 : in std_logic_vector(9 downto 0);
      
      -- ----------------------------------------------------------------------
      --                            MDIO EMAC 0
      -- ----------------------------------------------------------------------
      -- EMAC block 0
    
      ---------- I2C and MDIO controller interface ----------
      EMAC0WE              : in std_logic;
      EMAC0RE              : in std_logic;
      EMAC0FRAME           : in std_logic_vector(31 downto 0);
      EMAC0RD_DATA         : out std_logic_vector(31 downto 0);
      EMAC0BUSY            : out std_logic;
      EMAC0EMAC1           : in std_logic;
    
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
      
      ---------- I2C and MDIO controller interface ----------
      EMAC1WE              : in std_logic;
      EMAC1RE              : in std_logic;
      EMAC1FRAME           : in std_logic_vector(31 downto 0);
      EMAC1RD_DATA         : out std_logic_vector(31 downto 0);
      EMAC1BUSY            : out std_logic;
      EMAC1EMAC1           : in std_logic;
      
      ---------- Host Bus interface ----------
      EMAC1HOSTCLK         : out std_logic;
      EMAC1HOSTOPCODE      : out std_logic_vector(1 downto 0);
      EMAC1HOSTADDR        : out std_logic_vector(9 downto 0);
      EMAC1HOSTWRDATA      : out std_logic_vector(31 downto 0);
      EMAC1HOSTRDDATA      : in std_logic_vector(31 downto 0);
      EMAC1HOSTMIIMSEL     : out std_logic;
      EMAC1HOSTEMAC1SEL    : out std_logic;
      EMAC1HOSTREQ         : out std_logic;
      EMAC1HOSTMIIMRDY     : in std_logic
   );
end mdio_emac_top2;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

architecture mdio_emac_top2_arch of mdio_emac_top2 is

begin

   -- -------------------------------------------------------------------------
   --                              MDIO EMAC 0
   -- -------------------------------------------------------------------------
   
   mdio_emac0_i: entity work.mdio_emac
      port map(
         ---------- Clock signal ----------
         CLK            => CLK,
         RESET          => RESET,
         
         ---------- I2C and MDIO controller interface ----------
         WE             => EMAC0WE,
         RE             => EMAC0RE,
         FRAME          => EMAC0FRAME,
         RD_DATA        => EMAC0RD_DATA,
         BUSY           => EMAC0BUSY,
         EMAC1          => EMAC0EMAC1,
         CONFREGS       => CONFREGS,
         ADDR           => ADDR,
      
         ---------- Host Bus interface ----------
         HOSTCLK        => EMAC0HOSTCLK,
         HOSTOPCODE     => EMAC0HOSTOPCODE,
         HOSTADDR       => EMAC0HOSTADDR,
         HOSTWRDATA     => EMAC0HOSTWRDATA,
         HOSTRDDATA     => EMAC0HOSTRDDATA,
         HOSTMIIMSEL    => EMAC0HOSTMIIMSEL,
         HOSTEMAC1SEL   => EMAC0HOSTEMAC1SEL,
         HOSTREQ        => EMAC0HOSTREQ,
         HOSTMIIMRDY    => EMAC0HOSTMIIMRDY
      );

   -- -------------------------------------------------------------------------
   --                              MDIO EMAC 1
   -- -------------------------------------------------------------------------

   mdio_emac1_i: entity work.mdio_emac
      port map(
         ---------- Clock signal ----------
         CLK            => CLK,
         RESET          => RESET,

         ---------- I2C and MDIO controller interface ----------
         WE             => EMAC1WE,
         RE             => EMAC1RE,
         FRAME          => EMAC1FRAME,
         RD_DATA        => EMAC1RD_DATA,
         BUSY           => EMAC1BUSY,
         EMAC1          => EMAC1EMAC1,
         CONFREGS       => CONFREGS,
         ADDR           => ADDR,

         ---------- Host Bus interface ----------
         HOSTCLK        => EMAC1HOSTCLK,
         HOSTOPCODE     => EMAC1HOSTOPCODE,
         HOSTADDR       => EMAC1HOSTADDR,
         HOSTWRDATA     => EMAC1HOSTWRDATA,
         HOSTRDDATA     => EMAC1HOSTRDDATA,
         HOSTMIIMSEL    => EMAC1HOSTMIIMSEL,
         HOSTEMAC1SEL   => EMAC1HOSTEMAC1SEL,
         HOSTREQ        => EMAC1HOSTREQ,
         HOSTMIIMRDY    => EMAC1HOSTMIIMRDY
      );

end mdio_emac_top2_arch;
