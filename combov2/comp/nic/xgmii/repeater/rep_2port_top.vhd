--
-- rep_2port_top.vhd: This component encapsulates rep_2port_cover component
--                    (which contatins repeater), over- and underflow
--                    counters, enable registers for enabling functionality
--                    of repeater. These component are available through
--                    MI32 interface - 2 address decoders and 2 output
--                    multiplexers are used (one for each interface).
--                
--
-- Copyright (C) 2008 CESNET
-- Author(s): Michal Kajan <kajan@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- library with MI32 interface definition
use work.lb_pkg.all;

-- ----------------------------------------------------------------------------
--  Entity declaration: REP_2PORT_TOP
-- ---------------------------------------------------------------------------- 
entity rep_2port_top is
   port (
      -- general signal
      ECLK         : in  std_logic;
      RESET_GLOBAL : in  std_logic;
      RESET_IBUF   : out std_logic;

      -- XGMII Receiver A input
      RXCLKA     : in  std_logic;
      RXDA       : in  std_logic_vector(31 downto 0);
      RXCA       : in  std_logic_vector(3 downto 0);

      -- XGMII Receiver B input
      RXCLKB     : in  std_logic;
      RXDB       : in  std_logic_vector(31 downto 0);
      RXCB       : in  std_logic_vector(3 downto 0);

      -- XGMII Transmitter A output
      TXCLKA     : out std_logic;
      TXDA       : out std_logic_vector(31 downto 0);
      TXCA       : out std_logic_vector(3 downto 0);

      -- XGMII Transmitter B output
      TXCLKB     : out std_logic;
      TXDB       : out std_logic_vector(31 downto 0);
      TXCB       : out std_logic_vector(3 downto 0);

      -- XGMII Receiver A output
      IBUF0_CLK  : out std_logic;
      IBUF0_DATA : out std_logic_vector(63 downto 0);
      IBUF0_CMD  : out std_logic_vector(7 downto 0);

      -- XGMII Receiver B output
      IBUF1_CLK  : out std_logic;
      IBUF1_DATA : out std_logic_vector(63 downto 0);
      IBUF1_CMD  : out std_logic_vector(7 downto 0);

      -- MI32 interface
--      MI32_0     : inout t_mi32;
--      MI32_1     : inout t_mi32;

      MI32_0_DWR  : in  std_logic_vector(31 downto 0);
      MI32_0_ADDR : in  std_logic_vector(31 downto 0);  
      MI32_0_RD   : in  std_logic;
      MI32_0_WR   : in  std_logic;
      MI32_0_BE   : in  std_logic_vector(3 downto 0);
      MI32_0_DRD  : out std_logic_vector(31 downto 0);
      MI32_0_ARDY : out std_logic;
      MI32_0_DRDY : out std_logic;

      MI32_1_DWR  : in  std_logic_vector(31 downto 0);
      MI32_1_ADDR : in  std_logic_vector(31 downto 0);  
      MI32_1_RD   : in  std_logic;
      MI32_1_WR   : in  std_logic;
      MI32_1_BE   : in  std_logic_vector(3 downto 0);
      MI32_1_DRD  : out std_logic_vector(31 downto 0);
      MI32_1_ARDY : out std_logic;
      MI32_1_DRDY : out std_logic;


      -- MI32_ASYNC master clock - used for both MI32_ASYNC components
      MI32_CLK   : in std_logic
   );

end entity rep_2port_top;

-- ----------------------------------------------------------------------------
--  Architecture declaration: REP_2PORT_TOP_ARCH
-- ---------------------------------------------------------------------------- 
architecture rep_2port_top_arch of rep_2port_top is

   signal reset_ibuf_ifc     : std_logic;

   signal enable_0           : std_logic;
   signal enable_1           : std_logic;

   signal clk_ibuf0          : std_logic;
   signal clk_ibuf1          : std_logic;

   signal cnt_overflow_0     : std_logic_vector(9 downto 0);
   signal cnt_overflow_0_ce  : std_logic;

   signal cnt_overflow_1     : std_logic_vector(9 downto 0);
   signal cnt_overflow_1_ce  : std_logic;

   signal cnt_underflow_0    : std_logic_vector(9 downto 0);
   signal cnt_underflow_0_ce : std_logic;

   signal cnt_underflow_1    : std_logic_vector(9 downto 0);
   signal cnt_underflow_1_ce : std_logic;

   signal reg_en_0           : std_logic;
   signal reg_en_0_we        : std_logic;

   signal reg_en_1           : std_logic;
   signal reg_en_1_we        : std_logic;

   signal cs_reg_en_0        : std_logic;
   signal cs_reg_en_1        : std_logic;

   -- connects MI32_ASYNC component and MI32 address decoder
   signal mi32_addr_dec_0    : t_mi32;
   signal mi32_addr_dec_1    : t_mi32;

   signal mi32_0             : t_mi32;
   signal mi32_1             : t_mi32;
         

begin

   -- -------------------------------------------------------------------------
   --                             Repeater
   -- -------------------------------------------------------------------------
   REP_2PORT_COVER_I : entity work.REP_2PORT_COVER
   port map (
      ECLK           => ECLK,
      RESET_GLOBAL   => RESET_GLOBAL,
      RESET_IBUF_IFC => reset_ibuf_ifc,
   
      -- XGMII Receiver A input
      RXCLKA     => RXCLKA,
      RXDA       => RXDA,
      RXCA       => RXCA,

      -- XGMII Receiver B input 
      RXCLKB     => RXCLKB,
      RXDB       => RXDB,
      RXCB       => RXCB,
   
      -- packet forwarding enable
      EN0        => reg_en_0,
      EN1        => reg_en_1,

      -- FIFO overflow indicator
      OVERFLOW0  =>  cnt_overflow_0_ce,
      OVERFLOW1  =>  cnt_overflow_1_ce,

      -- FIFO underflow indicator
      UNDERFLOW0 =>  cnt_underflow_0_ce,
      UNDERFLOW1 =>  cnt_underflow_1_ce,

      -- XGMII Transmitter A output
      TXCLKA     => TXCLKA,
      TXDA       => TXDA,
      TXCA       => TXCA,

      -- XGMII Transmitter B output
      TXCLKB     => TXCLKB,
      TXDB       => TXDB,
      TXCB       => TXCB,

      -- XGMII Receiver A output
      IBUF0_CLK  => clk_ibuf0,
      IBUF0_DATA => IBUF0_DATA,
      IBUF0_CMD  => IBUF0_CMD,
   
      -- XGMII Receiver B output
      IBUF1_CLK  => clk_ibuf1,
      IBUF1_DATA => IBUF1_DATA, 
      IBUF1_CMD  => IBUF1_CMD
   );


   IBUF0_CLK   <= clk_ibuf0;
   IBUF1_CLK   <= clk_ibuf1;
   RESET_IBUF  <= reset_ibuf_ifc;

   mi32_0.DWR  <= MI32_0_DWR;   
   mi32_0.ADDR <= MI32_0_ADDR;
   mi32_0.RD   <= MI32_0_RD;   
   mi32_0.WR   <= MI32_0_WR;   
   mi32_0.BE   <= MI32_0_BE;   
   MI32_0_DRD  <= mi32_0.DRD; 
   MI32_0_ARDY <= mi32_0.ARDY;
   MI32_0_DRDY <= mi32_0.DRDY;

   mi32_1.DWR  <= MI32_1_DWR;   
   mi32_1.ADDR <= MI32_1_ADDR;
   mi32_1.RD   <= MI32_1_RD;   
   mi32_1.WR   <= MI32_1_WR;   
   mi32_1.BE   <= MI32_1_BE;   
   MI32_1_DRD  <= mi32_1.DRD; 
   MI32_1_ARDY <= mi32_1.ARDY;
   MI32_1_DRDY <= mi32_1.DRDY;


   -- MI32_ASYNC instantiation ------------------------------------------------
   MI32_ASYNC_0 : entity work.MI32_ASYNC
   port map (
      RESET => RESET_GLOBAL,

      -- Master interface
      CLK_M => MI32_CLK,
      MI_M  => mi32_0,

      -- Slave interface
      CLK_S => clk_ibuf0,
      MI_S  => mi32_addr_dec_0
   );


   -- MI32_ASYNC instantiation ------------------------------------------------
   MI32_ASYNC_1 : entity work.MI32_ASYNC
   port map (
      RESET => RESET_GLOBAL,

      -- Master interface
      CLK_M => MI32_CLK,
      MI_M  => mi32_1,
           
      -- Slave interface
      CLK_S => clk_ibuf1,
      MI_S  => mi32_addr_dec_1
   );



   -- MI32_0 address decoder (for enable register 0) --------------------------
--    addr_dec_0 : process(mi32_addr_dec_0.ADDR, mi32_addr_dec_0.WR)
--    begin 
--       cs_reg_en_0 <= '0';
-- 
--       case mi32_addr_dec_0.ADDR(3 downto 0) is 
--          when X"0" => cs_reg_en_0 <= '1';
--          when others => null;
--       end case;   
--    end process addr_dec_0;
   cs_reg_en_0 <= '1' when mi32_addr_dec_0.ADDR(3 downto 2) = "00" else '0';

   reg_en_0_we <= cs_reg_en_0 AND mi32_addr_dec_0.WR;
   mi32_addr_dec_0.ARDY <= mi32_addr_dec_0.RD XOR mi32_addr_dec_0.WR;
   mi32_addr_dec_0.DRDY <= mi32_addr_dec_0.RD;



   -- MI32_1 address decoder (for enable register 1) --------------------------
--    addr_dec_1 : process(mi32_addr_dec_1.ADDR, mi32_addr_dec_1.WR)
--    begin 
--       cs_reg_en_1 <= '0';
-- 
--       case mi32_addr_dec_1.ADDR(3 downto 0) is 
--          when X"0"   => cs_reg_en_1 <= '1';
--          when others => null;
--       end case;   
--    end process addr_dec_1;
   cs_reg_en_1 <= '1' when mi32_addr_dec_1.ADDR(3 downto 2) = "00" else '0';

   reg_en_1_we <= cs_reg_en_1 AND mi32_addr_dec_1.WR;
   mi32_addr_dec_1.ARDY <= mi32_addr_dec_1.RD XOR mi32_addr_dec_1.WR;
   mi32_addr_dec_1.DRDY <= mi32_addr_dec_1.RD;



   -- MI32_0 output select ----------------------------------------------------
   mux_out_0 : process(mi32_addr_dec_0.ADDR, cnt_overflow_0, cnt_underflow_0,
                       reg_en_0)
   begin
      mi32_addr_dec_0.DRD  <= (others => '0');
--      mi32_addr_dec_0.DRDY <= '0';

      case mi32_addr_dec_0.ADDR(3 downto 0) is
         when "0000" =>
            mi32_addr_dec_0.DRD  <= X"0000000" & "000" & reg_en_0;
         when "0100" =>
            mi32_addr_dec_0.DRD  <= X"00000" & "00" & cnt_overflow_0;
         when "1000" =>
            mi32_addr_dec_0.DRD  <= X"00000" & "00" & cnt_underflow_0;
         when others =>
            null;
      end case;
   end process mux_out_0;



   -- MI32_1 output select ----------------------------------------------------
   mux_out_1 : process(mi32_addr_dec_1.ADDR, cnt_overflow_1, cnt_underflow_1,
                       reg_en_1)
   begin
      mi32_addr_dec_1.DRD  <= (others => '0');
--      mi32_addr_dec_1.DRDY <= '0';

      case mi32_addr_dec_1.ADDR(3 downto 0) is
         when "0000" =>
            mi32_addr_dec_1.DRD  <= X"0000000" & "000" & reg_en_1;
         when "0100" =>
            mi32_addr_dec_1.DRD  <= X"00000" & "00" & cnt_overflow_1;
         when "1000" =>
            mi32_addr_dec_1.DRD  <= X"00000" & "00" & cnt_underflow_1;
         when others =>
            null;
      end case;
   end process mux_out_1;



   -- register reg_en_0 -------------------------------------------------------
   reg_en_0p: process(reset_ibuf_ifc, clk_ibuf0, reg_en_0_we)
   begin
--       if (reset_ibuf_ifc = '1') then
--          reg_en_0 <= '1';
--       end if;
      if (clk_ibuf0'event AND clk_ibuf0 = '1') then
         if (reset_ibuf_ifc = '1') then
            reg_en_0 <= '1';
         elsif (reg_en_0_we = '1') then
            reg_en_0 <= mi32_addr_dec_0.DWR(0);
         end if;
      end if;
   end process;
   

   
   -- register reg_en_1 -------------------------------------------------------
   reg_en_1p: process(reset_ibuf_ifc, clk_ibuf1, reg_en_1_we)
   begin
--       if (reset_ibuf_ifc = '1') then
--          reg_en_1 <= '1';
--       end if;
      if (clk_ibuf1'event AND clk_ibuf1 = '1') then
         if (reset_ibuf_ifc = '1') then
            reg_en_1 <= '1';
         elsif (reg_en_1_we = '1') then
            reg_en_1 <= mi32_addr_dec_1.DWR(0);
         end if;
      end if;
   end process;
   


   -- cnt_overflow_0 counter --------------------------------------------------
   cnt_overflow_0p: process(reset_ibuf_ifc, clk_ibuf0, cnt_overflow_0_ce)
   begin
--       if (reset_ibuf_ifc = '1') then
--          cnt_overflow_0 <= (others => '0');
--       end if;
      if (clk_ibuf0'event AND clk_ibuf0 = '1') then
         if (reset_ibuf_ifc = '1') then
            cnt_overflow_0 <= (others => '0');
         elsif (cnt_overflow_0_ce = '1') then
            cnt_overflow_0 <= cnt_overflow_0 + 1;
         end if;
      end if;
   end process;
   
   

   -- cnt_overflow_1 counter --------------------------------------------------
   cnt_overflow_1p: process(reset_ibuf_ifc, clk_ibuf1, cnt_overflow_1_ce)
   begin
--       if (reset_ibuf_ifc = '1') then
--          cnt_overflow_1 <= (others => '0');
--       end if;
       if (clk_ibuf1'event AND clk_ibuf1 = '1') then
         if (reset_ibuf_ifc = '1') then
            cnt_overflow_1 <= (others => '0');
         elsif (cnt_overflow_1_ce = '1') then
            cnt_overflow_1 <= cnt_overflow_1 + 1;
         end if;
      end if;
   end process;
 
   

   -- cnt_underflow_0 counter -------------------------------------------------
   cnt_underflow_0p: process(reset_ibuf_ifc, clk_ibuf0)
   begin
--       if (reset_ibuf_ifc = '1') then
--          cnt_underflow_0 <= (others => '0');
--       end if;
      if (clk_ibuf0'event AND clk_ibuf0 = '1') then
         if (reset_ibuf_ifc = '1') then
            cnt_underflow_0 <= (others => '0');
         elsif (cnt_underflow_0_ce = '1') then
            cnt_underflow_0 <= cnt_underflow_0 + 1;
         end if;
      end if;
   end process;
   

   
   -- cnt_underflow_1 counter -------------------------------------------------
   cnt_underflow_1p: process(reset_ibuf_ifc, clk_ibuf1)
   begin
--       if (reset_ibuf_ifc = '1') then
--          cnt_underflow_1 <= (others => '0');
--       end if;
      if (clk_ibuf1'event AND clk_ibuf1 = '1') then
         if (reset_ibuf_ifc = '1') then
            cnt_underflow_1 <= (others => '0');
         elsif (cnt_underflow_1_ce = '1') then
            cnt_underflow_1 <= cnt_underflow_1 + 1;
         end if;
      end if;
   end process;

end architecture rep_2port_top_arch;

