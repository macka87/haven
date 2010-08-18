--
-- crossbar.vhd : Crossbar for gmii interface.
-- Copyright (C) 2007 CESNET
-- Author(s): Bronislav Pribyl <xpriby12@stud.fit.vutbr.cz>
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the OpenIPCore Hardware General Public
-- License as published by the OpenIPCore Organization; either version
-- 0.20-15092000 of the License, or (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful, but
-- WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- OpenIPCore Hardware General Public License for more details.
--
-- You should have received a copy of the OpenIPCore Hardware Public
-- License along with this program; if not, download it from
-- OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;


-- Internal bus package
use work.lb_pkg.all;

-- Math package - log2 function
use work.math_pack.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on



architecture full of crossbar is

   signal din  : std_logic_vector(10*(PORTS+INPUTS)-1 downto 0);
   signal sel  : std_logic_vector((log2(PORTS+INPUTS) * (PORTS+OUTPUTS))-1 downto 0);
   signal dout : std_logic_vector(10*(PORTS+OUTPUTS)-1 downto 0);

   signal registers_out : std_logic_vector(log2(PORTS+INPUTS)-1 downto 0);

begin
   -- -------------------------------------------------------------------------
   -- Multiplexer "net"
   -- -------------------------------------------------------------------------
   In_signals : for i in 0 to INPUTS-1 generate
      din(10*(i+PORTS+1)-1 downto 10*(i+PORTS))
      <= I_RXD(8*(i+1)-1 downto 8*i) &
         I_RXDV(i) &
         I_RXER(i);
   end generate;

   In_ports : for i in 0 to PORTS-1 generate
      din(10*(i+1)-1 downto 10*i)
      <= P_RXD(8*(i+1)-1 downto 8*i) &
         P_RXDV(i) &
         P_RXER(i);
   end generate;


   Multiplexers : for i in 0 to (PORTS + OUTPUTS)-1 generate
      Multiplexer : entity work.GEN_MUX
      generic map(
         DATA_WIDTH => 10,
         MUX_WIDTH  => PORTS + INPUTS   -- multiplexer width (number of inputs)
      )
      port map(
         --(DATA_WIDTH*MUX_WIDTH-1 downto 0);
         DATA_IN  => din,
         --(log2(MUX_WIDTH)-1 downto 0);
         SEL      => sel((log2(PORTS+INPUTS)*(i+1)-1) downto log2(PORTS+INPUTS)*i),
         --(DATA_WIDTH-1 downto 0)
         DATA_OUT => dout(10*(i+1)-1 downto 10*i)
      );
   end generate;


   Out_ports : for i in 0 to PORTS-1 generate
      P_TXD(8*(i+1)-1 downto 8*i) <= dout(10*(i+1)-1 downto 10*i+2);
      P_TXEN(i)                   <= dout(10*i+1);
      P_TXER(i)                   <= dout(10*i);
   end generate;

   Out_signals : for i in 0 to OUTPUTS-1 generate
      O_TXD(8*(i+1)-1 downto 8*i) <= dout(10*(i+PORTS+1)-1 downto 10*(i+PORTS)+2);
      O_TXEN(i)                   <= dout(10*(i+PORTS)+1);
      O_TXER(i)                   <= dout(10*(i+PORTS));
   end generate;


   -- -------------------------------------------------------------------------
   -- Selection register array
   -- -------------------------------------------------------------------------
   Register_array_ports : for i in 0 to PORTS - 1 generate
      process(CLK,RESET)
      begin
         if (RESET = '1') then
            sel((log2(PORTS+INPUTS)*(i+1)-1) downto log2(PORTS+INPUTS)*i)
            <= conv_std_logic_vector(i+PORTS, log2(PORTS+INPUTS));
         elsif (CLK'event and CLK = '1') then
            if ((MI32.addr = conv_std_logic_vector(4*i,MI32.addr'length)) and (MI32.wr = '1')) then
               sel((log2(PORTS+INPUTS)*(i+1)-1) downto log2(PORTS+INPUTS)*i)
               <= MI32.dwr(log2(PORTS+INPUTS)-1 downto 0);
            end if;
         end if;
      end process;
   end generate;
   
   Register_array_outputs : for i in PORTS to (PORTS+OUTPUTS) - 1 generate
      process(CLK,RESET)
      begin
         if (RESET = '1') then
            sel((log2(PORTS+INPUTS)*(i+1)-1) downto log2(PORTS+INPUTS)*i)
            <= conv_std_logic_vector(i-PORTS, log2(PORTS+INPUTS));
         elsif (CLK'event and CLK = '1') then
            if ((MI32.addr = conv_std_logic_vector(4*i,MI32.addr'length)) and (MI32.wr = '1')) then
               sel((log2(PORTS+INPUTS)*(i+1)-1) downto log2(PORTS+INPUTS)*i)
               <= MI32.dwr(log2(PORTS+INPUTS)-1 downto 0);
            end if;
         end if;
      end process;
   end generate;


   -- -------------------------------------------------------------------------
   -- MI32 interface
   -- -------------------------------------------------------------------------
   Dout_multiplexer : entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => log2(PORTS+INPUTS),
      MUX_WIDTH   => PORTS + OUTPUTS   -- multiplexer width (number of inputs)
   )
   port map(
      --(DATA_WIDTH*MUX_WIDTH-1 downto 0);
      DATA_IN     => sel,
      --(log2(MUX_WIDTH)-1 downto 0);
      SEL         => mi32.addr(log2(PORTS+OUTPUTS)+1 downto 2),
      --(DATA_WIDTH-1 downto 0)
      DATA_OUT    => registers_out
   );

   MI32.ardy <= '1';
   MI32.drd  <= conv_std_logic_vector(0, 32-log2(PORTS+INPUTS)) & registers_out;
   MI32.drdy <= MI32.rd;

end architecture full;
