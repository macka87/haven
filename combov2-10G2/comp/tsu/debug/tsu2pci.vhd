--
-- tsu2pci.vhd: Debugging design for TSU (add on card)
-- Copyright (C) 2004 Masaryk University
-- Author(s): Jiri Novotny <novotny@ics.muni.cz>
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
-- TODO: need to debug :-), just syntax debug is done
-- ----------------------------------------------------------------------------
--                      Entity declaration
-- ----------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;

architecture behavioral of fpga is

   signal reset: std_logic;

-- Connect to PTM

   signal refclk : std_logic;
   signal ppfts : std_logic;
   signal ts_ptm : std_logic_vector(7 downto 0);
   signal ts_request : std_logic;
   signal ts_short : std_logic;
   signal ts_fast : std_logic;

-- PCI local bus - local bus side

   signal lbclk : std_logic;
   signal lbframe : std_logic;
   signal lbholda :std_logic;
   signal lbad : std_logic_vector (15 downto 0);
   signal lbas : std_logic;
   signal lbrw : std_logic;
   signal lbrdy : std_logic;
   signal lblast : std_logic;

-- PCI local bus - register side

   constant pci_wide : integer := 16;

   constant adr_w : integer := 4; -- width of address is 4 bits i.e. 16 address
   constant pci_steps : integer := 4;
   signal pci_adr : std_logic_vector (adr_w-1 downto 0);
   signal data_from_lb :std_logic_vector (pci_wide-1 downto 0 );
   signal data_to_lb : std_logic_vector (pci_wide-1 downto 0 );
   signal pci_en : std_logic;
   signal pci_rw : std_logic;
   signal pci_adr_d : integer;

   subtype pci_part is std_logic_vector (pci_wide-1 downto 0);
   type pci_part_vector is array (natural range <>) of pci_part;
   signal data_l : pci_part_vector (pci_steps-1 downto 0);


   constant pci_stat : integer := 16#8#;
   constant pci_dat : integer := 16#00#;
   constant pci_adr_dmax : integer := pci_dat + 16#04#;


-- PCI signals

   signal ts_en_add : std_logic;
   signal ts_short_add : std_logic;
   signal ts_fast_add : std_logic;
   signal ts_ack_add : std_logic;
   signal ts_ack_add_t : std_logic;
   signal ts_add : std_logic_vector (63 downto 0);

   signal pci_write : std_logic;
   signal pci_read : std_logic;

-- Translate signed vector into integer representation
--
   function evec2int (l: std_logic_vector)
     return natural is
     variable result: natural := 0;
     begin
        for t1 in l'range loop
           result := result * 2;
           if (l(t1) = '1' or l(t1) = 'H') then
              result := result + 1;
           end if;
        end loop;
        return result;
    end evec2int;

component PULLDOWN
   port(O     : out std_logic
   );
end component;

begin

   reset <= not LRESET;

--   refclk <= IO(28);
--   ppfts <= IO (30);
--   ts_ptm <= IO (43 downto 36);
--   IO(29) <= ts_request;
--   IO(31) <= ts_short;

   refclk <= IO(28);
   IO(29) <= ts_request;
   IO(31) <= ts_fast;
   ts_ptm(0) <= IO(32);
   ts_ptm(2) <= IO(33);
   ts_ptm(4) <= IO(34);
   ts_ptm(6) <= IO(35);
   IO(36) <= ts_short;
   ppfts <= IO(39);
   ts_ptm(1) <= IO(40);
   ts_ptm(3) <= IO(41);
   ts_ptm(5) <= IO(42);
   ts_ptm(7) <= IO(43);


-- Local (internal) bus to PLX communication component -------------
   Inst_local_bus: entity work.local_bus
   port map(
      lad     => LAD,
      ads     => ADS,
      blast   => BLAST,
      lhold   => LHOLD,
      lholda  => LHOLDA,
      lwr     => LWR,
      ready   => READY,
      lreset  => LRESET,
      lclkf   => LCLKF,
      usero   => USERO,
      lbclk   => lbclk,
      lbframe => lbframe,
      lbholda => lbholda,
      lbad    => lbad,
      lbas    => lbas,
      lbrw    => lbrw,
      lbrdy   => lbrdy,
      lblast  => lblast,
      swq_req => '0'
   );


   lb_connect0: entity work.lbconn_mem
   generic map(
      ADDR_WIDTH => adr_w,      -- address bus width
      BASE       => 16#00#  -- base address 0x0
   )
   port map(
      data_out => data_from_lb,
      data_in  => data_to_lb,
      addr     => pci_adr,
      en       => pci_en,
      rw       => pci_rw,
      sel      => open,
      drdy     => '1',
      ardy     => '1',
      reset    => reset,
      lbclk    => lbclk,
      lbframe  => lbframe,
      lbas     => lbas,
      lbrw     => lbrw,
      lblast   => lblast,
      lbad     => lbad,
      lbholda  => lbholda,
      lbrdy    => lbrdy
   );

   tsu_add_test: entity work.tsu_add
   port map(
        -- Input from PTM
     REFCLK	=> refclk,
     PPFTS	=> ppfts,
     TS_PTM	=> ts_ptm,
     --       from Add on Card
     RESET	=> reset,
     CLK_ADD	=> lbclk,
     TS_EN_ADD	=> ts_en_add,
     TS_SHORT_ADD => ts_short_add,
     TS_FAST_ADD => ts_fast_add,

     -- Output to PTM
     TS_REQUEST	=> ts_request,
     TS_SHORT	=> ts_short,
     TS_FAST	=> ts_fast,
     --        to Add on Card
     TS_ACK_ADD	=> ts_ack_add,
     TS_ADD	=> ts_add
   );

   pci_adr_d <= evec2int(pci_adr);
   pci_write <= '1' when pci_en = '1' and pci_rw = '1' else '0';
   pci_read <= '1' when pci_en = '1' and pci_rw = '0' else '0';


  process (reset, lbclk)
  begin
     if (reset = '1') then
        ts_en_add <= '0';
        ts_short_add <= '0';
     elsif (lbclk'event and lbclk = '1') then
        ts_en_add <= '0';
        if pci_write = '1' and pci_adr_d = pci_stat then
           ts_en_add <= data_from_lb(7);
           ts_short_add <= data_from_lb(0);
	   ts_fast_add <= data_from_lb(1);
        end if;
     end if;
   end process;

   process (reset, lbclk)
   begin
      if (reset = '1') then
         data_to_lb <= (others => '0');
      elsif (lbclk'event and lbclk = '1') then
         if pci_read = '1' and pci_adr_d = pci_stat then
            data_to_lb <= (ts_ack_add_t, others => '0');
         elsif pci_read = '1' and pci_adr_d < pci_adr_dmax then
            data_to_lb <= data_l(pci_adr_d);
         else
--            data_to_lb <= (others => '0');
            data_to_lb <= X"1234";
         end if;
      end if;
   end process;

   L1: for i in 1 to pci_steps generate
          data_l(i-1) <= ts_add(pci_wide*i-1 downto pci_wide*(i-1)) ;
       end generate;

  process (reset, lbclk)
  begin
     if (reset = '1') then
        ts_ack_add_t <= '0';
     elsif (lbclk'event and lbclk = '1') then
        if ts_ack_add = '1' then
	   ts_ack_add_t <= '1';
	elsif pci_read = '1' and pci_adr_d = pci_stat then
	   ts_ack_add_t <= '0';
        else
	   ts_ack_add_t <= ts_ack_add_t;
        end if;
     end if;
   end process;

end architecture behavioral;


