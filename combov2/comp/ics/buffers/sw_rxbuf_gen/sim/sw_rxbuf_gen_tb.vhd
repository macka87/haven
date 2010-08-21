--
-- sw_rxbuf_gen_tb.vhd: Testbench for SW_RXBUF_GEN
-- Copyright (C) 2010 CESNET
-- Author(s): Karel Koranda    <xkoran01@stud.fit.vutbr.cz>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant clkper_50            : time    := 20 ns;
   constant clkper_100           : time    := 10 ns;
   constant reset_time           : time    := 10 * clkper_100;
   
   constant TEST_DATA_WIDTH      : integer := 64;
   constant TEST_BLOCK_SIZE      : integer := 8;
   constant TEST_FLOWS           : integer := 4;

   constant TEST_BMEM_ITEMS      : integer := 64;
   constant TEST_BMEM_MAX_BLOCKS : integer := 32;
   constant TEST_CTRL_MEM_ITEMS  : integer := 16;
   constant TEST_CONTROL_SIZE    : integer := 32;
   constant TEST_HEADER          : boolean := true;
   constant TEST_FOOTER          : boolean := true;
   constant TEST_RX_COUNT        : integer := 1;
   
   constant TEST_DATA_BITS       : integer := log2(TEST_DATA_WIDTH/8);
   constant TEST_BLOCK_BITS      : integer := log2(TEST_BLOCK_SIZE);
   constant TEST_FLOW_BITS       : integer := log2(TEST_FLOWS);
   constant TEST_SEPARE_BIT      : integer := TEST_BLOCK_BITS + TEST_DATA_BITS;
   constant TEST_ADDR_FLOWS_UP   : integer := TEST_DATA_BITS + TEST_BLOCK_BITS + 1 + TEST_FLOW_BITS - 1;
   constant TEST_ADDR_FLOWS_DOWN : integer := TEST_BLOCK_BITS + TEST_DATA_BITS + 1;

   -- -----------------------Testbench auxilarity signals----------------------
   -- CLK_GEN Signals
   signal reset               : std_logic;
   signal clk50               : std_logic;
   signal clk100              : std_logic;
   signal lock                : std_logic;

   -- SW_RXBUF signals
   
   signal init                : std_logic_vector(TEST_FLOWS-1 downto 0);
   
   -- status signals
   signal status              : std_logic_vector(log2(TEST_BLOCK_SIZE+1)*TEST_FLOWS-1 downto 0);
   signal full                : std_logic_vector(TEST_FLOWS-1 downto 0);
   signal empty               : std_logic_vector(TEST_FLOWS-1 downto 0);
   
   -- input FrameLink interface
   signal rx_addr             : std_logic_vector(abs(log2(TEST_FLOWS)-1) downto 0);
   
   signal rx_sof_n            : std_logic;
   signal rx_sop_n            : std_logic;
   signal rx_eop_n            : std_logic;
   signal rx_eof_n            : std_logic;
   signal rx_src_rdy_n        : std_logic;
   signal rx_dst_rdy_n        : std_logic_vector(TEST_FLOWS-1 downto 0);
   signal rx_data             : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
   signal rx_rem              : std_logic_vector(log2(TEST_DATA_WIDTH/8)-1 downto 0);
   
   -- read interface
   
   signal rd_addr             : std_logic_vector(31 downto 0);
   signal rd_be               : std_logic_vector((TEST_DATA_WIDTH/8)-1 downto 0);
   signal rd_req              : std_logic;
   signal rd_ardy             : std_logic;
   
   signal rd_data             : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
   signal rd_src_rdy          : std_logic;
   signal rd_dst_rdy          : std_logic;
   
   -- rellen and newlen
   signal rellen              : std_logic_vector(15 downto 0);
   signal rellen_dv           : std_logic;
   signal rellen_ifc          : std_logic_vector(abs(log2(TEST_FLOWS)-1) downto 0);
   signal newlen              : std_logic_vector(15 downto 0);
   signal newlen_dv           : std_logic;
   signal newlen_ifc          : std_logic_vector(abs(log2(TEST_FLOWS)-1) downto 0);

-- CLK setting
 	   alias ib_clk               : std_logic is clk100;
 	   alias clk                  : std_logic is clk100;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   uut : entity work.SW_RXBUF_GEN
      generic map(
         DATA_WIDTH     => TEST_DATA_WIDTH,
         BLOCK_SIZE     => TEST_BLOCK_SIZE,
         FLOWS          => TEST_FLOWS
      )
      port map(
         CLK            => clk100,
         RESET          => reset,
         INIT           => init,
         
         STATUS         => status,
         EMPTY          => empty,
         FULL           => full,
         
         -- Input Interface
         RD_ADDR        => rd_addr,
         RD_BE          => rd_be,
         RD_REQ         => rd_req,
         RD_ARDY        => rd_ardy,
         -- Output Interface
         RD_DATA        => rd_data,
         RD_SRC_RDY     => rd_src_rdy,
         RD_DST_RDY     => rd_dst_rdy,
         -- input FrameLink interface
         RX_ADDR        => rx_addr,
         RX_SOF_N       => rx_sof_n,
         RX_SOP_N       => rx_sop_n,
         RX_EOP_N       => rx_eop_n,
         RX_EOF_N       => rx_eof_n,
         RX_SRC_RDY_N   => rx_src_rdy_n,
         RX_DST_RDY_N   => rx_dst_rdy_n,
         RX_DATA        => rx_data,
         RX_REM         => rx_rem,
         -- 
         BUF_NEWLEN     => newlen,
         BUF_NEWLEN_DV  => newlen_dv,
         BUF_NEWLEN_IFC => newlen_ifc,
         BUF_RELLEN     => rellen,
         BUF_RELLEN_DV  => rellen_dv,
         BUF_RELLEN_IFC => rellen_ifc

      );


   -- Reset generation --------------------------------------------------------
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;
   
   -- clk50 generator ---------------------------------------------------------
   clk50_gen : process
   begin
      clk50 <= '1';
      wait for clkper_50/2;
      clk50 <= '0';
      wait for clkper_50/2;
   end process;
   
   -- clk100 generator --------------------------------------------------------
   clk100_gen : process
   begin
      clk100 <= '1';
      wait for clkper_100/2;
      clk100 <= '0';
      wait for clkper_100/2;
   end process;
   

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process
   
begin

   rx_sof_n    <= '1';
   rx_sop_n    <= '1';
   rx_eop_n    <= '1';
   rx_eof_n    <= '1';
   rx_data     <= (others => '0');
   rx_rem      <= (others => '0');
   rx_src_rdy_n<= '1';

   rd_be <= (others => '1');

  rellen <= (others => '0');
  rellen_dv <= '0';
  rellen_ifc <= (others => '0');
  
  rd_addr <= (others => '0');
  rd_dst_rdy <= '0';
  rd_req <= '0';

  init <= (others => '0');

   wait for reset_time;
   wait for clkper_100;
   wait for 1 ps;

  rx_sof_n <= '0';
  rx_src_rdy_n <= '0';  

  rx_data <= (others => '0');
  for j in 0 to 3 loop
    rx_addr <= conv_std_logic_vector(j, rx_addr'length);
    rx_data <= rx_data + 16;
    wait for clkper_100;
  end loop;

  rx_sof_n <= '1';
  rx_addr <= (others => '0');
  
  for j in 0 to 10 loop
    rx_data <= conv_std_logic_vector(j, rx_data'length);
    wait for clkper_100;
    rx_addr <= rx_addr + 1;
  end loop;  

  rx_eof_n <= '0';
  rx_data <= conv_std_logic_vector(15, rx_data'length);
  wait for clkper_100;
  
  rx_addr <= rx_addr + 1;
  rx_data <= conv_std_logic_vector(15, rx_data'length);
  wait for clkper_100;
  
  rx_eof_n <= '1';
  rx_addr <= rx_addr + 1;
  rx_data <= conv_std_logic_vector(7, rx_data'length);
  wait for clkper_100;
  
  rx_eof_n <= '0';
  rx_addr <= rx_addr + 1;
  rx_data <= conv_std_logic_vector(7, rx_data'length);
  wait for clkper_100;
  
  rx_eof_n <= '1';
  rx_src_rdy_n <= '1';
  wait for 2*clkper_100;
  rx_addr <= conv_std_logic_vector(1, rx_addr'length);
  rx_eof_n <= '0';
  rx_src_rdy_n <= '0';
  rx_data <= conv_std_logic_vector(15, rx_data'length);
  wait for clkper_100;
  rx_eof_n <= '1';
  rx_src_rdy_n <= '1';
  
  wait for 4 * clkper_100;
  
  rx_src_rdy_n <= '0';
  rx_sof_n <= '0';
  rx_addr <= (others => '0');
  rx_data <= conv_std_logic_vector(27, rx_data'length);
  
  for j in 1 to 8 loop
    wait for clkper_100;
    rx_data <= rx_data + 10;
    if (j = 1) then
      rx_sof_n <= '1';
      rellen_dv <= '1';
      rellen <= conv_std_logic_vector(5, rellen'length);
      rellen_ifc <= (others => '0');
    end if;
    if (j = 2) then
      rellen_dv <= '0';
    end if;
    if (j = 7) then
      rx_eof_n <= '0';
    end if;
    if (j = 8) then
      rx_eof_n <= '1';
      rx_src_rdy_n <= '1';
    end if;
  end loop;
    
    wait for 4 * clkper_100;
    
    rd_addr <= (others => '0');
    rd_req <= '1';
    rd_dst_rdy <= '1';
    
    for j in 1 to 8 loop
      wait for clkper_100;
      rd_addr(TEST_SEPARE_BIT) <= '1'; -- 1
      wait for clkper_100;
      rd_addr(TEST_SEPARE_BIT) <= '0'; -- 0
      rd_addr((TEST_DATA_BITS+TEST_BLOCK_BITS)-1 downto TEST_DATA_BITS) <= conv_std_logic_vector(j, TEST_BLOCK_BITS);
    end loop;
    
    rd_req <= '0';
    wait for 4 * clkper_100;
    
    rd_req <= '1';
    
    for i in 0 to 3 loop
      rd_addr(TEST_ADDR_FLOWS_UP downto TEST_ADDR_FLOWS_DOWN) <= conv_std_logic_vector(i, TEST_FLOW_BITS);
      for j in 1 to 8 loop
        wait for clkper_100;
        rd_addr(TEST_SEPARE_BIT) <= '1'; -- 1
        wait for clkper_100;
        rd_addr(TEST_SEPARE_BIT) <= '0'; -- 0
        rd_addr((TEST_DATA_BITS+TEST_BLOCK_BITS)-1 downto TEST_DATA_BITS) <= conv_std_logic_vector(j, TEST_BLOCK_BITS);        
      end loop;
    end loop;
    
    rd_req <= '0';
    
    rd_addr <= (others => '0');
    
    wait for 4 * clkper_100;
    
    rd_dst_rdy <= '0';
    rellen_ifc <= conv_std_logic_vector(0, rellen_ifc'length);
    rellen_dv <= '1';
    rellen <= conv_std_logic_vector(8, rellen'length);
    
    wait for clkper_100;
    
    rellen_ifc <= conv_std_logic_vector(1, rellen_ifc'length);
    rellen_dv <= '1';
    rellen <= conv_std_logic_vector(6, rellen'length);
    
    wait for clkper_100;
    
    rellen_ifc <= conv_std_logic_vector(3, rellen_ifc'length);
    rellen_dv <= '1';
    rellen <= conv_std_logic_vector(2, rellen'length);
    
    wait for clkper_100;
   
    rellen_ifc <= conv_std_logic_vector(2, rellen_ifc'length);
    rellen_dv <= '1';
    rellen <= conv_std_logic_vector(5, rellen'length);
    
    wait for clkper_100;

    rellen_ifc <= conv_std_logic_vector(3, rellen_ifc'length);
    rellen_dv <= '1';
    rellen <= conv_std_logic_vector(2, rellen'length);
    
    wait for clkper_100;
   
    rellen_dv <= '0';
    
   wait;
end process;

end architecture behavioral;
