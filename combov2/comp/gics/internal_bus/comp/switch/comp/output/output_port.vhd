--
-- output_port.vhd : IB Switch Output port
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 
use work.ib_switch_pkg.all;

-- ----------------------------------------------------------------------------
--                 ENTITY DECLARATION -- IB Switch Output port               -- 
-- ----------------------------------------------------------------------------

entity IB_SWITCH_OUTPUT_PORT is 
   generic(
      -- Data Width (1-128)
      DATA_WIDTH   : integer:= 64;
      -- Port number (0/1/2)
      PORT_NUM     : integer:=  0         
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK            : in std_logic;  
      RESET          : in std_logic;  

      -- Upstream Port #0 (input) ---------------------------------------------
      IN0_DATA       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN0_DATA_VLD   : in  std_logic;
      IN0_SOF_N      : in  std_logic;
      IN0_EOF_N      : in  std_logic;      
      IN0_RD         : out std_logic;

      IN0_REQ        : in  std_logic;
      IN0_ACK        : out std_logic;

      -- Downstream Port #1 (input) -------------------------------------------
      IN1_DATA       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN1_DATA_VLD   : in  std_logic;
      IN1_SOF_N      : in  std_logic;
      IN1_EOF_N      : in  std_logic;      
      IN1_RD         : out std_logic;
                          
      IN1_REQ        : in  std_logic;
      IN1_ACK        : out std_logic;      
 
      -- Downstream Port #2 ---------------------------------------------------
      IN2_DATA       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN2_DATA_VLD   : in  std_logic;
      IN2_SOF_N      : in  std_logic;
      IN2_EOF_N      : in  std_logic;      
      IN2_RD         : out std_logic;
                          
      IN2_REQ        : in  std_logic;
      IN2_ACK        : out std_logic;

      -- OUTPUT Port ----------------------------------------------------------
      OUT_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_SOF_N     : out std_logic;
      OUT_EOF_N     : out std_logic;
      OUT_SRC_RDY_N : out std_logic;
      OUT_DST_RDY_N : in  std_logic      
   );
end IB_SWITCH_OUTPUT_PORT;

-- ----------------------------------------------------------------------------
--              ARCHITECTURE DECLARATION  --  IB Switch Output port          --
-- ----------------------------------------------------------------------------

architecture ib_switch_output_port_arch of IB_SWITCH_OUTPUT_PORT is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal fsm_out_sof_n     : std_logic;
   signal fsm_out_eof_n     : std_logic;
   signal fsm_out_src_rdy_n : std_logic;
   signal fsm_out_dst_rdy_n : std_logic; 
   signal mx_sel            : std_logic_vector(1 downto 0);
   signal mx_out_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal pipe_empty        : std_logic;
   
begin

   -- -------------------------------------------------------------------------
   --                             OUTPUT FSM                                 --
   -- -------------------------------------------------------------------------
   
   U_ib_switch_output_fsm: entity work.IB_SWITCH_OUTPUT_FSM
   generic map (
      -- Port number (0/1/2)
      PORT_NUM       => PORT_NUM      
   )
   port map (
      -- Common interface -----------------------------------------------------
      CLK            => CLK, 
      RESET          => RESET,

      -- Upstream Port #0 (input) ---------------------------------------------
      IN0_DATA_VLD   => IN0_DATA_VLD,
      IN0_SOF_N      => IN0_SOF_N,   
      IN0_EOF_N      => IN0_EOF_N,        
      IN0_RD         => IN0_RD,      

      IN0_REQ        => IN0_REQ,
      IN0_ACK        => IN0_ACK,

      -- Downstream Port #1 (input) -------------------------------------------
      IN1_DATA_VLD   => IN1_DATA_VLD,
      IN1_SOF_N      => IN1_SOF_N,   
      IN1_EOF_N      => IN1_EOF_N,              
      IN1_RD         => IN1_RD,      
                       
      IN1_REQ        => IN1_REQ,
      IN1_ACK        => IN1_ACK,      
 
      -- Downstream Port #2 ---------------------------------------------------
      IN2_DATA_VLD   => IN2_DATA_VLD,
      IN2_SOF_N      => IN2_SOF_N,   
      IN2_EOF_N      => IN2_EOF_N,              
      IN2_RD         => IN2_RD,      
                       
      IN2_REQ        => IN2_REQ,
      IN2_ACK        => IN2_ACK,

      -- OUTPUT Port ----------------------------------------------------------
      OUT_SOF_N      => fsm_out_sof_n,
      OUT_EOF_N      => fsm_out_eof_n,
      OUT_SRC_RDY_N  => fsm_out_src_rdy_n,
      OUT_DST_RDY_N  => fsm_out_dst_rdy_n,

      -- OUTPUT data control --------------------------------------------------
      MX_SEL         => mx_sel
   );

   -- -------------------------------------------------------------------------
   --                        OUTPUT DATA MULTIPLEXOR                         --
   -- -------------------------------------------------------------------------

   -- PORT 0 ------------------------------------------------------------------
   MX_PORT0: if (PORT_NUM = 0) generate 
   
      port0_mxp: process(mx_sel, IN0_DATA, IN1_DATA, IN2_DATA)
      begin
         case mx_sel is
            when "01" => mx_out_data <= IN1_DATA;
            when "10" => mx_out_data <= IN2_DATA;
            when others => mx_out_data <= (others => 'X');
         end case;
      end process;    
      
   end generate;

   -- PORT 1 ------------------------------------------------------------------
   MX_PORT1: if (PORT_NUM = 1) generate 

      port1_mxp: process(mx_sel, IN0_DATA, IN1_DATA, IN2_DATA)
      begin
         case mx_sel is
            when "00" => mx_out_data <= IN0_DATA;
            when "10" => mx_out_data <= IN2_DATA;
            when others => mx_out_data <= (others => 'X');
         end case;
      end process;      

   end generate;

   -- PORT 2 ------------------------------------------------------------------
   MX_PORT2: if (PORT_NUM = 2) generate 

      port2_mxp: process(mx_sel, IN0_DATA, IN1_DATA, IN2_DATA)
      begin
         case mx_sel is
            when "00" => mx_out_data <= IN0_DATA;
            when "01" => mx_out_data <= IN1_DATA;
            when others => mx_out_data <= (others => 'X');
         end case;
      end process;         

   end generate;   

   -- WRONG PORT NUMBER ASSERTION ---------------------------------------------
   assert ((PORT_NUM = 0) or (PORT_NUM = 1) or (PORT_NUM = 2))
   report "Wrong port number (IB_SWITCH_OUTPUT_PORT)."
   severity ERROR;    

   -- -------------------------------------------------------------------------
   --                          OUTPUT PIPELINE                               --
   -- -------------------------------------------------------------------------

   output_pipelinep: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            pipe_empty            <= '1';
            --OUT_DATA              <= (others => '0');
            OUT_SOF_N             <= '1';
            OUT_EOF_N             <= '1';
            OUT_SRC_RDY_N         <= '1';
      
         elsif (OUT_DST_RDY_N = '0' or pipe_empty = '1') then
            pipe_empty         <= fsm_out_src_rdy_n;
            OUT_DATA           <= mx_out_data;
            OUT_SOF_N          <= fsm_out_sof_n;
            OUT_EOF_N          <= fsm_out_eof_n;
            OUT_SRC_RDY_N      <= fsm_out_src_rdy_n;
         end if;
      end if;
   end process;

   fsm_out_dst_rdy_n  <= not (not OUT_DST_RDY_N or pipe_empty);
   
end ib_switch_output_port_arch;


