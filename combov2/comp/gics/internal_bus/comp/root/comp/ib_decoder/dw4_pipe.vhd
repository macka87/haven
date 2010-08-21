--
-- ib_pipe.vhd: Pipeline with negative logic
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
--            Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>  
--            Petr Kobierský <kobiersky@liberouter.org>
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

-- ----------------------------------------------------------------------------
--               PIPELINE FOR NEGATIVE LOGIC                                 --
-- ---------------------------------------------------------------------------- 
entity DW4_PIPE is
   generic(
      -- Data Width
      DATA_WIDTH     : integer := 64
   );   
   port(
      -- Common interface -----------------------------------------------------
      CLK            : in std_logic;
      RESET          : in std_logic;
      
      -- Input interface ------------------------------------------------------
      IN_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_SOF_N       : in  std_logic;
      IN_EOF_N       : in  std_logic;
      IN_SRC_RDY_N   : in  std_logic;
      IN_DST_RDY_N   : out std_logic;
      IN_DW4         : in  std_logic;
 
      -- Output interface -----------------------------------------------------
      OUT_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_SOF_N      : out std_logic;
      OUT_EOF_N      : out std_logic;
      OUT_SRC_RDY_N  : out std_logic;
      OUT_DST_RDY_N  : in  std_logic;
      OUT_DW4        : out std_logic; -- DW3/DW4 header
      OUT_DW4_VLD    : out std_logic  -- DW3/DW4 header valid
      );
end entity DW4_PIPE;


architecture FULL of DW4_PIPE is
   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
   type   fsm_states is (S_0, S_1, S_2);
   signal present_state, next_state : fsm_states; 
   signal ce                 : std_logic;
   signal addr               : std_logic;
   signal pipe_reg_in        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal pipe_src_rdy_n_in  : std_logic;
   signal pipe_sop_n_in      : std_logic;
   signal pipe_eop_n_in      : std_logic;
   signal aux_sop_n          : std_logic;

begin

   -- -------------------------------------------------------------------------
   --                               DATA PATH                                --
   -- -------------------------------------------------------------------------
   
   SH_REG_DATA_WIDTH : for i in 0 to DATA_WIDTH-1 generate
   begin
      SRL16E_DATA_U : entity work.SRL_REG16
         port map (
            CLK           => CLK,
            DATA          => IN_DATA(i),
            CE            => ce,
            A(0)          => addr,
            A(3 downto 1) => "000",
            Q             => pipe_reg_in(i)
            );
   end generate;

   SRL16E_SOF_N_U : entity work.SRL_REG16
      port map (
         CLK           => CLK,
         DATA          => IN_SOF_N,
         CE            => ce,
         A(0)          => addr,
         A(3 downto 1) => "000",
         Q             => pipe_sop_n_in
         );

   SRL16E_EOF_N_U : entity work.SRL_REG16
      port map (
         CLK           => CLK,
         DATA          => IN_EOF_N,
         CE            => ce,
         A(0)          => addr,
         A(3 downto 1) => "000",
         Q             => pipe_eop_n_in
         );

   SRL16E_DW4_N_U : entity work.SRL_REG16
      port map (
         CLK           => CLK,
         DATA          => IN_DW4,
         CE            => ce,
         A(0)          => addr,
         A(3 downto 1) => "000",
         Q             => OUT_DW4
         );
   -- -------------------------------------------------------------------------
   --                               OUTPUT REGISTER                          --
   -- -------------------------------------------------------------------------
   -- register pipe_reg -------------------------------------------------------
     pipe_regp: process(RESET, CLK)
       begin
          if (CLK'event AND CLK = '1') then
             if (RESET = '1') then
                OUT_DATA      <= (others => '0');
                OUT_SRC_RDY_N <= '1';
                aux_sop_n     <= '1';
                OUT_EOF_N     <= '1';
             elsif (OUT_DST_RDY_N = '0') then
                OUT_DATA      <= pipe_reg_in;
                OUT_SRC_RDY_N <= pipe_src_rdy_n_in;
                aux_sop_n     <= pipe_sop_n_in or pipe_src_rdy_n_in;
                OUT_EOF_N     <= pipe_eop_n_in or pipe_src_rdy_n_in;
             end if;
          end if;
       end process;
   OUT_SOF_N <= aux_sop_n;

   -- -------------------------------------------------------------------------
   --                          DW4 VLD COMPUTATION                               --
   -- -------------------------------------------------------------------------
   OUT_DW4_VLD <= '1' when (aux_sop_n ='0' and pipe_src_rdy_n_in='0') else '0';

   -- -------------------------------------------------------------------------
   --                              CONTROL FSM                               --
   -- -------------------------------------------------------------------------

   -- synchronize logic -------------------------------------------------------
   synchlogp : process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
        if (RESET = '1') then
          present_state <= S_0;
        else
          present_state <= next_state;
        end if;
      end if;
   end process;

   -- next state logic --------------------------------------------------------
   nextstatelogicp : process(present_state,IN_SRC_RDY_N,OUT_DST_RDY_N)
   begin
      next_state <= present_state;

      case (present_state) is

         when  S_0 =>
            if (IN_SRC_RDY_N = '0') then
               next_state <= S_1;
            end if;
         
         when  S_1 =>
            if (IN_SRC_RDY_N = '0') and (OUT_DST_RDY_N = '1') then
               next_state <= S_2;
            elsif (OUT_DST_RDY_N = '0') and (IN_SRC_RDY_N = '1') then
               next_state <= S_0;
            end if;
         
         when  S_2 =>
            if (OUT_DST_RDY_N = '0') then
               next_state <= S_1;
            end if;

      end case;
   end process;

   -- output logic ------------------------------------------------------------
   outputlogicp : process(present_state,IN_SRC_RDY_N)
   begin
      case (present_state) is
         when  S_0 =>
            ce                <= not IN_SRC_RDY_N;
            addr              <= '0';
            pipe_src_rdy_n_in <= '1';
            IN_DST_RDY_N      <= '0';
         when  S_1 =>
            ce                <= not IN_SRC_RDY_N;
            addr              <= '0';
            pipe_src_rdy_n_in <= '0';
            IN_DST_RDY_N      <= '0';
         when  S_2 =>
            ce                <= '0';
            addr              <= '1';
            pipe_src_rdy_n_in <= '0';
            IN_DST_RDY_N      <= '1';
      end case;
   end process;

   end architecture FULL;
