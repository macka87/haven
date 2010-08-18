--
-- pipe_wr.vhd: Internal Bus Write interface Pipeline
-- Copyright (C) 2008 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--               ENTITY DECLARATION -- Internal Bus Pipeline                 --
-- ---------------------------------------------------------------------------- 

entity IB_PIPE_WR is
   generic(
      -- Write data interface data Width
      DATA_WIDTH     : integer:= 64
   );   
   port(
      -- Common interface -----------------------------------------------------
      CLK            : in std_logic;
      RESET          : in std_logic;
      
      -- Input interface ------------------------------------------------------
      IN_ADDR        : in std_logic_vector(31 downto 0);
      IN_DATA        : in std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_BE          : in std_logic_vector((DATA_WIDTH/8)-1 downto 0);
      IN_REQ         : in std_logic;
      IN_RDY         : out std_logic;
      IN_LENGTH      : in std_logic_vector(11 downto 0);
      IN_SOF         : in std_logic;
      IN_EOF         : in std_logic;
 
      -- Output interface -----------------------------------------------------
      OUT_ADDR       : out std_logic_vector(31 downto 0);
      OUT_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_BE         : out std_logic_vector((DATA_WIDTH/8)-1 downto 0);
      OUT_REQ        : out std_logic;
      OUT_RDY        : in  std_logic;
      OUT_LENGTH     : out std_logic_vector(11 downto 0);
      OUT_SOF        : out std_logic;
      OUT_EOF        : out std_logic
   );
end entity IB_PIPE_WR;


-- ----------------------------------------------------------------------------
--             ARCHITECTURE DECLARATION  --  Internal Bus Pipeline           --
-- ----------------------------------------------------------------------------
architecture ib_pipe_wr_arch of IB_PIPE_WR is
   constant PIPE_WIDTH        : integer := 32+DATA_WIDTH+(DATA_WIDTH/8)+12;

   signal pipe_in_data        : std_logic_vector(PIPE_WIDTH-1 downto 0);
   signal pipe_in_sof_n       : std_logic;
   signal pipe_in_eof_n       : std_logic;
   signal pipe_in_src_rdy_n   : std_logic;
   signal pipe_in_dst_rdy_n   : std_logic;

   signal pipe_out_data       : std_logic_vector(PIPE_WIDTH-1 downto 0);
   signal pipe_out_sof_n      : std_logic;
   signal pipe_out_eof_n      : std_logic;
   signal pipe_out_src_rdy_n  : std_logic;
   signal pipe_out_dst_rdy_n  : std_logic;
begin
   pipe_in_data   <= IN_LENGTH & IN_BE & IN_DATA & IN_ADDR;
   pipe_in_sof_n  <= not IN_SOF;
   pipe_in_eof_n  <= not IN_EOF;
   pipe_in_src_rdy_n <= not IN_REQ;
   IN_RDY         <= not pipe_in_dst_rdy_n;

   OUT_ADDR       <= pipe_out_data(31 downto 0);
   OUT_DATA       <= pipe_out_data(32+DATA_WIDTH-1 downto 32);
   OUT_BE         <= pipe_out_data(32+DATA_WIDTH+(DATA_WIDTH/8)-1 
                     downto 32+DATA_WIDTH);
   OUT_REQ        <= not pipe_out_src_rdy_n;
   pipe_out_dst_rdy_n <= not OUT_RDY;
   OUT_LENGTH     <= pipe_out_data(32+DATA_WIDTH+(DATA_WIDTH/8)+12-1 
                     downto 32+DATA_WIDTH+(DATA_WIDTH/8));
   OUT_SOF        <= not pipe_out_sof_n;
   OUT_EOF        <= not pipe_out_eof_n;


   IB_PIPE_I: entity work.IB_PIPE
      generic map(
         -- Data Width (1-128)
         DATA_WIDTH     => PIPE_WIDTH
      )
      port map(
         -- Common interface -----------------------------------------------------
         CLK            => CLK,
         RESET          => RESET,
         -- Input interface ------------------------------------------------------
         IN_DATA        => pipe_in_data,
         IN_SOF_N       => pipe_in_sof_n,
         IN_EOF_N       => pipe_in_eof_n,
         IN_SRC_RDY_N   => pipe_in_src_rdy_n,
         IN_DST_RDY_N   => pipe_in_dst_rdy_n,
         -- Output interface -----------------------------------------------------
         OUT_DATA       => pipe_out_data,
         OUT_SOF_N      => pipe_out_sof_n,
         OUT_EOF_N      => pipe_out_eof_n,
         OUT_SRC_RDY_N  => pipe_out_src_rdy_n,
         OUT_DST_RDY_N  => pipe_out_dst_rdy_n
      );

end ib_pipe_wr_arch;

