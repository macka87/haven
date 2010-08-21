-- ib_endpoint_norec.vhd: Internal Bus End Point Component
--                               VHDL wrapper without records
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
use work.ib_pkg.all; -- Internal Bus package
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_ENDPOINT_NOREC is
   generic(
      LIMIT               : std_logic_vector(31 downto 0):=X"10000000";
      INPUT_BUFFER_SIZE   : integer:=0;
      OUTPUT_BUFFER_SIZE  : integer:=0;
      READ_REORDER_BUFFER : boolean:=true;
      STRICT_EN           : boolean:=false -- Eanble Strict version
   );
   port(
      -- Common Interface
      IB_CLK        : in std_logic;
      IB_RESET      : in std_logic;
      
      -- Internal Bus Interface
      -- DOWNSTREAM
      IB_DOWN_DATA        : in  std_logic_vector(63 downto 0);
      IB_DOWN_SOP_N       : in  std_logic;
      IB_DOWN_EOP_N       : in  std_logic;
      IB_DOWN_SRC_RDY_N   : in  std_logic;
      IB_DOWN_DST_RDY_N   : out std_logic;
        -- UPSTREAM
      IB_UP_DATA          : out std_logic_vector(63 downto 0);
      IB_UP_SOP_N         : out std_logic;
      IB_UP_EOP_N         : out std_logic;
      IB_UP_SRC_RDY_N     : out std_logic;
      IB_UP_DST_RDY_N     : in  std_logic;

      -- Write Interface
      WR_ADDR       : out std_logic_vector(31 downto 0);
      WR_DATA       : out std_logic_vector(63 downto 0);
      WR_BE         : out std_logic_vector(7 downto 0);
      WR_REQ        : out std_logic;
      WR_RDY        : in  std_logic;
      WR_LENGTH     : out std_logic_vector(11 downto 0);
      WR_SOF        : out std_logic;
      WR_EOF        : out std_logic;

      -- Read Interface
      -- Input Interface
      RD_ADDR          : out std_logic_vector(31 downto 0);
      RD_BE            : out std_logic_vector(7 downto 0);
      RD_REQ           : out std_logic;
      RD_ARDY          : in  std_logic;
      RD_SOF_IN        : out std_logic;
      RD_EOF_IN        : out std_logic;
      -- Output Interface
      RD_DATA          : in  std_logic_vector(63 downto 0);
      RD_SRC_RDY       : in  std_logic;
      RD_DST_RDY       : out std_logic
  );
end entity IB_ENDPOINT_NOREC;

architecture FULL of IB_ENDPOINT_NOREC is

   signal reset_pipe   : std_logic;

begin

WR_ADDR(31 downto log2(LIMIT)) <= (others => '0');
RD_ADDR(31 downto log2(LIMIT)) <= (others => '0');

-- ----------------------------------------------------------------------------
RESET_PIPE_P : process(IB_RESET, IB_CLK)
   begin
      if IB_CLK'event and IB_CLK = '1' then
         reset_pipe  <= IB_RESET;
      end if;
end process;

-- -----------------------Portmaping of tested component-----------------------
IB_ENDPOINT_CORE_U: entity work.IB_ENDPOINT_CORE
   generic map (
      ADDR_WIDTH          => log2(LIMIT),
      INPUT_BUFFER_SIZE   => INPUT_BUFFER_SIZE,
      OUTPUT_BUFFER_SIZE  => OUTPUT_BUFFER_SIZE,
      READ_REORDER_BUFFER => READ_REORDER_BUFFER,
      STRICT_EN           => STRICT_EN,
      MASTER_EN           => false  -- Master Endpoint
   )
   port map (
      -- Common Interface
      IB_CLK             => IB_CLK,
      IB_RESET           => reset_pipe,

      -- Internal Bus Interface
        -- DOWNSTREAM
      IB_DOWN_DATA       => IB_DOWN_DATA,
      IB_DOWN_SOP_N      => IB_DOWN_SOP_N,
      IB_DOWN_EOP_N      => IB_DOWN_EOP_N,
      IB_DOWN_SRC_RDY_N  => IB_DOWN_SRC_RDY_N,
      IB_DOWN_DST_RDY_N  => IB_DOWN_DST_RDY_N,
        -- UPSTREAM
      IB_UP_DATA         => IB_UP_DATA,
      IB_UP_SOP_N        => IB_UP_SOP_N,
      IB_UP_EOP_N        => IB_UP_EOP_N,
      IB_UP_SRC_RDY_N    => IB_UP_SRC_RDY_N,
      IB_UP_DST_RDY_N    => IB_UP_DST_RDY_N,

      -- Write Interface   
      WR_ADDR            => WR_ADDR(log2(LIMIT)-1 downto 0),
      WR_DATA            => WR_DATA,
      WR_BE              => WR_BE,
      WR_REQ             => WR_REQ,
      WR_RDY             => WR_RDY,
      WR_LENGTH          => WR_LENGTH,
      WR_SOF             => WR_SOF,
      WR_EOF             => WR_EOF,

      -- Read Interface
      RD_ADDR            => RD_ADDR(log2(LIMIT)-1 downto 0),
      RD_BE              => RD_BE,
      RD_REQ             => RD_REQ,
      RD_ARDY            => RD_ARDY,
      RD_SOF_IN          => RD_SOF_IN,
      RD_EOF_IN          => RD_EOF_IN,
      RD_DATA            => RD_DATA,
      RD_SRC_RDY         => RD_SRC_RDY,
      RD_DST_RDY         => RD_DST_RDY,

      -- RD_WR Abort
      RD_WR_ABORT        => '0',

      -- Master Interface Input
      BM_GLOBAL_ADDR     => (others => '0'), 
      BM_LOCAL_ADDR      => (others => '0'), 
      BM_LENGTH          => (others => '0'), 
      BM_TAG             => (others => '0'),
      BM_TRANS_TYPE      => "00",
      BM_REQ             => '0', 
      BM_ACK             => open,

      -- Master Output interface
      BM_OP_TAG          => open,
      BM_OP_DONE         => open
  );



end architecture FULL;
