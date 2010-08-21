--
-- lb_endpoint.vhd: Internal Bus End Point Component
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
entity IB_ENDPOINT is
   generic(
      LIMIT               : std_logic_vector(31 downto 0):=X"00000100";
      INPUT_BUFFER_SIZE   : integer:=0;
      OUTPUT_BUFFER_SIZE  : integer:=0;
      READ_REORDER_BUFFER : boolean:=true;
      STRICT_EN           : boolean:=false  -- Eanble Strict version
    );
   port(
      -- Common Interface
      IB_CLK        : in std_logic;
      IB_RESET      : in std_logic;
      
      -- Internal Bus Interface
      INTERNAL_BUS  : inout t_internal_bus64;
      
      -- User Component Interface
      WR            : inout t_ibmi_write64;
      RD            : inout t_ibmi_read64s
  );
end entity IB_ENDPOINT;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_ENDPOINT_ARCH of IB_ENDPOINT is
  
      signal reset_pipe : std_logic;
      attribute equivalent_register_removal : string;
      attribute equivalent_register_removal of reset_pipe : signal is "no";

begin

WR.ADDR(31 downto log2(LIMIT)) <= (others => '0');
RD.ADDR(31 downto log2(LIMIT)) <= (others => '0');

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
      IB_DOWN_DATA       => INTERNAL_BUS.DOWN.DATA,
      IB_DOWN_SOP_N      => INTERNAL_BUS.DOWN.SOP_N,
      IB_DOWN_EOP_N      => INTERNAL_BUS.DOWN.EOP_N,
      IB_DOWN_SRC_RDY_N  => INTERNAL_BUS.DOWN.SRC_RDY_N,
      IB_DOWN_DST_RDY_N  => INTERNAL_BUS.DOWN.DST_RDY_N,
        -- UPSTREAM
      IB_UP_DATA         => INTERNAL_BUS.UP.DATA,
      IB_UP_SOP_N        => INTERNAL_BUS.UP.SOP_N,
      IB_UP_EOP_N        => INTERNAL_BUS.UP.EOP_N,
      IB_UP_SRC_RDY_N    => INTERNAL_BUS.UP.SRC_RDY_N,
      IB_UP_DST_RDY_N    => INTERNAL_BUS.UP.DST_RDY_N,

      -- Write Interface   
      WR_ADDR            => WR.ADDR(log2(LIMIT)-1 downto 0),
      WR_DATA            => WR.DATA,
      WR_BE              => WR.BE,
      WR_REQ             => WR.REQ,
      WR_RDY             => WR.RDY,
      WR_LENGTH          => WR.LENGTH,
      WR_SOF             => WR.SOF,
      WR_EOF             => WR.EOF,

      -- Read Interface
      RD_ADDR            => RD.ADDR(log2(LIMIT)-1 downto 0),
      RD_BE              => RD.BE,
      RD_REQ             => RD.REQ,
      RD_ARDY            => RD.ARDY,
      RD_SOF_IN          => RD.SOF_IN,
      RD_EOF_IN          => RD.EOF_IN,
      RD_DATA            => RD.DATA,
      RD_SRC_RDY         => RD.SRC_RDY,
      RD_DST_RDY         => RD.DST_RDY,

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

end architecture IB_ENDPOINT_ARCH;
