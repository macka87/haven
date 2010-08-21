-- desc_manager_wrapper.vhd: Simple VHDL wrapper.
-- Copyright (C) 2008 CESNET
-- Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
--
-- $Id$
--
--

library IEEE;
use IEEE.std_logic_1164.all;
-- use ieee.std_logic_arith.all;
use ieee.numeric_std.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity desc_manager_wrapper is
   generic(
      -- local base address
      VLOG_BASE_ADDR    : integer := 0;
      -- number of connected controlers (TX + RX)
      FLOWS             : integer := 32;
      -- number of descriptors. In scheme DOWNLOADED_BLOCK_SIZE. 
      -- Must be 2**N
      BLOCK_SIZE        : integer := 32
   );
   port(
      -- Common interface
      CLK               : in std_logic;
      RESET             : in std_logic;

      -- Memory interface (InternalBus)
      -- Write interface
      WR_ADDR           : in std_logic_vector(31 downto 0);
      WR_DATA           : in std_logic_vector(63 downto 0);
      WR_BE             : in std_logic_vector(7 downto 0);
      WR_REQ            : in std_logic;
      WR_RDY            : out std_logic;
--       -- Read interface
--       RD_ADDR           : in  std_logic_vector(31 downto 0);
--       RD_BE             : in  std_logic_vector(7 downto 0);
--       RD_REQ            : in  std_logic;
--       RD_ARDY           : out std_logic;
--       RD_DATA           : out std_logic_vector(63 downto 0);
--       RD_SRC_RDY        : out std_logic;
--       RD_DST_RDY        : in  std_logic;

      -- BM Interface 
      BM_GLOBAL_ADDR    : out std_logic_vector(63 downto 0); 
      BM_LOCAL_ADDR     : out std_logic_vector(31 downto 0); 
      BM_LENGTH         : out std_logic_vector(11 downto 0); 
      BM_TAG            : out std_logic_vector(15 downto 0); 
      BM_TRANS_TYPE     : out std_logic_vector(3 downto 0);  
      BM_REQ            : out std_logic;                     
      BM_ACK            : in std_logic;                     
      BM_OP_TAG         : in std_logic_vector(15 downto 0); -- NOT USED!
      BM_OP_DONE        : in std_logic;                     -- NOT USED!  

      -- DMA ctrls interface
      DATA_OUT          : out std_logic_vector(63 downto 0);
      EMPTY             : out std_logic_vector(FLOWS-1 downto 0); -- not DATA_VLD
      READ              : in  std_logic_vector(FLOWS-1 downto 0);

      -- Per channel enable interface
      ENABLE            : in std_logic_vector(FLOWS-1 downto 0) 
   );
end entity desc_manager_wrapper;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture fake of desc_manager_wrapper is
begin
vhdl_desc_manager_bm : entity work.desc_manager_bm
  generic map (
    BASE_ADDR  => std_logic_vector(to_unsigned(VLOG_BASE_ADDR, 32)),
    FLOWS      => FLOWS,
    BLOCK_SIZE => BLOCK_SIZE
  )
  port map (
    CLK            => CLK,
    RESET          => RESET,
    
    WR_ADDR        => WR_ADDR,
    WR_DATA        => WR_DATA,
    WR_BE          => WR_BE,
    WR_REQ         => WR_REQ,
    WR_RDY         => WR_RDY,
    
    BM_GLOBAL_ADDR => BM_GLOBAL_ADDR,
    BM_LOCAL_ADDR  => BM_LOCAL_ADDR,
    BM_LENGTH      => BM_LENGTH,
    BM_TAG         => BM_TAG,
    BM_TRANS_TYPE  => BM_TRANS_TYPE,
    BM_REQ         => BM_REQ,
    BM_ACK         => BM_ACK,
    BM_OP_TAG      => BM_OP_TAG,
    BM_OP_DONE     => BM_OP_DONE,
    
    DATA_OUT       => DATA_OUT,
    EMPTY          => EMPTY,
    READ           => READ,
    
    ENABLE         => ENABLE
  );
end architecture;
