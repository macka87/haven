--
-- lb_endpoint.vhd: Internal Bus End Point Component CORE
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_ENDPOINT_CORE is
   generic(
      ADDR_WIDTH           : integer;
      INPUT_BUFFER_SIZE    : integer:=0;
      OUTPUT_BUFFER_SIZE   : integer:=0;
      READ_REORDER_BUFFER  : boolean:=true;
      WRITE_REORDER_BUFFER : boolean:=false;
      STRICT_EN            : boolean:=false; -- Eanble Strict version
      MASTER_EN            : boolean:=false  -- Master Endpoint
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
      WR_ADDR       : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      WR_DATA       : out std_logic_vector(63 downto 0);
      WR_BE         : out std_logic_vector(7 downto 0);
      WR_REQ        : out std_logic;
      WR_RDY        : in  std_logic;
      WR_LENGTH     : out std_logic_vector(11 downto 0);
      WR_SOF        : out std_logic;
      WR_EOF        : out std_logic;
      RD_BACK       : out std_logic;

      -- Read Interface
      -- Input Interface
      RD_ADDR          : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      RD_BE            : out std_logic_vector(7 downto 0);
      RD_REQ           : out std_logic;
      RD_ARDY          : in  std_logic;
      RD_SOF_IN        : out std_logic;
      RD_EOF_IN        : out std_logic;
      -- Output Interface
      RD_DATA          : in  std_logic_vector(63 downto 0);
      RD_SRC_RDY       : in  std_logic;
      RD_DST_RDY       : out std_logic;
      
      -- RD_WR Abort
      RD_WR_ABORT      : in  std_logic;

      -- Master Interface Input
      BM_GLOBAL_ADDR   : in  std_logic_vector(63 downto 0);   -- Global Address 
      BM_LOCAL_ADDR    : in  std_logic_vector(31 downto 0);   -- Local Address
      BM_LENGTH        : in  std_logic_vector(11 downto 0);   -- Length
      BM_TAG           : in  std_logic_vector(15 downto 0);   -- Operation TAG
      BM_TRANS_TYPE    : in  std_logic_vector(1 downto 0);    -- Transaction type
      BM_REQ           : in  std_logic;                       -- Request
      BM_ACK           : out std_logic;                       -- Ack

      -- Master Output interface
      BM_OP_TAG        : out std_logic_vector(15 downto 0);   -- Operation TAG
      BM_OP_DONE       : out std_logic                        -- Acknowledge
  );
end entity IB_ENDPOINT_CORE;
