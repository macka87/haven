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
      LIMIT               : std_logic_vector(31 downto 0);
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
   
begin


end architecture IB_ENDPOINT_ARCH;
