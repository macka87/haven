
-- aurvc_pkg.vhd: Aurvc package 
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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
-- TODO: - 
library IEEE;
use IEEE.std_logic_1164.all;

package aurvc_pkg is

   constant C_XON  : std_logic := '1';
   constant C_XOFF : std_logic := '0';

   type t_aurvc_txbuf_param is record
      CHANNEL_SIZE         : integer;     -- Number of items in channel buffer
      BYTE_QUOTA           : integer;     -- Byte quota for this channel (see documentation for more information)
   end record;
   
   type t_aurvc_txbuf_param_arr is array (0 to 7) of t_aurvc_txbuf_param;

   type t_aurvc_rxbuf_param is record
      CHANNEL_SIZE         : integer;     -- Number of items in channel buffer
      XON_LIMIT            : std_logic_vector(2 downto 0);  -- XON limit for this channel (see documentation for more information)
      XOFF_LIMIT           : std_logic_vector(2 downto 0);  -- XOFF limit for this channel (see documentation for more information)
      RX_IS_HEADER         : boolean;                       -- Channel includes header
      RX_IS_FOOTER         : boolean;                       -- Channel includes footer
   end record;

   type t_aurvc_rxbuf_param_arr is array (0 to 7) of t_aurvc_rxbuf_param;

   type t_aurvc_buffers_param is record
       TXBUF_PARAMS : t_aurvc_txbuf_param_arr;
       RXBUF_PARAMS : t_aurvc_rxbuf_param_arr;
   end record;
   
end aurvc_pkg;

package body aurvc_pkg is
end aurvc_pkg;
 

