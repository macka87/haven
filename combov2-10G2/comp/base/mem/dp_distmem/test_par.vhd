--
-- test_par.vhd: Parameters for test_dp_distmem.vhd testing
-- Copyright (C) 2005 CESNET
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
-- README: This file is very useful for simulations of dp_distmem
--         You can change constants and both simulations (PaR, behavioral)
--         will simulate dp_distmem component with this generic parameters.
--         You may only change simulation time in test_dp_distmem.fdo and
--         test_dp_distmem.tdo.
-- 
-- 
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use WORK.distmem_func.all; -- functions for enumerating generic parameters

-- ----------------------------------------------------------------------------
--                        Package declaration
-- ----------------------------------------------------------------------------
Package TEST_PAR is

--Parameters for simulation PaR and Behavioral...
constant TEST_DISTMEM_TYPE : integer := 32; -- only 16, 32, 64
constant TEST_DATA_WIDTH   : integer := 4;
constant TEST_ITEMS        : integer := 16;-- item size = DATA_WIDTH
constant TEST_DEBUG        : boolean := true;

end TEST_PAR;
