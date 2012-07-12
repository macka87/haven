--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    HAVEN constants
-- Description:  Contains a package with various HAVEN constants
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- --------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;

package haven_const is

   -- ATTENTION! ------------------------------------------------
   -- X"00000000" to X"00020000" and
   -- X"02000000" to X"FFFFFFFF"
   -- are reserved for NetCOPE purposes
   -- use X"00020000" to X"02000000" for application (NetCOPE plugin)

   -- see https://merlin.fit.vutbr.cz/wiki-haven/index.php/Address_spaces
   -- for an up-to-date address space

   --------------------------------------------------------------------------
   --                         TYPES OF DESIGNS
   --------------------------------------------------------------------------

   type core_type is (core_fifo, core_err_fifo, core_hgen_1x, core_hgen_2x,
      core_hgen_4x, core_hgen_8x, core_hgen_16x);

   --------------------------------------------------------------------------
   --                            PROTOCOLS
   --------------------------------------------------------------------------

   -- ---------------------- INPUT PROTOCOLS --------------------------------
   -- input FrameLink
   constant PROTO_IN_FRAMELINK       : std_logic_vector(7 downto 0) := X"00";

   -- --------------------- OUTPUT PROTOCOLS --------------------------------
   -- output FrameLink
   constant PROTO_OUT_FRAMELINK      : std_logic_vector(7 downto 0) := X"80";
   -- FrameLink signal observer
   constant PROTO_OUT_FL_SIG_OBS     : std_logic_vector(7 downto 0) := X"8B";
   -- FrameLink validity checker
   constant PROTO_OUT_FL_VAL_CHECKER : std_logic_vector(7 downto 0) := X"90";

   --------------------------------------------------------------------------
   --                           ENDPOINT IDs
   --------------------------------------------------------------------------

   -- The FrameLink random generator
   constant ENDPOINT_ID_FL_RAND_GEN  : std_logic_vector(7 downto 0) := X"F6";

   -- The monitor
   constant ENDPOINT_ID_MONITOR      : std_logic_vector(7 downto 0) := X"88";
   -- The validity checker
   constant ENDPOINT_ID_VAL_CHECKER  : std_logic_vector(7 downto 0) := X"AA";
   -- The signal observer
   constant ENDPOINT_ID_SIG_OBSERV   : std_logic_vector(7 downto 0) := X"BB";

end haven_const;

package body haven_const is
end haven_const;

