--
-- dual_dec_8b10b.vhd: Dual-port 8b/10b decoder
-- Copyright (C) 2003 CESNET
-- Author(s): Petr Mikusek <xmikus01@stud.fit.vutbr.cz>
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

-- pragma translate_off
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity dual_dec_8b10b is
   port (
      CLK0      : in  std_logic;
      RESET0    : in  std_logic;
      DIN0      : in  std_logic_vector(9 downto 0);
      DOUT0     : out std_logic_vector(7 downto 0);
      K0        : out std_logic;
      INVALID0  : out std_logic;

      CLK1      : in  std_logic;
      RESET1    : in  std_logic;
      DIN1      : in  std_logic_vector(9 downto 0);
      DOUT1     : out std_logic_vector(7 downto 0);
      K1        : out std_logic;
      INVALID1  : out std_logic
   );
end dual_dec_8b10b;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of dual_dec_8b10b is

component RAMB16_S18_S18
-- pragma translate_off
   generic (
      WRITE_MODE_A : string := "NO_CHANGE";
      WRITE_MODE_B : string := "NO_CHANGE";
      INIT_A : bit_vector(17 downto 0)  := "00" & X"0a00";
      INIT_B : bit_vector(17 downto 0)  := "00" & X"0a00";
      SRVAL_A : bit_vector(17 downto 0)  := "00" & X"0a00";
      SRVAL_B : bit_vector(17 downto 0)  := "00" & X"0a00";

      INIT_00 : bit_vector(255 downto 0) :=
      X"0aff02ee02ed0ef802eb0eff0ef00eff02e70ee00eef0eff0ffc0fff0fff0fff";
      INIT_01 : bit_vector(255 downto 0) :=
      X"0bff0bfe0bfd03fc0bfb03fa03f90fe80bf703f603f50fe403f30fe20fe10fff";
      INIT_02 : bit_vector(255 downto 0) :=
      X"0aff0ae10ae202ec0ae402ea02e90ef70ae802e602e50efb02e30efd0efe0eff";
      INIT_03 : bit_vector(255 downto 0) :=
      X"0bff0bff0bff0bfc0aff0aef0ae002e70aff0af00aff02f40af802f202f10eff";
      INIT_04 : bit_vector(255 downto 0) :=
      X"0aff00ee00ed0ef800eb0eff0ef00eff02e70ee00eef0eff0ffc0fff0fff0fff";
      INIT_05 : bit_vector(255 downto 0) :=
      X"0bff09fe09fd03fc09fb03fa03f90fe809f703f603f50fe403f30fe20fe10fff";
      INIT_06 : bit_vector(255 downto 0) :=
      X"0aff0ae10ae202ec0ae402ea02e90ef70ae802e602e50efb02e30efd0efe0eff";
      INIT_07 : bit_vector(255 downto 0) :=
      X"0bff0bff0bff09fc0aff0aef0ae002e70aff0af00aff02f40af802f202f10eff";
      INIT_08 : bit_vector(255 downto 0) :=
      X"0a1f000e000d0e18000b0e1f0e100e1f02070e000e0f0e1f0f1c0f1f0f1f0f1f";
      INIT_09 : bit_vector(255 downto 0) :=
      X"0a1f081e081d001c081b001a00190e080817001600150e0400130e020e010e1f";
      INIT_0A : bit_vector(255 downto 0) :=
      X"0a1f08010802000c0804000a00090e170808000600050e1b00030e1d0e1e0e1f";
      INIT_0B : bit_vector(255 downto 0) :=
      X"0b1f0b1f0b1f091c0a1f080f080000070a1f0810081f00140818001200110e1f";
      INIT_0C : bit_vector(255 downto 0) :=
      X"067f086e086d0078086b007f0070027f08670060006f027f017c037f037f037f";
      INIT_0D : bit_vector(255 downto 0) :=
      X"067f067e067d087c067b087a087900680677087608750064087300620061027f";
      INIT_0E : bit_vector(255 downto 0) :=
      X"067f06610662086c0664086a08690077066808660865007b0863007d007e027f";
      INIT_0F : bit_vector(255 downto 0) :=
      X"077f077f077f077c067f066f06600a67067f0670067f0874067808720871027f";
      INIT_10 : bit_vector(255 downto 0) :=
      X"0a9f008e008d0e98008b0e9f0e900e9f02870e800e8f0e9f0f9c0f9f0f9f0f9f";
      INIT_11 : bit_vector(255 downto 0) :=
      X"0a9f089e089d009c089b009a00990e880897009600950e8400930e820e810e9f";
      INIT_12 : bit_vector(255 downto 0) :=
      X"0a9f08810882008c0884008a00890e970888008600850e9b00830e9d0e9e0e9f";
      INIT_13 : bit_vector(255 downto 0) :=
      X"0b9f0b9f0b9f099c0a9f088f088000870a9f0890089f00940898009200910e9f";
      INIT_14 : bit_vector(255 downto 0) :=
      X"06bf08ae08ad00b808ab00bf00b002bf08a700a000af02bf015c035f035f035f";
      INIT_15 : bit_vector(255 downto 0) :=
      X"06bf04be04bd08bc04bb08ba08b900a804b708b608b500a408b300a200a102bf";
      INIT_16 : bit_vector(255 downto 0) :=
      X"06bf04a104a208ac04a408aa08a900b704a808a608a500bb08a300bd00be02bf";
      INIT_17 : bit_vector(255 downto 0) :=
      X"07bf07bf07bf05bc06bf04af04a008a706bf04b004bf08b404b808b208b102bf";
      INIT_18 : bit_vector(255 downto 0) :=
      X"06df08ce08cd00d808cb00df00d002df08c700c000cf02df013c033f033f033f";
      INIT_19 : bit_vector(255 downto 0) :=
      X"06df04de04dd08dc04db08da08d900c804d708d608d500c408d300c200c102df";
      INIT_1A : bit_vector(255 downto 0) :=
      X"06df04c104c208cc04c408ca08c900d704c808c608c500db08c300dd00de02df";
      INIT_1B : bit_vector(255 downto 0) :=
      X"07df07df07df05dc06df04cf04c008c706df04d004df08d404d808d208d102df";
      INIT_1C : bit_vector(255 downto 0) :=
      X"0eff04ee04ed08f804eb08ff08f00aff04e708e008ef0aff0bfc0bff0bff0bff";
      INIT_1D : bit_vector(255 downto 0) :=
      X"0eff0efe0efd04fc0efb04fa04f908e80ef704f604f508e404f308e208e10aff";
      INIT_1E : bit_vector(255 downto 0) :=
      X"0eff0ee10ee204ec0ee404ea04e908f70ee804e604e508fb04e308fd08fe0aff";
      INIT_1F : bit_vector(255 downto 0) :=
      X"0fff0fff0fff0ffc0eff0eef0ee006e70eff0ef00eff06f40ef806f206f10aff";
      INIT_20 : bit_vector(255 downto 0) :=
      X"0aff02ee02ed0ef802eb0eff0ef00eff02e70ee00eef0eff0ffc0fff0fff0fff";
      INIT_21 : bit_vector(255 downto 0) :=
      X"0aff08fe08fd00fc08fb00fa00f90ee808f700f600f50ee400f30ee20ee10eff";
      INIT_22 : bit_vector(255 downto 0) :=
      X"0aff08e108e200ec08e400ea00e90ef708e800e600e50efb00e30efd0efe0eff";
      INIT_23 : bit_vector(255 downto 0) :=
      X"0bff0bff0bff0bfc0aff08ef08e000e70aff08f008ff00f408f800f200f10eff";
      INIT_24 : bit_vector(255 downto 0) :=
      X"063f082e082d0038082b003f0030023f08270020002f023f01dc03df03df03df";
      INIT_25 : bit_vector(255 downto 0) :=
      X"063f043e043d083c043b083a083900280437083608350024083300220021023f";
      INIT_26 : bit_vector(255 downto 0) :=
      X"063f04210422082c0424082a08290037042808260825003b0823003d003e023f";
      INIT_27 : bit_vector(255 downto 0) :=
      X"073f073f073f053c063f042f04200827063f0430043f0834043808320831023f";
      INIT_28 : bit_vector(255 downto 0) :=
      X"065f084e084d0058084b005f0050025f08470040004f025f01bc03bf03bf03bf";
      INIT_29 : bit_vector(255 downto 0) :=
      X"065f045e045d085c045b085a085900480457085608550044085300420041025f";
      INIT_2A : bit_vector(255 downto 0) :=
      X"065f04410442084c0444084a08490057044808460845005b0843005d005e025f";
      INIT_2B : bit_vector(255 downto 0) :=
      X"075f075f075f055c065f044f04400847065f0450045f0854045808520851025f";
      INIT_2C : bit_vector(255 downto 0) :=
      X"0e9f048e048d0898048b089f08900a9f04870880088f0a9f099c0b9f0b9f0b9f";
      INIT_2D : bit_vector(255 downto 0) :=
      X"0e9f0e9e0e9d049c0e9b049a049908880e970496049508840493088208810a9f";
      INIT_2E : bit_vector(255 downto 0) :=
      X"0e9f0e810e82048c0e84048a048908970e8804860485089b0483089d089e0a9f";
      INIT_2F : bit_vector(255 downto 0) :=
      X"0f9f0f9f0f9f0f9c0e9f0e8f0e8006870e9f0e900e9f04940e98049204910a9f";
      INIT_30 : bit_vector(255 downto 0) :=
      X"067f086e086d0278086b027f0270027f0a670260026f027f037c037f037f037f";
      INIT_31 : bit_vector(255 downto 0) :=
      X"067f047e047d087c047b087a087902680477087608750264087302620261027f";
      INIT_32 : bit_vector(255 downto 0) :=
      X"067f04610462086c0464086a08690277046808660865027b0863027d027e027f";
      INIT_33 : bit_vector(255 downto 0) :=
      X"077f077f077f057c067f046f04600867067f0470047f0874047808720871027f";
      INIT_34 : bit_vector(255 downto 0) :=
      X"0e1f040e040d0818040b081f08100a1f04070800080f0a1f091c0b1f0b1f0b1f";
      INIT_35 : bit_vector(255 downto 0) :=
      X"0e1f0e1e0e1d041c0e1b041a041908080e170416041508040413080208010a1f";
      INIT_36 : bit_vector(255 downto 0) :=
      X"0e1f0e010e02040c0e04040a040908170e0804060405081b0403081d081e0a1f";
      INIT_37 : bit_vector(255 downto 0) :=
      X"0f1f0f1f0f1f0f1c0e1f0e0f0e0006070e1f0e100e1f04140e18041204110a1f";
      INIT_38 : bit_vector(255 downto 0) :=
      X"0eff06ee06ed0af806eb0aff0af00aff06e70ae00aef0aff09fc0bff0bff0bff";
      INIT_39 : bit_vector(255 downto 0) :=
      X"0eff0efe0efd06fc0efb06fa06f90ae80ef706f606f50ae406f30ae20ae10aff";
      INIT_3A : bit_vector(255 downto 0) :=
      X"0fff0fe10fe207ec0fe407ea07e909f70fe807e607e509fb07e309fd09fe0bff";
      INIT_3B : bit_vector(255 downto 0) :=
      X"0fff0fff0fff0ffc0eff0eef0ee006e70eff0ef00eff04f40ef804f204f10aff";
      INIT_3C : bit_vector(255 downto 0) :=
      X"0eff06ee06ed0af806eb0aff0af00aff06e70ae00aef0aff0bfc0bff0bff0bff";
      INIT_3D : bit_vector(255 downto 0) :=
      X"0eff0efe0efd06fc0efb06fa06f90ae80ef706f606f50ae406f30ae20ae10aff";
      INIT_3E : bit_vector(255 downto 0) :=
      X"0fff0fe10fe207ec0fe407ea07e90bf70fe807e607e50bfb07e30bfd0bfe0bff";
      INIT_3F : bit_vector(255 downto 0) :=
      X"0fff0fff0fff0ffc0eff0eef0ee006e70eff0ef00eff06f40ef806f206f10aff"
   );
-- pragma translate_on
   port (
      DIA     : in std_logic_vector (15 downto 0);
      DIPA    : in std_logic_vector (1 downto 0);
      ADDRA   : in std_logic_vector (9 downto 0);
      ENA     : in std_logic;
      WEA     : in std_logic;
      SSRA    : in std_logic;
      CLKA    : in std_logic;
      DOA     : out std_logic_vector (15 downto 0);
      DOPA    : out std_logic_vector (1 downto 0);

      DIB     : in std_logic_vector (15 downto 0);
      DIPB    : in std_logic_vector (1 downto 0);
      ADDRB   : in std_logic_vector (9 downto 0);
      ENB     : in std_logic;
      WEB     : in std_logic;
      SSRB    : in std_logic;
      CLKB    : in std_logic;
      DOB     : out std_logic_vector (15 downto 0);
      DOPB    : out std_logic_vector (1 downto 0)
   );
end component;

attribute WRITE_MODE_A: string;
attribute WRITE_MODE_B: string;
attribute INIT_A: string;
attribute INIT_B: string;
attribute SRVAL_A: string;
attribute SRVAL_B: string;

attribute INIT_00: string;
attribute INIT_01: string;
attribute INIT_02: string;
attribute INIT_03: string;
attribute INIT_04: string;
attribute INIT_05: string;
attribute INIT_06: string;
attribute INIT_07: string;
attribute INIT_08: string;
attribute INIT_09: string;
attribute INIT_0A: string;
attribute INIT_0B: string;
attribute INIT_0C: string;
attribute INIT_0D: string;
attribute INIT_0E: string;
attribute INIT_0F: string;
attribute INIT_10: string;
attribute INIT_11: string;
attribute INIT_12: string;
attribute INIT_13: string;
attribute INIT_14: string;
attribute INIT_15: string;
attribute INIT_16: string;
attribute INIT_17: string;
attribute INIT_18: string;
attribute INIT_19: string;
attribute INIT_1A: string;
attribute INIT_1B: string;
attribute INIT_1C: string;
attribute INIT_1D: string;
attribute INIT_1E: string;
attribute INIT_1F: string;
attribute INIT_20: string;
attribute INIT_21: string;
attribute INIT_22: string;
attribute INIT_23: string;
attribute INIT_24: string;
attribute INIT_25: string;
attribute INIT_26: string;
attribute INIT_27: string;
attribute INIT_28: string;
attribute INIT_29: string;
attribute INIT_2A: string;
attribute INIT_2B: string;
attribute INIT_2C: string;
attribute INIT_2D: string;
attribute INIT_2E: string;
attribute INIT_2F: string;
attribute INIT_30: string;
attribute INIT_31: string;
attribute INIT_32: string;
attribute INIT_33: string;
attribute INIT_34: string;
attribute INIT_35: string;
attribute INIT_36: string;
attribute INIT_37: string;
attribute INIT_38: string;
attribute INIT_39: string;
attribute INIT_3A: string;
attribute INIT_3B: string;
attribute INIT_3C: string;
attribute INIT_3D: string;
attribute INIT_3E: string;
attribute INIT_3F: string;

attribute WRITE_MODE_A of U_RAMB16_S18_S18: label is "NO_CHANGE";
attribute WRITE_MODE_B of U_RAMB16_S18_S18: label is "NO_CHANGE";
attribute INIT_A of U_RAMB16_S18_S18: label is "00a00";
attribute INIT_B of U_RAMB16_S18_S18: label is "00a00";
attribute SRVAL_A of U_RAMB16_S18_S18: label is "00a00";
attribute SRVAL_B of U_RAMB16_S18_S18: label is "00a00";

attribute INIT_00 of U_RAMB16_S18_S18: label is
"0aff02ee02ed0ef802eb0eff0ef00eff02e70ee00eef0eff0ffc0fff0fff0fff";
attribute INIT_01 of U_RAMB16_S18_S18: label is
"0bff0bfe0bfd03fc0bfb03fa03f90fe80bf703f603f50fe403f30fe20fe10fff";
attribute INIT_02 of U_RAMB16_S18_S18: label is
"0aff0ae10ae202ec0ae402ea02e90ef70ae802e602e50efb02e30efd0efe0eff";
attribute INIT_03 of U_RAMB16_S18_S18: label is
"0bff0bff0bff0bfc0aff0aef0ae002e70aff0af00aff02f40af802f202f10eff";
attribute INIT_04 of U_RAMB16_S18_S18: label is
"0aff00ee00ed0ef800eb0eff0ef00eff02e70ee00eef0eff0ffc0fff0fff0fff";
attribute INIT_05 of U_RAMB16_S18_S18: label is
"0bff09fe09fd03fc09fb03fa03f90fe809f703f603f50fe403f30fe20fe10fff";
attribute INIT_06 of U_RAMB16_S18_S18: label is
"0aff0ae10ae202ec0ae402ea02e90ef70ae802e602e50efb02e30efd0efe0eff";
attribute INIT_07 of U_RAMB16_S18_S18: label is
"0bff0bff0bff09fc0aff0aef0ae002e70aff0af00aff02f40af802f202f10eff";
attribute INIT_08 of U_RAMB16_S18_S18: label is
"0a1f000e000d0e18000b0e1f0e100e1f02070e000e0f0e1f0f1c0f1f0f1f0f1f";
attribute INIT_09 of U_RAMB16_S18_S18: label is
"0a1f081e081d001c081b001a00190e080817001600150e0400130e020e010e1f";
attribute INIT_0A of U_RAMB16_S18_S18: label is
"0a1f08010802000c0804000a00090e170808000600050e1b00030e1d0e1e0e1f";
attribute INIT_0B of U_RAMB16_S18_S18: label is
"0b1f0b1f0b1f091c0a1f080f080000070a1f0810081f00140818001200110e1f";
attribute INIT_0C of U_RAMB16_S18_S18: label is
"067f086e086d0078086b007f0070027f08670060006f027f017c037f037f037f";
attribute INIT_0D of U_RAMB16_S18_S18: label is
"067f067e067d087c067b087a087900680677087608750064087300620061027f";
attribute INIT_0E of U_RAMB16_S18_S18: label is
"067f06610662086c0664086a08690077066808660865007b0863007d007e027f";
attribute INIT_0F of U_RAMB16_S18_S18: label is
"077f077f077f077c067f066f06600a67067f0670067f0874067808720871027f";
attribute INIT_10 of U_RAMB16_S18_S18: label is
"0a9f008e008d0e98008b0e9f0e900e9f02870e800e8f0e9f0f9c0f9f0f9f0f9f";
attribute INIT_11 of U_RAMB16_S18_S18: label is
"0a9f089e089d009c089b009a00990e880897009600950e8400930e820e810e9f";
attribute INIT_12 of U_RAMB16_S18_S18: label is
"0a9f08810882008c0884008a00890e970888008600850e9b00830e9d0e9e0e9f";
attribute INIT_13 of U_RAMB16_S18_S18: label is
"0b9f0b9f0b9f099c0a9f088f088000870a9f0890089f00940898009200910e9f";
attribute INIT_14 of U_RAMB16_S18_S18: label is
"06bf08ae08ad00b808ab00bf00b002bf08a700a000af02bf015c035f035f035f";
attribute INIT_15 of U_RAMB16_S18_S18: label is
"06bf04be04bd08bc04bb08ba08b900a804b708b608b500a408b300a200a102bf";
attribute INIT_16 of U_RAMB16_S18_S18: label is
"06bf04a104a208ac04a408aa08a900b704a808a608a500bb08a300bd00be02bf";
attribute INIT_17 of U_RAMB16_S18_S18: label is
"07bf07bf07bf05bc06bf04af04a008a706bf04b004bf08b404b808b208b102bf";
attribute INIT_18 of U_RAMB16_S18_S18: label is
"06df08ce08cd00d808cb00df00d002df08c700c000cf02df013c033f033f033f";
attribute INIT_19 of U_RAMB16_S18_S18: label is
"06df04de04dd08dc04db08da08d900c804d708d608d500c408d300c200c102df";
attribute INIT_1A of U_RAMB16_S18_S18: label is
"06df04c104c208cc04c408ca08c900d704c808c608c500db08c300dd00de02df";
attribute INIT_1B of U_RAMB16_S18_S18: label is
"07df07df07df05dc06df04cf04c008c706df04d004df08d404d808d208d102df";
attribute INIT_1C of U_RAMB16_S18_S18: label is
"0eff04ee04ed08f804eb08ff08f00aff04e708e008ef0aff0bfc0bff0bff0bff";
attribute INIT_1D of U_RAMB16_S18_S18: label is
"0eff0efe0efd04fc0efb04fa04f908e80ef704f604f508e404f308e208e10aff";
attribute INIT_1E of U_RAMB16_S18_S18: label is
"0eff0ee10ee204ec0ee404ea04e908f70ee804e604e508fb04e308fd08fe0aff";
attribute INIT_1F of U_RAMB16_S18_S18: label is
"0fff0fff0fff0ffc0eff0eef0ee006e70eff0ef00eff06f40ef806f206f10aff";
attribute INIT_20 of U_RAMB16_S18_S18: label is
"0aff02ee02ed0ef802eb0eff0ef00eff02e70ee00eef0eff0ffc0fff0fff0fff";
attribute INIT_21 of U_RAMB16_S18_S18: label is
"0aff08fe08fd00fc08fb00fa00f90ee808f700f600f50ee400f30ee20ee10eff";
attribute INIT_22 of U_RAMB16_S18_S18: label is
"0aff08e108e200ec08e400ea00e90ef708e800e600e50efb00e30efd0efe0eff";
attribute INIT_23 of U_RAMB16_S18_S18: label is
"0bff0bff0bff0bfc0aff08ef08e000e70aff08f008ff00f408f800f200f10eff";
attribute INIT_24 of U_RAMB16_S18_S18: label is
"063f082e082d0038082b003f0030023f08270020002f023f01dc03df03df03df";
attribute INIT_25 of U_RAMB16_S18_S18: label is
"063f043e043d083c043b083a083900280437083608350024083300220021023f";
attribute INIT_26 of U_RAMB16_S18_S18: label is
"063f04210422082c0424082a08290037042808260825003b0823003d003e023f";
attribute INIT_27 of U_RAMB16_S18_S18: label is
"073f073f073f053c063f042f04200827063f0430043f0834043808320831023f";
attribute INIT_28 of U_RAMB16_S18_S18: label is
"065f084e084d0058084b005f0050025f08470040004f025f01bc03bf03bf03bf";
attribute INIT_29 of U_RAMB16_S18_S18: label is
"065f045e045d085c045b085a085900480457085608550044085300420041025f";
attribute INIT_2A of U_RAMB16_S18_S18: label is
"065f04410442084c0444084a08490057044808460845005b0843005d005e025f";
attribute INIT_2B of U_RAMB16_S18_S18: label is
"075f075f075f055c065f044f04400847065f0450045f0854045808520851025f";
attribute INIT_2C of U_RAMB16_S18_S18: label is
"0e9f048e048d0898048b089f08900a9f04870880088f0a9f099c0b9f0b9f0b9f";
attribute INIT_2D of U_RAMB16_S18_S18: label is
"0e9f0e9e0e9d049c0e9b049a049908880e970496049508840493088208810a9f";
attribute INIT_2E of U_RAMB16_S18_S18: label is
"0e9f0e810e82048c0e84048a048908970e8804860485089b0483089d089e0a9f";
attribute INIT_2F of U_RAMB16_S18_S18: label is
"0f9f0f9f0f9f0f9c0e9f0e8f0e8006870e9f0e900e9f04940e98049204910a9f";
attribute INIT_30 of U_RAMB16_S18_S18: label is
"067f086e086d0278086b027f0270027f0a670260026f027f037c037f037f037f";
attribute INIT_31 of U_RAMB16_S18_S18: label is
"067f047e047d087c047b087a087902680477087608750264087302620261027f";
attribute INIT_32 of U_RAMB16_S18_S18: label is
"067f04610462086c0464086a08690277046808660865027b0863027d027e027f";
attribute INIT_33 of U_RAMB16_S18_S18: label is
"077f077f077f057c067f046f04600867067f0470047f0874047808720871027f";
attribute INIT_34 of U_RAMB16_S18_S18: label is
"0e1f040e040d0818040b081f08100a1f04070800080f0a1f091c0b1f0b1f0b1f";
attribute INIT_35 of U_RAMB16_S18_S18: label is
"0e1f0e1e0e1d041c0e1b041a041908080e170416041508040413080208010a1f";
attribute INIT_36 of U_RAMB16_S18_S18: label is
"0e1f0e010e02040c0e04040a040908170e0804060405081b0403081d081e0a1f";
attribute INIT_37 of U_RAMB16_S18_S18: label is
"0f1f0f1f0f1f0f1c0e1f0e0f0e0006070e1f0e100e1f04140e18041204110a1f";
attribute INIT_38 of U_RAMB16_S18_S18: label is
"0eff06ee06ed0af806eb0aff0af00aff06e70ae00aef0aff09fc0bff0bff0bff";
attribute INIT_39 of U_RAMB16_S18_S18: label is
"0eff0efe0efd06fc0efb06fa06f90ae80ef706f606f50ae406f30ae20ae10aff";
attribute INIT_3A of U_RAMB16_S18_S18: label is
"0fff0fe10fe207ec0fe407ea07e909f70fe807e607e509fb07e309fd09fe0bff";
attribute INIT_3B of U_RAMB16_S18_S18: label is
"0fff0fff0fff0ffc0eff0eef0ee006e70eff0ef00eff04f40ef804f204f10aff";
attribute INIT_3C of U_RAMB16_S18_S18: label is
"0eff06ee06ed0af806eb0aff0af00aff06e70ae00aef0aff0bfc0bff0bff0bff";
attribute INIT_3D of U_RAMB16_S18_S18: label is
"0eff0efe0efd06fc0efb06fa06f90ae80ef706f606f50ae406f30ae20ae10aff";
attribute INIT_3E of U_RAMB16_S18_S18: label is
"0fff0fe10fe207ec0fe407ea07e90bf70fe807e607e50bfb07e30bfd0bfe0bff";
attribute INIT_3F of U_RAMB16_S18_S18: label is
"0fff0fff0fff0ffc0eff0eef0ee006e70eff0ef00eff06f40ef806f206f10aff";

   constant C_NEG     : std_logic_vector(1 downto 0) := "00";
   constant C_POS     : std_logic_vector(1 downto 0) := "01";
   constant C_ZERO    : std_logic_vector(1 downto 0) := "10";
   constant C_INVALID : std_logic_vector(1 downto 0) := "11";

   signal vcc : std_logic;
   signal gnd : std_logic;
   signal ramb_di  : std_logic_vector(15 downto 0);
   signal ramb_dip : std_logic_vector(1 downto 0);

   signal sym_disp_0     : std_logic_vector(1 downto 0);
   signal cur_sym_disp_0 : std_logic_vector(1 downto 0);
   signal disp_0         : std_logic;
   signal disp_last_0    : std_logic;
   signal disp_error_0   : std_logic;
   signal code_error_0   : std_logic;
   signal ramb_do_0      : std_logic_vector(15 downto 0);

   signal sym_disp_1     : std_logic_vector(1 downto 0);
   signal cur_sym_disp_1 : std_logic_vector(1 downto 0);
   signal disp_1         : std_logic;
   signal disp_last_1    : std_logic;
   signal disp_error_1   : std_logic;
   signal code_error_1   : std_logic;
   signal ramb_do_1      : std_logic_vector(15 downto 0);

begin
   vcc <= '1';
   gnd <= '0';
   ramb_di   <= (others => '1');
   ramb_dip  <= "11";

   U_RAMB16_S18_S18: RAMB16_S18_S18
      port map (
         DIA     => ramb_di,
         DIPA    => ramb_dip,
         ADDRA   => DIN0,
         ENA     => vcc,
         WEA     => gnd,
         SSRA    => RESET0,
         CLKA    => CLK0,
         DOA     => ramb_do_0,
         DOPA    => open,

         DIB     => ramb_di,
         DIPB    => ramb_dip,
         ADDRB   => DIN1,
         ENB     => vcc,
         WEB     => gnd,
         SSRB    => RESET1,
         CLKB    => CLK1,
         DOB     => ramb_do_1,
         DOPB    => open
      );

   DOUT0 <= ramb_do_0(7 downto 0);
   K0 <= ramb_do_0(8);
   code_error_0 <= ramb_do_0(9);
   cur_sym_disp_0 <= ramb_do_0(11 downto 10);
   INVALID0 <= code_error_0 or disp_error_0;

   DOUT1 <= ramb_do_1(7 downto 0);
   K1 <= ramb_do_1(8);
   code_error_1 <= ramb_do_1(9);
   cur_sym_disp_1 <= ramb_do_1(11 downto 10);
   INVALID1 <= code_error_1 or disp_error_1;

   P_SYM_DISP_0: process (RESET0, CLK0)
   begin
      if (RESET0 = '1') then
         sym_disp_0 <= "10";
      else
         if (CLK0'event and CLK0 = '1') then
            sym_disp_0 <= cur_sym_disp_0;
         end if;
      end if;
   end process;

   P_SYM_DISP_1: process (RESET1, CLK1)
   begin
      if (RESET1 = '1') then
         sym_disp_1 <= "10";
      else
         if (CLK1'event and CLK1 = '1') then
            sym_disp_1 <= cur_sym_disp_1;
         end if;
      end if;
   end process;

   P_DISP_LAST_0: process (RESET0, CLK0)
   begin
      if (RESET0 = '1') then
         disp_last_0 <= '0';
      else
         if (CLK0'event and CLK0 = '1') then
            if (sym_disp_0 = C_POS or sym_disp_0 = C_NEG) then
               disp_last_0 <= sym_disp_0(0);
            end if;
         end if;
      end if;
   end process;

   P_DISP_LAST_1: process (RESET1, CLK1)
   begin
      if (RESET1 = '1') then
         disp_last_1 <= '0';
      else
         if (CLK1'event and CLK1 = '1') then
            if (sym_disp_1 = C_POS or sym_disp_1 = C_NEG) then
               disp_last_1 <= sym_disp_1(0);
            end if;
         end if;
      end if;
   end process;

   P_DISP_0: process (sym_disp_0, disp_last_0)
   begin
      if (sym_disp_0 = C_NEG) then
         disp_0 <= '0';
      elsif (sym_disp_0 = C_POS) then
         disp_0 <= '1';
      else
         disp_0 <= disp_last_0;
      end if;
   end process;

   P_DISP_1: process (sym_disp_1, disp_last_1)
   begin
      if (sym_disp_1 = C_NEG) then
         disp_1 <= '0';
      elsif (sym_disp_1 = C_POS) then
         disp_1 <= '1';
      else
         disp_1 <= disp_last_1;
      end if;
   end process;

   P_DISP_ERROR_0: process (sym_disp_0, disp_last_0)
   begin
      if (sym_disp_0(1) = '0') then
         if (sym_disp_0(0) = disp_last_0) then
            disp_error_0 <= '1';
         else
            disp_error_0 <= '0';
         end if;
      else
         disp_error_0 <= sym_disp_0(0);
      end if;
   end process;

   P_DISP_ERROR_1: process (sym_disp_1, disp_last_1)
   begin
      if (sym_disp_1(1) = '0') then
         if (sym_disp_1(0) = disp_last_1) then
            disp_error_1 <= '1';
         else
            disp_error_1 <= '0';
         end if;
      else
         disp_error_1 <= sym_disp_1(0);
      end if;
   end process;

end behavioral;

