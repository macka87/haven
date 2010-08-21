--
-- dual_enc_8b10b.vhd: Dual-port 8b/10b encoder
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
entity dual_enc_8b10b is
   port (
      CLK0        : in  std_logic;
      RESET0      : in  std_logic;
      DIN0        : in  std_logic_vector(7 downto 0);
      KIN0        : in  std_logic;
      DISP_IN0    : in  std_logic;
      FORCE_DISP0 : in  std_logic;
      DOUT0       : out std_logic_vector(9 downto 0);
      DISP_OUT0   : out std_logic;
      KERR0       : out std_logic;

      CLK1        : in  std_logic;
      RESET1      : in  std_logic;
      DIN1        : in  std_logic_vector(7 downto 0);
      KIN1        : in  std_logic;
      DISP_IN1    : in  std_logic;
      FORCE_DISP1 : in  std_logic;
      DOUT1       : out std_logic_vector(9 downto 0);
      DISP_OUT1   : out std_logic;
      KERR1       : out std_logic
   );
end dual_enc_8b10b;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of dual_enc_8b10b is

component RAMB16_S18_S18
-- pragma translate_off
   generic (
      WRITE_MODE_A : string := "NO_CHANGE";
      WRITE_MODE_B : string := "NO_CHANGE";
      INIT_A : bit_vector(17 downto 0)  := "00" & X"0283";
      INIT_B : bit_vector(17 downto 0)  := "00" & X"0283";
      SRVAL_A : bit_vector(17 downto 0)  := "00" & X"0283";
      SRVAL_B : bit_vector(17 downto 0)  := "00" & X"0283";

      INIT_00 : bit_vector(255 downto 0) :=
      X"00ba074e074d076c074b076a076900a707470766076500ab076300ad00ae00b9";
      INIT_01 : bit_vector(255 downto 0) :=
      X"00b5009e009d075c009b075a075900b3009707560755077407530772077100b6";
      INIT_02 : bit_vector(255 downto 0) :=
      X"067a024e024d026c024b026a02690667024702660265066b0263066d066e0679";
      INIT_03 : bit_vector(255 downto 0) :=
      X"0675065e065d025c065b025a0259067306570256025502740253027202710676";
      INIT_04 : bit_vector(255 downto 0) :=
      X"06ba028e028d02ac028b02aa02a906a7028702a602a506ab02a306ad06ae06b9";
      INIT_05 : bit_vector(255 downto 0) :=
      X"06b5069e069d029c069b029a029906b306970296029502b4029302b202b106b6";
      INIT_06 : bit_vector(255 downto 0) :=
      X"073a00ce00cd00ec00cb00ea00e9072700c700e600e5072b00e3072d072e0739";
      INIT_07 : bit_vector(255 downto 0) :=
      X"0735071e071d00dc071b00da00d90733071700d600d500f400d300f200f10736";
      INIT_08 : bit_vector(255 downto 0) :=
      X"013a06ce06cd06ec06cb06ea06e9012706c706e606e5012b06e3012d012e0139";
      INIT_09 : bit_vector(255 downto 0) :=
      X"0135011e011d06dc011b06da06d90133011706d606d506f406d306f206f10136";
      INIT_0A : bit_vector(255 downto 0) :=
      X"057a014e014d016c014b016a01690567014701660165056b0163056d056e0579";
      INIT_0B : bit_vector(255 downto 0) :=
      X"0575055e055d015c055b015a0159057305570156015501740153017201710576";
      INIT_0C : bit_vector(255 downto 0) :=
      X"05ba018e018d01ac018b01aa01a905a7018701a601a505ab01a305ad05ae05b9";
      INIT_0D : bit_vector(255 downto 0) :=
      X"05b5059e059d019c059b019a019905b305970196019501b4019301b201b105b6";
      INIT_0E : bit_vector(255 downto 0) :=
      X"023a05ce05cd05ec05cb05ea05e9022705c705e605e5022b05e3022d022e0239";
      INIT_0F : bit_vector(255 downto 0) :=
      X"0235021e021d05dc021b05da05d90233021705d605d507b405d307b207b10236";
      INIT_10 : bit_vector(255 downto 0) :=
      X"0745008e008d00ac008b00aa00a9075800b800a600a5075400a3075207510746";
      INIT_11 : bit_vector(255 downto 0) :=
      X"074a07610762009c0764009a0099074c07680096009500b4009300b200b10749";
      INIT_12 : bit_vector(255 downto 0) :=
      X"0245064e064d066c064b066a0669025806780666066502540663025202510246";
      INIT_13 : bit_vector(255 downto 0) :=
      X"024a02610262065c0264065a0659024c02680656065506740653067206710249";
      INIT_14 : bit_vector(255 downto 0) :=
      X"0285068e068d06ac068b06aa06a9029806b806a606a5029406a3029202910286";
      INIT_15 : bit_vector(255 downto 0) :=
      X"028a02a102a2069c02a4069a0699028c02a80696069506b4069306b206b10289";
      INIT_16 : bit_vector(255 downto 0) :=
      X"00c5070e070d072c070b072a072900d807380726072500d4072300d200d100c6";
      INIT_17 : bit_vector(255 downto 0) :=
      X"00ca00e100e2071c00e4071a071900cc00e807160715073407130732073100c9";
      INIT_18 : bit_vector(255 downto 0) :=
      X"06c5010e010d012c010b012a012906d801380126012506d4012306d206d106c6";
      INIT_19 : bit_vector(255 downto 0) :=
      X"06ca06e106e2011c06e4011a011906cc06e801160115013401130132013106c9";
      INIT_1A : bit_vector(255 downto 0) :=
      X"0145054e054d056c054b056a0569015805780566056501540563015201510146";
      INIT_1B : bit_vector(255 downto 0) :=
      X"014a01610162055c0164055a0559014c01680556055505740553057205710149";
      INIT_1C : bit_vector(255 downto 0) :=
      X"0185058e058d05ac058b05aa05a9019805b805a605a5019405a3019201910186";
      INIT_1D : bit_vector(255 downto 0) :=
      X"018a01a101a2059c01a4059a0599018c01a80596059505b4059305b205b10189";
      INIT_1E : bit_vector(255 downto 0) :=
      X"05c5004e004d022c004b022a022905d802380226022505d4022305d205d105c6";
      INIT_1F : bit_vector(255 downto 0) :=
      X"05ca05e105e2021c05e4021a021905cc05e802160215023402130232023105c9";
      INIT_20 : bit_vector(255 downto 0) :=
      X"08ba0f4e0f4d0f6c0f4b0f6a0f6908a70f470f660f6508ab0f6308ad08ae08b9";
      INIT_21 : bit_vector(255 downto 0) :=
      X"08b5089e089d00bc089b0f5a0f5908b308970f560f550f740f530f720f7108b6";
      INIT_22 : bit_vector(255 downto 0) :=
      X"0e7a0a4e0a4d0a6c0a4b0a6a0a690e670a470a660a650e6b0a630e6d0e6e0e79";
      INIT_23 : bit_vector(255 downto 0) :=
      X"0e750e5e0e5d067c0e5b0a5a0a590e730e570a560a550a740a530a720a710e76";
      INIT_24 : bit_vector(255 downto 0) :=
      X"0eba0a8e0a8d0aac0a8b0aaa0aa90ea70a870aa60aa50eab0aa30ead0eae0eb9";
      INIT_25 : bit_vector(255 downto 0) :=
      X"0eb50e9e0e9d06bc0e9b0a9a0a990eb30e970a960a950ab40a930ab20ab10eb6";
      INIT_26 : bit_vector(255 downto 0) :=
      X"0f3a08ce08cd08ec08cb08ea08e90f2708c708e608e50f2b08e30f2d0f2e0f39";
      INIT_27 : bit_vector(255 downto 0) :=
      X"0f350f1e0f1d073c0f1b08da08d90f330f1708d608d508f408d308f208f10f36";
      INIT_28 : bit_vector(255 downto 0) :=
      X"093a0ece0ecd0eec0ecb0eea0ee909270ec70ee60ee5092b0ee3092d092e0939";
      INIT_29 : bit_vector(255 downto 0) :=
      X"0935091e091d013c091b0eda0ed9093309170ed60ed50ef40ed30ef20ef10936";
      INIT_2A : bit_vector(255 downto 0) :=
      X"0d7a094e094d096c094b096a09690d670947096609650d6b09630d6d0d6e0d79";
      INIT_2B : bit_vector(255 downto 0) :=
      X"0d750d5e0d5d057c0d5b095a09590d730d570956095509740953097209710d76";
      INIT_2C : bit_vector(255 downto 0) :=
      X"0dba098e098d09ac098b09aa09a90da7098709a609a50dab09a30dad0dae0db9";
      INIT_2D : bit_vector(255 downto 0) :=
      X"0db50d9e0d9d05bc0d9b099a09990db30d970996099509b4099309b209b10db6";
      INIT_2E : bit_vector(255 downto 0) :=
      X"087a0f8e0f8d0fac0f8b0faa0fa908670f870fa60fa5086b0fa3086d086e0879";
      INIT_2F : bit_vector(255 downto 0) :=
      X"0875005e005d007c005b0f9a0f99087300570f960f950fb40f930fb20fb10876";
      INIT_30 : bit_vector(255 downto 0) :=
      X"0f45088e088d08ac088b08aa08a90f5808b808a608a50f5408a30f520f510f46";
      INIT_31 : bit_vector(255 downto 0) :=
      X"0f4a0f610f6207430f64089a08990f4c0f680896089508b4089308b208b10f49";
      INIT_32 : bit_vector(255 downto 0) :=
      X"0a450e4e0e4d0e6c0e4b0e6a0e690a580e780e660e650a540e630a520a510a46";
      INIT_33 : bit_vector(255 downto 0) :=
      X"0a4a0a610a6201830a640e5a0e590a4c0a680e560e550e740e530e720e710a49";
      INIT_34 : bit_vector(255 downto 0) :=
      X"0a850e8e0e8d0eac0e8b0eaa0ea90a980eb80ea60ea50a940ea30a920a910a86";
      INIT_35 : bit_vector(255 downto 0) :=
      X"0a8a0aa10aa201430aa40e9a0e990a8c0aa80e960e950eb40e930eb20eb10a89";
      INIT_36 : bit_vector(255 downto 0) :=
      X"08c50f0e0f0d0f2c0f0b0f2a0f2908d80f380f260f2508d40f2308d208d108c6";
      INIT_37 : bit_vector(255 downto 0) :=
      X"08ca08e108e200c308e40f1a0f1908cc08e80f160f150f340f130f320f3108c9";
      INIT_38 : bit_vector(255 downto 0) :=
      X"0ec5090e090d092c090b092a09290ed80938092609250ed409230ed20ed10ec6";
      INIT_39 : bit_vector(255 downto 0) :=
      X"0eca0ee10ee206c30ee4091a09190ecc0ee80916091509340913093209310ec9";
      INIT_3A : bit_vector(255 downto 0) :=
      X"09450d4e0d4d0d6c0d4b0d6a0d6909580d780d660d6509540d63095209510946";
      INIT_3B : bit_vector(255 downto 0) :=
      X"094a09610962028309640d5a0d59094c09680d560d550d740d530d720d710949";
      INIT_3C : bit_vector(255 downto 0) :=
      X"09850d8e0d8d0dac0d8b0daa0da909980db80da60da509940da3099209910986";
      INIT_3D : bit_vector(255 downto 0) :=
      X"098a09a109a2024309a40d9a0d99098c09a80d960d950db40d930db20db10989";
      INIT_3E : bit_vector(255 downto 0) :=
      X"0f85084e084d086c084b086a08690f980878086608650f9408630f920f910f86";
      INIT_3F : bit_vector(255 downto 0) :=
      X"0f8a07a107a2078307a4085a08590f8c07a80856085508740853087208710f89"
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
attribute INIT_A of U_RAMB16_S18_S18: label is "00283";
attribute INIT_B of U_RAMB16_S18_S18: label is "00283";
attribute SRVAL_A of U_RAMB16_S18_S18: label is "00283";
attribute SRVAL_B of U_RAMB16_S18_S18: label is "00283";

attribute INIT_00 of U_RAMB16_S18_S18: label is
"00ba074e074d076c074b076a076900a707470766076500ab076300ad00ae00b9";
attribute INIT_01 of U_RAMB16_S18_S18: label is
"00b5009e009d075c009b075a075900b3009707560755077407530772077100b6";
attribute INIT_02 of U_RAMB16_S18_S18: label is
"067a024e024d026c024b026a02690667024702660265066b0263066d066e0679";
attribute INIT_03 of U_RAMB16_S18_S18: label is
"0675065e065d025c065b025a0259067306570256025502740253027202710676";
attribute INIT_04 of U_RAMB16_S18_S18: label is
"06ba028e028d02ac028b02aa02a906a7028702a602a506ab02a306ad06ae06b9";
attribute INIT_05 of U_RAMB16_S18_S18: label is
"06b5069e069d029c069b029a029906b306970296029502b4029302b202b106b6";
attribute INIT_06 of U_RAMB16_S18_S18: label is
"073a00ce00cd00ec00cb00ea00e9072700c700e600e5072b00e3072d072e0739";
attribute INIT_07 of U_RAMB16_S18_S18: label is
"0735071e071d00dc071b00da00d90733071700d600d500f400d300f200f10736";
attribute INIT_08 of U_RAMB16_S18_S18: label is
"013a06ce06cd06ec06cb06ea06e9012706c706e606e5012b06e3012d012e0139";
attribute INIT_09 of U_RAMB16_S18_S18: label is
"0135011e011d06dc011b06da06d90133011706d606d506f406d306f206f10136";
attribute INIT_0A of U_RAMB16_S18_S18: label is
"057a014e014d016c014b016a01690567014701660165056b0163056d056e0579";
attribute INIT_0B of U_RAMB16_S18_S18: label is
"0575055e055d015c055b015a0159057305570156015501740153017201710576";
attribute INIT_0C of U_RAMB16_S18_S18: label is
"05ba018e018d01ac018b01aa01a905a7018701a601a505ab01a305ad05ae05b9";
attribute INIT_0D of U_RAMB16_S18_S18: label is
"05b5059e059d019c059b019a019905b305970196019501b4019301b201b105b6";
attribute INIT_0E of U_RAMB16_S18_S18: label is
"023a05ce05cd05ec05cb05ea05e9022705c705e605e5022b05e3022d022e0239";
attribute INIT_0F of U_RAMB16_S18_S18: label is
"0235021e021d05dc021b05da05d90233021705d605d507b405d307b207b10236";
attribute INIT_10 of U_RAMB16_S18_S18: label is
"0745008e008d00ac008b00aa00a9075800b800a600a5075400a3075207510746";
attribute INIT_11 of U_RAMB16_S18_S18: label is
"074a07610762009c0764009a0099074c07680096009500b4009300b200b10749";
attribute INIT_12 of U_RAMB16_S18_S18: label is
"0245064e064d066c064b066a0669025806780666066502540663025202510246";
attribute INIT_13 of U_RAMB16_S18_S18: label is
"024a02610262065c0264065a0659024c02680656065506740653067206710249";
attribute INIT_14 of U_RAMB16_S18_S18: label is
"0285068e068d06ac068b06aa06a9029806b806a606a5029406a3029202910286";
attribute INIT_15 of U_RAMB16_S18_S18: label is
"028a02a102a2069c02a4069a0699028c02a80696069506b4069306b206b10289";
attribute INIT_16 of U_RAMB16_S18_S18: label is
"00c5070e070d072c070b072a072900d807380726072500d4072300d200d100c6";
attribute INIT_17 of U_RAMB16_S18_S18: label is
"00ca00e100e2071c00e4071a071900cc00e807160715073407130732073100c9";
attribute INIT_18 of U_RAMB16_S18_S18: label is
"06c5010e010d012c010b012a012906d801380126012506d4012306d206d106c6";
attribute INIT_19 of U_RAMB16_S18_S18: label is
"06ca06e106e2011c06e4011a011906cc06e801160115013401130132013106c9";
attribute INIT_1A of U_RAMB16_S18_S18: label is
"0145054e054d056c054b056a0569015805780566056501540563015201510146";
attribute INIT_1B of U_RAMB16_S18_S18: label is
"014a01610162055c0164055a0559014c01680556055505740553057205710149";
attribute INIT_1C of U_RAMB16_S18_S18: label is
"0185058e058d05ac058b05aa05a9019805b805a605a5019405a3019201910186";
attribute INIT_1D of U_RAMB16_S18_S18: label is
"018a01a101a2059c01a4059a0599018c01a80596059505b4059305b205b10189";
attribute INIT_1E of U_RAMB16_S18_S18: label is
"05c5004e004d022c004b022a022905d802380226022505d4022305d205d105c6";
attribute INIT_1F of U_RAMB16_S18_S18: label is
"05ca05e105e2021c05e4021a021905cc05e802160215023402130232023105c9";
attribute INIT_20 of U_RAMB16_S18_S18: label is
"08ba0f4e0f4d0f6c0f4b0f6a0f6908a70f470f660f6508ab0f6308ad08ae08b9";
attribute INIT_21 of U_RAMB16_S18_S18: label is
"08b5089e089d00bc089b0f5a0f5908b308970f560f550f740f530f720f7108b6";
attribute INIT_22 of U_RAMB16_S18_S18: label is
"0e7a0a4e0a4d0a6c0a4b0a6a0a690e670a470a660a650e6b0a630e6d0e6e0e79";
attribute INIT_23 of U_RAMB16_S18_S18: label is
"0e750e5e0e5d067c0e5b0a5a0a590e730e570a560a550a740a530a720a710e76";
attribute INIT_24 of U_RAMB16_S18_S18: label is
"0eba0a8e0a8d0aac0a8b0aaa0aa90ea70a870aa60aa50eab0aa30ead0eae0eb9";
attribute INIT_25 of U_RAMB16_S18_S18: label is
"0eb50e9e0e9d06bc0e9b0a9a0a990eb30e970a960a950ab40a930ab20ab10eb6";
attribute INIT_26 of U_RAMB16_S18_S18: label is
"0f3a08ce08cd08ec08cb08ea08e90f2708c708e608e50f2b08e30f2d0f2e0f39";
attribute INIT_27 of U_RAMB16_S18_S18: label is
"0f350f1e0f1d073c0f1b08da08d90f330f1708d608d508f408d308f208f10f36";
attribute INIT_28 of U_RAMB16_S18_S18: label is
"093a0ece0ecd0eec0ecb0eea0ee909270ec70ee60ee5092b0ee3092d092e0939";
attribute INIT_29 of U_RAMB16_S18_S18: label is
"0935091e091d013c091b0eda0ed9093309170ed60ed50ef40ed30ef20ef10936";
attribute INIT_2A of U_RAMB16_S18_S18: label is
"0d7a094e094d096c094b096a09690d670947096609650d6b09630d6d0d6e0d79";
attribute INIT_2B of U_RAMB16_S18_S18: label is
"0d750d5e0d5d057c0d5b095a09590d730d570956095509740953097209710d76";
attribute INIT_2C of U_RAMB16_S18_S18: label is
"0dba098e098d09ac098b09aa09a90da7098709a609a50dab09a30dad0dae0db9";
attribute INIT_2D of U_RAMB16_S18_S18: label is
"0db50d9e0d9d05bc0d9b099a09990db30d970996099509b4099309b209b10db6";
attribute INIT_2E of U_RAMB16_S18_S18: label is
"087a0f8e0f8d0fac0f8b0faa0fa908670f870fa60fa5086b0fa3086d086e0879";
attribute INIT_2F of U_RAMB16_S18_S18: label is
"0875005e005d007c005b0f9a0f99087300570f960f950fb40f930fb20fb10876";
attribute INIT_30 of U_RAMB16_S18_S18: label is
"0f45088e088d08ac088b08aa08a90f5808b808a608a50f5408a30f520f510f46";
attribute INIT_31 of U_RAMB16_S18_S18: label is
"0f4a0f610f6207430f64089a08990f4c0f680896089508b4089308b208b10f49";
attribute INIT_32 of U_RAMB16_S18_S18: label is
"0a450e4e0e4d0e6c0e4b0e6a0e690a580e780e660e650a540e630a520a510a46";
attribute INIT_33 of U_RAMB16_S18_S18: label is
"0a4a0a610a6201830a640e5a0e590a4c0a680e560e550e740e530e720e710a49";
attribute INIT_34 of U_RAMB16_S18_S18: label is
"0a850e8e0e8d0eac0e8b0eaa0ea90a980eb80ea60ea50a940ea30a920a910a86";
attribute INIT_35 of U_RAMB16_S18_S18: label is
"0a8a0aa10aa201430aa40e9a0e990a8c0aa80e960e950eb40e930eb20eb10a89";
attribute INIT_36 of U_RAMB16_S18_S18: label is
"08c50f0e0f0d0f2c0f0b0f2a0f2908d80f380f260f2508d40f2308d208d108c6";
attribute INIT_37 of U_RAMB16_S18_S18: label is
"08ca08e108e200c308e40f1a0f1908cc08e80f160f150f340f130f320f3108c9";
attribute INIT_38 of U_RAMB16_S18_S18: label is
"0ec5090e090d092c090b092a09290ed80938092609250ed409230ed20ed10ec6";
attribute INIT_39 of U_RAMB16_S18_S18: label is
"0eca0ee10ee206c30ee4091a09190ecc0ee80916091509340913093209310ec9";
attribute INIT_3A of U_RAMB16_S18_S18: label is
"09450d4e0d4d0d6c0d4b0d6a0d6909580d780d660d6509540d63095209510946";
attribute INIT_3B of U_RAMB16_S18_S18: label is
"094a09610962028309640d5a0d59094c09680d560d550d740d530d720d710949";
attribute INIT_3C of U_RAMB16_S18_S18: label is
"09850d8e0d8d0dac0d8b0daa0da909980db80da60da509940da3099209910986";
attribute INIT_3D of U_RAMB16_S18_S18: label is
"098a09a109a2024309a40d9a0d99098c09a80d960d950db40d930db20db10989";
attribute INIT_3E of U_RAMB16_S18_S18: label is
"0f85084e084d086c084b086a08690f980878086608650f9408630f920f910f86";
attribute INIT_3F of U_RAMB16_S18_S18: label is
"0f8a07a107a2078307a4085a08590f8c07a80856085508740853087208710f89";

   constant C_NEG     : std_logic_vector(1 downto 0) := "00";
   constant C_POS     : std_logic_vector(1 downto 0) := "01";
   constant C_ZERO    : std_logic_vector(1 downto 0) := "10";
   constant C_INVALID : std_logic_vector(1 downto 0) := "11";

   signal vcc : std_logic;
   signal gnd : std_logic;
   signal ramb_di  : std_logic_vector(15 downto 0);
   signal ramb_dip : std_logic_vector(1 downto 0);

   signal ramb_do_0      : std_logic_vector(15 downto 0);
   signal ramb_addr_0    : std_logic_vector(9 downto 0);
   signal disp_0         : std_logic;
   signal disp_out_int_0 : std_logic;

   signal ramb_do_1      : std_logic_vector(15 downto 0);
   signal ramb_addr_1    : std_logic_vector(9 downto 0);
   signal disp_1         : std_logic;
   signal disp_out_int_1 : std_logic;

begin
   vcc <= '1';
   gnd <= '0';
   ramb_di   <= (others => '1');
   ramb_dip  <= "11";

   U_RAMB16_S18_S18: RAMB16_S18_S18
      port map (
         DIA     => ramb_di,
         DIPA    => ramb_dip,
         ADDRA   => ramb_addr_0,
         ENA     => vcc,
         WEA     => gnd,
         SSRA    => RESET0,
         CLKA    => CLK0,
         DOA     => ramb_do_0,
         DOPA    => open,

         DIB     => ramb_di,
         DIPB    => ramb_dip,
         ADDRB   => ramb_addr_1,
         ENB     => vcc,
         WEB     => gnd,
         SSRB    => RESET1,
         CLKB    => CLK1,
         DOB     => ramb_do_1,
         DOPB    => open
      );

   DOUT0 <= ramb_do_0(9 downto 0);
   disp_out_int_0 <= ramb_do_0(10);
   DISP_OUT0 <= disp_out_int_0;
   KERR0 <= ramb_do_0(11);
   ramb_addr_0(7 downto 0) <= DIN0;
   ramb_addr_0(8) <= disp_0;
   ramb_addr_0(9) <= KIN0;

   DOUT1 <= ramb_do_1(9 downto 0);
   disp_out_int_1 <= ramb_do_1(10);
   DISP_OUT1 <= disp_out_int_1;
   KERR1 <= ramb_do_1(11);
   ramb_addr_1(7 downto 0) <= DIN1;
   ramb_addr_1(8) <= disp_1;
   ramb_addr_1(9) <= KIN1;

   P_DISP_0: process (RESET0, CLK0)
   begin
      if (FORCE_DISP0 = '1') then
         disp_0 <= DISP_IN0;
      else
         disp_0 <= disp_out_int_0;
      end if;
   end process;

   P_DISP_1: process (RESET1, CLK1)
   begin
      if (FORCE_DISP1 = '1') then
         disp_1 <= DISP_IN1;
      else
         disp_1 <= disp_out_int_1;
      end if;
   end process;

end behavioral;

