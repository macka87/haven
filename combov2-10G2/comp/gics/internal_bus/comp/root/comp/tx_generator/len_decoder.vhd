 --
-- len_decoder.vhd : PCI-e Length decoder
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kobierský <kobierskyk@liberouter.org>
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

library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity PCIE_TX_LEN_DECODER is
  port (
    -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N           : in  std_logic; 
      TRN_CLK               : in  std_logic; 

    -- Data Input Interface -------------------------------------------------
      LEN_IN                : in std_logic_vector(11 downto 0);
      LEN_IN_WE             : in std_logic;
      TYPE_REG              : in std_logic_vector(1 downto 0);
      MAX_READ_SIZE         : in std_logic_vector(9 downto 0);
      MAX_PAYLOAD_SIZE      : in std_logic_vector(9 downto 0);
      FIRST_BE_SRC_ADDR_REG : in std_logic_vector(2 downto 0);

    -- Output FSM Interface -------------------------------------------------
      SPLIT_TRANS           : out std_logic;
      NEXT_PART             : in  std_logic;

    -- Output Interface -----------------------------------------------------
      DW_LEN_OUT            : out std_logic_vector(9 downto 0);
      FIRST_BE_OUT          : out std_logic_vector(3 downto 0);
      LAST_BE_OUT           : out std_logic_vector(3 downto 0);
      BYTE_COUNT            : out std_logic_vector(11 downto 0)
   );
end PCIE_TX_LEN_DECODER;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of PCIE_TX_LEN_DECODER is

   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------


   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal len_in_reg           : std_logic_vector(11 downto 0);
   signal len_in_mux           : std_logic_vector(12 downto 0);
   signal len_part             : std_logic_vector( 1 downto 0);
   signal split_trans_sig      : std_logic;
   signal split_trans_sig_r    : std_logic;
   signal split_trans_sig_w    : std_logic;
   signal out_sel              : std_logic_vector( 1 downto 0);
   signal dec_sel              : std_logic_vector( 3 downto 0);
   signal one_dw_detect        : std_logic;
   signal one_dw               : std_logic;
   signal select_last_be       : std_logic_vector(1 downto 0);
   signal last_be_out_sig      : std_logic_vector( 3 downto 0);
   signal last_be_dec_sel      : std_logic_vector( 3 downto 0);
   signal last_be_dec_out      : std_logic_vector( 3 downto 0);
   signal first_be_dec_out     : std_logic_vector( 3 downto 0);
   signal first_be_1dw_dec_out : std_logic_vector(3 downto 0);
   signal one_dw_detect_in     : std_logic_vector(3 downto 0);
   signal first_be_1dw_dec_sel : std_logic_vector(3 downto 0);

   signal zero_len             : std_logic;
   signal zero_read_len        : std_logic;
   signal zero_write_len       : std_logic;

begin
   zero_len        <= '1' when (len_in_reg = 0) else '0';
   zero_read_len   <= '1' when (MAX_READ_SIZE(9 downto 5) = 0) else '0';
   zero_write_len  <= '1' when (MAX_PAYLOAD_SIZE(9 downto 5) = 0) else '0';
   
   -- memory for length -------------------------------------------------------
   LEN_IN_P : process (TRN_CLK, TRN_RESET_N, LEN_IN, LEN_IN_WE, NEXT_PART, len_in_mux ) 
      begin
         if (TRN_CLK = '1' and TRN_CLK'event) then
            if (TRN_RESET_N = '0') then 
               len_in_reg  <= (others => '0');
            elsif (LEN_IN_WE = '1') then        -- INIT
               len_in_reg <=  LEN_IN;
            elsif (NEXT_PART = '1') then     -- DECREMENT
            	len_in_reg  <= len_in_mux(11 downto 0);
            end if;
         end if;
      end process;

   -- send number of not sended bytes -----------------------------------------    
   BYTE_COUNT <= len_in_reg;

   -- multiplexer for decrement length ----------------------------------------
   LEN_MUX : process(TYPE_REG, len_in_reg, MAX_READ_SIZE, MAX_PAYLOAD_SIZE, FIRST_BE_SRC_ADDR_REG, zero_len, zero_read_len, zero_write_len)
	   begin
		   case (TYPE_REG(1)) is
		   	when '0' => len_in_mux <= ((zero_len & len_in_reg) - (zero_read_len & MAX_READ_SIZE & "00") + (FIRST_BE_SRC_ADDR_REG(1 downto 0)) );  -- READ
		   	when '1' => len_in_mux <= ((zero_len & len_in_reg) - (zero_write_len & MAX_PAYLOAD_SIZE & "00") + (FIRST_BE_SRC_ADDR_REG(1 downto 0)) );  -- WRITE, CPL
		   	when others => len_in_mux <= (others => 'X');
		   end case;
	   end process;

   -- detect split transaction ------------------------------------------------  
   split_trans_sig_r <= '1' when ( ((zero_len & len_in_reg) + FIRST_BE_SRC_ADDR_REG(1 downto 0)) > (zero_read_len & MAX_READ_SIZE&"00")) else  -- READ
                        '0';
   split_trans_sig_w <= '1' when ( ((zero_len & len_in_reg) + FIRST_BE_SRC_ADDR_REG(1 downto 0)) > (zero_write_len & MAX_PAYLOAD_SIZE&"00")) else   -- WRITE, CPL
                        '0';

   -- multiplexer for transaction signal --------------------------------------
   TRANS_MUX : process(TYPE_REG, split_trans_sig_r, split_trans_sig_w)
	   begin
		   case (TYPE_REG(1)) is
		   	when '0' => split_trans_sig <= split_trans_sig_r;           -- READ
		   	when '1' => split_trans_sig <= split_trans_sig_w;           -- WRITE, CPL
		   	when others => null;
		   end case;
	   end process;

   dec_sel <= len_in_reg(1 downto 0) & FIRST_BE_SRC_ADDR_REG(1 downto 0);

   -- DW length decoder -------------------------------------------------------
   LEN_DEC : process(dec_sel)
	   begin
		   case (dec_sel) is
		   	when "0000" => len_part <= "00";   --0+0    
		   	when "0001" => len_part <= "01";   --0+1
            when "0010" => len_part <= "01";   --0+2        
		   	when "0011" => len_part <= "01";   --0+3
            when "0100" => len_part <= "01";   --1+0        
		   	when "0101" => len_part <= "01";   --1+1		   	
            when "0110" => len_part <= "01";   --1+2        
		   	when "0111" => len_part <= "01";   --1+3
            when "1000" => len_part <= "01";   --2+0       
		   	when "1001" => len_part <= "01";   --2+1		   	
            when "1010" => len_part <= "01";   --2+2
		   	when "1011" => len_part <= "10";   --2+3
            when "1100" => len_part <= "01";   --3+0        
		   	when "1101" => len_part <= "01";   --3+1
            when "1110" => len_part <= "10";   --3+2        
		   	when "1111" => len_part <= "10";   --3+3
		   	when others => null;
		   end case;
	   end process; 

   -- output multiplexor selector ---------------------------------------------
   out_sel <= split_trans_sig & TYPE_REG(1);

   -- output multiplexor ------------------------------------------------------
   OUT_LEN_MUX : process(out_sel, MAX_READ_SIZE, MAX_PAYLOAD_SIZE, len_in_reg, len_part )
      begin
         case (out_sel) is
            when "00" => DW_LEN_OUT <= len_in_reg(11 downto 2) + len_part;  -- READ
            when "01" => DW_LEN_OUT <= len_in_reg(11 downto 2) + len_part;  -- WRITE, CPL
            when "10" => DW_LEN_OUT <= MAX_READ_SIZE;       -- READ (exceed max.)
            when "11" => DW_LEN_OUT <= MAX_PAYLOAD_SIZE;    -- WRITE, CPL (exceed max.)
            when others => null;
         end case;
      end process;

   -- output split transaction ------------------------------------------------
   SPLIT_TRANS <= split_trans_sig;

   -- selector include 4kB support
   select_last_be <= split_trans_sig & zero_read_len;

   -- multiplexer for LAST_BE_OUT ---------------------------------------------
   LAST_BE_OUT_MUX : process(select_last_be, last_be_out_sig)
	   begin
		   case (select_last_be) is
		   	when "10" => LAST_BE_OUT <= "1111";                 -- split trans.
		   	when "00" => LAST_BE_OUT <= last_be_out_sig;        -- otherwise
		   	when "11" => LAST_BE_OUT <= "1111";                 -- not possible!
		   	when "01" => LAST_BE_OUT <= "1111";                 -- 4kB last_be
		   	when others => null;
		   end case;
	   end process;

   one_dw_detect_in <= LEN_IN_REG(1 downto 0) & FIRST_BE_SRC_ADDR_REG(1 downto 0);
   -- get correct last_be_out signal ------------------------------------------
   ONE_DW_DECP : process(one_dw_detect_in)
     begin
        case (one_dw_detect_in) is
           when "0000" => one_dw_detect <= '1';
           when "0001" => one_dw_detect <= '0';
           when "0010" => one_dw_detect <= '0';
           when "0011" => one_dw_detect <= '0';
           when "0100" => one_dw_detect <= '1';
           when "0101" => one_dw_detect <= '1';
           when "0110" => one_dw_detect <= '1';
           when "0111" => one_dw_detect <= '1';
           when "1000" => one_dw_detect <= '1';
           when "1001" => one_dw_detect <= '1';
           when "1010" => one_dw_detect <= '1';
           when "1011" => one_dw_detect <= '0';
           when "1100" => one_dw_detect <= '1';
           when "1101" => one_dw_detect <= '1';
           when "1110" => one_dw_detect <= '0';
           when "1111" => one_dw_detect <= '0';
           when others => one_dw_detect <= 'X';
        end case;
      end process;

   one_dw <= '0' when (len_in_reg > 4) else one_dw_detect;

   -- get correct last_be_out signal ------------------------------------------
   LAST_BE_MUX : process(one_dw, last_be_dec_out)
	   begin
		   case (one_dw) is
		   	when '0' => last_be_out_sig <= last_be_dec_out;     -- more than one DW                   
		   	when '1' => last_be_out_sig <= "0000";              -- only one DW
		   	when others => null;
		   end case;
      end process;

   last_be_dec_sel <= len_in_reg(1 downto 0) & FIRST_BE_SRC_ADDR_REG(1 downto 0);
   -- decode output last_be-----------------------------------------------------
   LAST_BE_DEC_P : process(last_be_dec_sel)
      begin
         case (last_be_dec_sel) is -- Adder
            when "0000" => last_be_dec_out <= "1111";
            when "0001" => last_be_dec_out <= "0001";
            when "0010" => last_be_dec_out <= "0011";
            when "0011" => last_be_dec_out <= "0111"; 
            when "0100" => last_be_dec_out <= "0001";
            when "0101" => last_be_dec_out <= "0011";
            when "0110" => last_be_dec_out <= "0111";
            when "0111" => last_be_dec_out <= "1111";
            when "1000" => last_be_dec_out <= "0011";
            when "1001" => last_be_dec_out <= "0111";
            when "1010" => last_be_dec_out <= "1111";
            when "1011" => last_be_dec_out <= "0001";
            when "1100" => last_be_dec_out <= "0111";
            when "1101" => last_be_dec_out <= "1111";
            when "1110" => last_be_dec_out <= "0001";
            when "1111" => last_be_dec_out <= "0011";
            when others => last_be_dec_out <= "XXXX";
         end case;
      end process;

   -- multiplexer for FIRST_BE_OUT ---------------------------------------------
   FIRST_BE_OUT_MUX : process(one_dw, first_be_dec_out, first_be_1dw_dec_out )
	   begin
		   case (one_dw) is
		   	when '0'    => FIRST_BE_OUT <= first_be_dec_out;     -- more than one dw
		   	when '1'    => FIRST_BE_OUT <= first_be_1dw_dec_out; -- only one dw
		   	when others => FIRST_BE_OUT <= "XXXX";
		   end case;
	   end process;

   -- decode output first_be-----------------------------------------------------
   FIRST_BE_DEC_P : process(FIRST_BE_SRC_ADDR_REG)
      begin
         case FIRST_BE_SRC_ADDR_REG(1 downto 0) is
            when "00"   => first_be_dec_out <= "1111";
            when "01"   => first_be_dec_out <= "1110";
            when "10"   => first_be_dec_out <= "1100";
            when "11"   => first_be_dec_out <= "1000";
            when others => first_be_dec_out <= "XXXX";
         end case;
      end process;

   first_be_1dw_dec_sel <= FIRST_BE_SRC_ADDR_REG(1 downto 0) & len_in_reg(1 downto 0);
   -- decode output first_be-----------------------------------------------------
   FIRST_BE_1DW_DEC_P : process(first_be_1dw_dec_sel)
      begin
         case first_be_1dw_dec_sel is
            when "0000" => first_be_1dw_dec_out <= "1111";
            when "0001" => first_be_1dw_dec_out <= "0001";
            when "0010" => first_be_1dw_dec_out <= "0011";
            when "0011" => first_be_1dw_dec_out <= "0111"; 
            when "0100" => first_be_1dw_dec_out <= "XXXX";
            when "0101" => first_be_1dw_dec_out <= "0010";
            when "0110" => first_be_1dw_dec_out <= "0110";
            when "0111" => first_be_1dw_dec_out <= "1110";
            when "1000" => first_be_1dw_dec_out <= "XX00";
            when "1001" => first_be_1dw_dec_out <= "0100";
            when "1010" => first_be_1dw_dec_out <= "1100";
            when "1011" => first_be_1dw_dec_out <= "XXXX";
            when "1100" => first_be_1dw_dec_out <= "XXXX";
            when "1101" => first_be_1dw_dec_out <= "1000";
            when "1110" => first_be_1dw_dec_out <= "XXXX";
            when "1111" => first_be_1dw_dec_out <= "XXXX";
            when others => first_be_1dw_dec_out <= "XXXX";
         end case;
      end process;

end architecture FULL;

