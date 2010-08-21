--
-- align_unit.vhd : Alignment Unit (src_addr -> dst_addr)
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
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
-- TODO: repair it
--

library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on


-- ----------------------------------------------------------------------------
--        ENTITY DECLARATION -- Alignment Unit (src_addr -> dst_addr)        -- 
-- ----------------------------------------------------------------------------

entity GICS_ALIGN_UNIT is 
   port (
      -- Common interface -----------------------------------------------------
      CLK           : in std_logic;  
      RESET         : in std_logic;  

      -- Control input interface ----------------------------------------------  
      SRC_ADDR      : in  std_logic_vector(2 downto 0);     -- source address
      DST_ADDR      : in  std_logic_vector(2 downto 0);     -- destination address
	   DATA_LEN      : in  std_logic_vector(2 downto 0);     -- last data word length

      -- Control output interface ---------------------------------------------
      WAIT_ON_START : out std_logic;            -- need wait on start
      WAIT_ON_END   : out std_logic;            -- need wait on end

      -- Input interface ------------------------------------------------------
      IN_DATA       : in  std_logic_vector(63 downto 0);
      IN_SOF        : in  std_logic;
      IN_EOF        : in  std_logic;
      IN_SRC_RDY    : in  std_logic;
      IN_DST_RDY    : out std_logic;      

      -- Output interface -----------------------------------------------------
      OUT_DATA      : out std_logic_vector(63 downto 0);
      OUT_SOF       : out std_logic;
      OUT_EOF       : out std_logic;      
      OUT_SRC_RDY   : out std_logic;      
      OUT_DST_RDY   : in  std_logic
   );
end GICS_ALIGN_UNIT;

-- ----------------------------------------------------------------------------
--    ARCHITECTURE DECLARATION  --  Alignment Unit (src_addr -> dst_addr)    --
-- ----------------------------------------------------------------------------

architecture align_unit_arch of GICS_ALIGN_UNIT is

	-- shift register signals
	signal shreg_in 		      : std_logic_vector(63 downto 0);
	signal shreg_out 		      : std_logic_vector(63 downto 0);
	signal shreg_addr		      : std_logic_vector(7 downto 0);

	-- barrel shifter selector
	signal barrel_sel		      : std_logic_vector(2 downto 0);

   -- auxiliary computes
	signal aux_1 			      : std_logic_vector(3 downto 0);
	signal aux_2			      : std_logic_vector(2 downto 0);
	signal aux_3			      : std_logic_vector(3 downto 0);
   signal len_corrected       : std_logic_vector(2 downto 0);
   
   -- full the link, but do not send data
   signal wait_on_start_sig   : std_logic;

   -- empty the link, but do not recieve data
   signal wait_on_end_sig     : std_logic;

	-- for LUT simulating only
	signal clk_del : std_logic;


   -- used for shifr register -------------------------------------------------
   component SRLC16E
   -- synthesis translate_off
       generic (INIT : bit_vector := X"0000");
   -- synthesis translate_on
   port (
            Q     : out std_ulogic;
            Q15   : out std_ulogic;
            A0    : in std_ulogic;
            A1    : in std_ulogic;
            A2    : in std_ulogic;
            A3    : in std_ulogic;
            CE    : in std_ulogic;
            CLK   : in std_ulogic;
            D     : in std_ulogic
         );
   end component;

 	signal write_allow   : std_logic; 	-- allow write to internal registers
   signal f_we          : std_logic;   -- first write enable for input pipe
   signal in_sof_p      : std_logic;   -- first input pipe
   signal in_sof_p_p    : std_logic;   -- second input pipe
   signal in_eof_p      : std_logic;   -- first input pipe
   signal in_eof_p_p    : std_logic;   -- second input pipe
   signal in_eof_p_p_p  : std_logic;   -- third input pipe
   signal out_eof_sig   : std_logic;   -- output logic signal
   signal eof_mux       : std_logic;   -- first mux eof output
   signal empty_link    : std_logic;   -- empty data link now
   signal last_word     : std_logic;   -- last transfered word(s)
   signal in_src_rdy_p  : std_logic;   -- input pipe
   signal stop_output   : std_logic;   -- time to stop output


begin

   aux_1	<= ('0' & DST_ADDR) - ('0' & SRC_ADDR);
   aux_2	<= SRC_ADDR + len_corrected;
   aux_3	<= ( '0' & aux_1(2 downto 0)) + ('0' & aux_2);

   len_corrected  <= DATA_LEN - 1;
   barrel_sel	   <= aux_1(2 downto 0);

   clk_del        <= CLK; -- clock delay (for LUT simulating only)

   -- output control signals --------------------------------------------------
   wait_on_start_sig    <= aux_1(3);
   wait_on_end_sig      <= aux_3(3);
   WAIT_ON_START        <= wait_on_start_sig;    
   WAIT_ON_END          <= wait_on_end_sig;

   -- first write enable
   f_we <= '1' when (IN_SRC_RDY = '1' and OUT_DST_RDY = '1') else '0';

   -- -------------------------------------------------------------------------
   -- register in_sof_p -------------------------------------------------------
   IN_SOF_P_I: process(RESET, CLK, IN_SOF, f_we)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            in_sof_p <= '0';
         elsif (f_we = '1') then
            in_sof_p <= IN_SOF;
         end if;
      end if;
   end process;

   -- register in_sof_p_p -----------------------------------------------------
   IN_SOF_P_P_I: process(RESET, CLK, in_sof_p, write_allow)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            in_sof_p_p <= '0';
         elsif (write_allow = '1') then
            in_sof_p_p <= in_sof_p;
         end if;
      end if;
   end process;

   -- multiplexor out_sop_muxp ------------------------------------------------
   out_sop_muxp: process(wait_on_start_sig, in_sof_p, in_sof_p_p)
   begin
      case wait_on_start_sig is
         when '0' => OUT_SOF <= in_sof_p;
         when '1' => OUT_SOF <= in_sof_p_p;
         when others => OUT_SOF <= 'X';
      end case;
   end process;

   stop_output <= '1' when (wait_on_start_sig = '1' and in_sof_p = '1') else '0';

   -- -------------------------------------------------------------------------
   -- register in_eof_p -------------------------------------------------------
   IN_EOF_P_I: process(RESET, CLK, IN_EOF, f_we)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            in_eof_p <= '0';
         elsif (f_we = '1') then
            in_eof_p <= IN_EOF;
         end if;
      end if;
   end process;

   -- register in_eof_p_p -----------------------------------------------------
   IN_EOF_P_P_I: process(RESET, CLK, in_eof_p, write_allow)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            in_eof_p_p <= '0';
         elsif (write_allow = '1') then
            in_eof_p_p <= in_eof_p;
         end if;
      end if;
   end process;

   -- multiplexor eof_muxp ----------------------------------------------------
   eof_muxp: process(wait_on_end_sig, in_eof_p, in_eof_p_p)
   begin
      case wait_on_end_sig is
         when '0' => eof_mux <= in_eof_p;
         when '1' => eof_mux <= in_eof_p_p;
         when others => eof_mux <= 'X';
      end case;
   end process;

   -- register in_eof_p_p_p ---------------------------------------------------
   IN_EOF_P_P_P_I: process(RESET, CLK, eof_mux, write_allow)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            in_eof_p_p_p <= '0';
         elsif (write_allow = '1') then
            in_eof_p_p_p <= eof_mux;
         end if;
      end if;
   end process;

   -- multiplexor out_eof_muxp ------------------------------------------------
   out_eof_muxp: process(wait_on_start_sig, eof_mux, in_eof_p_p_p)
   begin
      case wait_on_start_sig is
         when '0' => out_eof_sig <= eof_mux;
         when '1' => out_eof_sig <= in_eof_p_p_p;
         when others => out_eof_sig <= 'X';
      end case;
   end process;

   OUT_EOF <= out_eof_sig;

   -- register last_word ------------------------------------------------------
   LAST_WORD_P: process(RESET, CLK, out_eof_sig, IN_EOF, f_we)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            last_word <= '0';
         elsif (IN_EOF = '1' and f_we = '1') then
            last_word <= '1';
         else
         --elsif(EOP_OUT = '0') then
            last_word <= '0';
         end if;
      end if;
   end process;

   empty_link  <= '1' when (last_word = '1' and out_eof_sig = '0') else '0';
   write_allow <= '1' when (empty_link = '1' or f_we = '1') else '0';

   -- -------------------------------------------------------------------------
   -- RDY logic ---------------------------------------------------------------
   IN_DST_RDY  <= '1' when (OUT_DST_RDY = '1' and empty_link = '0') else '0'; 

   -- register in_src_rdy_p ---------------------------------------------------
   IN_SRC_RDY_P_I: process(RESET, CLK, IN_SRC_RDY)
   begin
      if (CLK'event AND CLK = '1') then
         in_src_rdy_p <= IN_SRC_RDY;
      end if;
   end process;

   OUT_SRC_RDY <= '1' when ((empty_link = '1' or in_src_rdy_p = '1') and stop_output = '0') 
                  else '0';

   -- addressable shift registers mapped dirrectly to LUT ---------------------
   SHIFT_REG : for i in 0 to 7 generate		
   	ONE_BYTE : for j in 0 to 7 generate
    		SRLC16E_I : SRLC16E
-- synthesis translate_off 
    		generic map (INIT => X"0000")
-- synthesis translate_on 
    		port map 
    		(
    		   Q 	   => shreg_out((i*8)+j),  -- SRL data output
    		   Q15 	=> open,   				   -- Carry output (connect to next SRL)
    		   A0 	=> shreg_addr(i),       -- Select[0] input
   		   A1 	=> '0',     			   -- Select[1] input
   		   A2	   => '0',     		   	-- Select[2] input
    		   A3 	=> '0',     			   -- Select[3] input
			   CE	   => write_allow,			-- Clock enable input
    		   CLK 	=> clk_del,				   -- Clock input
    		   D  	=> IN_DATA((i*8)+j)		-- SRL data input
    		);
     end generate; -- one_byte
   end generate; -- shift_reg


   -- barrel shifter	----------------------------------------------------------
   BARREL_SHIFTER_I : entity work.barrel_shifter_64
   	port map (
		DATA_IN		=> shreg_out,      
      SEL			=> barrel_sel,	 
      DATA_OUT    => OUT_DATA 	   
	);
   
   -- shift register address decoder ------------------------------------------
   ADDR_DEC: process (SRC_ADDR, DST_ADDR)
      -- init phase
      begin
	     case SRC_ADDR is
		    when "000" =>    -- SRC_ADDR = 0
		 	   case DST_ADDR is
		 	     when "000" => shreg_addr <= "00000000";
		 		  when "001" => shreg_addr <= "10000000";
		 		  when "010" => shreg_addr <= "11000000";
		 		  when "011" => shreg_addr <= "11100000";
		 		  when "100" => shreg_addr <= "11110000";
		 		  when "101" => shreg_addr <= "11111000";
		 		  when "110" => shreg_addr <= "11111100";
		 		  when "111" => shreg_addr <= "11111110";
		 		  when others => null;
		 	   end case;
		 	when "001" => 		-- SRC_ADDR = 1
		 	   case DST_ADDR is
		 	 	  when "000" => shreg_addr <= "11111110";
		 		  when "001" => shreg_addr <= "00000000";
		 		  when "010" => shreg_addr <= "10000000";
		 		  when "011" => shreg_addr <= "11000000";
		 		  when "100" => shreg_addr <= "11100000";
		 		  when "101" => shreg_addr <= "11110000";
		 		  when "110" => shreg_addr <= "11111000";
		 		  when "111" => shreg_addr <= "11111100";
		 		  when others => null;
		 	   end case;
		 	when "010" => 		-- SRC_ADDR = 2
		 	   case DST_ADDR is
		 	     when "000" => shreg_addr <= "11111100";
		 		  when "001" => shreg_addr <= "11111110";
		 		  when "010" => shreg_addr <= "00000000";
		 		  when "011" => shreg_addr <= "10000000";
		 		  when "100" => shreg_addr <= "11000000";
		 		  when "101" => shreg_addr <= "11100000";
		 		  when "110" => shreg_addr <= "11110000";
		 		  when "111" => shreg_addr <= "11111000";
		 		  when others => null;
		 	   end case;
		 	when "011" => 		-- SRC_ADDR = 3
		 	   case DST_ADDR is
		 	     when "000" => shreg_addr <= "11111000";
		 		  when "001" => shreg_addr <= "11111100";
		 		  when "010" => shreg_addr <= "11111110";
		 		  when "011" => shreg_addr <= "00000000";
		 		  when "100" => shreg_addr <= "10000000";
		 		  when "101" => shreg_addr <= "11000000";
		 		  when "110" => shreg_addr <= "11100000";
		 		  when "111" => shreg_addr <= "11110000";
		 		  when others => null;
		 	   end case;
		 	when "100" => 		-- SRC_ADDR = 4
		 	   case DST_ADDR is
		 	     when "000" => shreg_addr <= "11110000";
		 		  when "001" => shreg_addr <= "11111000";
		 		  when "010" => shreg_addr <= "11111100";
		 		  when "011" => shreg_addr <= "11111110";
		 		  when "100" => shreg_addr <= "00000000";
		 		  when "101" => shreg_addr <= "10000000";
		 		  when "110" => shreg_addr <= "11000000";
		 		  when "111" => shreg_addr <= "11100000";
		 		  when others => null;
		 	   end case;
		 	when "101" => 		-- SRC_ADDR = 5
		 	   case DST_ADDR is
		 		  when "000" => shreg_addr <= "11100000";
		 		  when "001" => shreg_addr <= "11110000";
		 		  when "010" => shreg_addr <= "11111000";
		 		  when "011" => shreg_addr <= "11111100";
		 		  when "100" => shreg_addr <= "11111110";
		 		  when "101" => shreg_addr <= "00000000";
		 		  when "110" => shreg_addr <= "10000000";
		 		  when "111" => shreg_addr <= "11000000";
		 		  when others => null;
		 	   end case;
		 	when "110" => 		-- SRC_ADDR = 6
		 	   case DST_ADDR is
		 	     when "000" => shreg_addr <= "11000000";
		 		  when "001" => shreg_addr <= "11100000";
		 		  when "010" => shreg_addr <= "11110000";
		 		  when "011" => shreg_addr <= "11111000";
		 		  when "100" => shreg_addr <= "11111100";
		 		  when "101" => shreg_addr <= "11111110";
		 		  when "110" => shreg_addr <= "00000000";
		 		  when "111" => shreg_addr <= "10000000";
		 		  when others => null;
		 	   end case;
		 	when "111" => 		-- SRC_ADDR = 7
		 	   case DST_ADDR is
		 	     when "000" => shreg_addr <= "10000000";
		 		  when "001" => shreg_addr <= "11000000";
		 		  when "010" => shreg_addr <= "11100000";
		 		  when "011" => shreg_addr <= "11110000";
		 		  when "100" => shreg_addr <= "11111000";
		 		  when "101" => shreg_addr <= "11111100";
		 		  when "110" => shreg_addr <= "11111110";
		 		  when "111" => shreg_addr <= "00000000";
		 		  when others => null;
		 	   end case;
		 	when others	=> null;
		 end case;
	end process;



end align_unit_arch;

