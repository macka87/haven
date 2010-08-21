-- fl_extract_full.vhd: Full architecture of FrameLink Extract
-- component.
-- Copyright (C) 2007 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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

architecture full of FL_EXTRACT is

-- inside signals
signal part_valid: std_logic;
signal valid_in: std_logic;
signal data_valid: std_logic;

constant DW:integer:=log2(PARTS);
constant PW:integer:=log2(LENGTH);
signal HEAD_EN   : std_logic_vector(2**DW-1 downto 0);
signal POSITION  : std_logic_vector(PW-1 downto 0);

-- generic align constants
-- data width in bytes
constant reduced_data_width : integer := DATA_WIDTH/8;
-- first register width
constant first_reg_top : integer := (reduced_data_width - OFFSET rem reduced_data_width)*8-1;
-- which part of input signal (RX_DATA) will be conected to the first register
constant first_reg_data_top : integer := DATA_WIDTH-1;
constant first_reg_data_bottom :integer := (OFFSET rem reduced_data_width)*8;
-- constant which is used for counting the position in EXT_DATA signal to which will be
-- the register's output connected
constant in_reg_out :integer := (reduced_data_width - OFFSET rem reduced_data_width)*8;
-- to which part of EXT_DATA signal will be the last part of data connected
constant last_top : integer := SIZE*8-1;
constant last_bottom :integer := (SIZE-(reduced_data_width-OFFSET rem reduced_data_width))/reduced_data_width*DATA_WIDTH+(reduced_data_width - OFFSET rem reduced_data_width)*8;
-- which part of RX_DATA signal will be connected to EXT_DATA in the last part stage
constant last_data_top :integer := ((SIZE-(reduced_data_width-OFFSET rem reduced_data_width)) rem reduced_data_width)*8-1;
-- counts number of registers with width of DATA_WIDTH
constant number_of_ful_reg :integer := (SIZE-(reduced_data_width-OFFSET rem reduced_data_width))/reduced_data_width;
-- indicates that ther will be some part of EXT_DATA signal which is uncovered by previous registers
constant rem_of_ful_reg :integer := (SIZE-(reduced_data_width-OFFSET rem reduced_data_width)) rem reduced_data_width; 

-- generic align signals
signal WE: std_logic_vector(number_of_ful_reg downto 0);

begin

-- generate pipeline
gen1: if (PIPELINE_EN=true) generate

  -- TX_DATA register
  process (clk, reset)
    begin
     if reset='1' then   --asynchronous reset active High
        TX_DATA <= (others=>'0');
     elsif (clk'event and clk='1') then  -- clk rising edge
        TX_DATA <= RX_DATA;
     end if;
  end process;

  -- TX_REM register
  process (clk, reset)
    begin
      if reset='1' then   --asynchronous reset active High
        TX_REM <= (others=>'0');
      elsif (clk'event and clk='1') then  -- clk rising edge
        TX_REM <= RX_REM;
      end if;
  end process;

  -- TX_SOF_N register
  process (clk, reset)
    begin
      if reset='1' then   --asynchronous reset active High
        TX_SOF_N <= '1';
      elsif (clk'event and clk='1') then  -- clk rising edge
        TX_SOF_N <= RX_SOF_N;
      end if;
  end process;

  -- TX_EOF_N register
  process (clk, reset)
    begin
      if reset='1' then   --asynchronous reset active High
        TX_EOF_N <= '1';
      elsif (clk'event and clk='1') then  -- clk rising edge
        TX_EOF_N <= RX_EOF_N;
      end if;
  end process;

  -- TX_SOP_N register
  process (clk, reset)
    begin
      if reset='1' then   --asynchronous reset active High
        TX_SOP_N <= '1';
      elsif (clk'event and clk='1') then  -- clk rising edge
        TX_SOP_N <= RX_SOP_N;
      end if;
  end process;

  -- TX_EOP_N register
  process (clk, reset)
    begin
     if reset='1' then   --asynchronous reset active High
        TX_EOP_N <= '1';
     elsif (clk'event and clk='1') then  -- clk rising edge
        TX_EOP_N <= RX_EOP_N;
     end if;
  end process;

  -- TX_SRC_RDY_N register
  process (clk, reset)
    begin
     if reset='1' then   --asynchronous reset active High
        TX_SRC_RDY_N <= '1';
     elsif (clk'event and clk='1') then  -- clk rising edge
        TX_SRC_RDY_N <= RX_SRC_RDY_N;
     end if;
  end process;

  -- RX_DST_RDY_N register
  process (clk, reset)
    begin
     if reset='1' then   --asynchronous reset active High
        RX_DST_RDY_N <= '1';
     elsif (clk'event and clk='1') then  -- clk rising edge
        RX_DST_RDY_N <= TX_DST_RDY_N;
     end if;
  end process;

end generate gen1;

-- generate conection between input and output when pipeline aren't generated
gen2: if (PIPELINE_EN=false) generate
   TX_DATA<=RX_DATA;
   TX_REM<=RX_REM;
   TX_SOF_N<=RX_SOF_N;
   TX_EOF_N<=RX_EOF_N;
   TX_SOP_N<=RX_SOP_N;
   TX_EOP_N<=RX_EOP_N;
   TX_SRC_RDY_N<=RX_SRC_RDY_N;
   RX_DST_RDY_N<=TX_DST_RDY_N;
end generate gen2;

-- decoder - contains packet counter and part of packet counter and packet counter
--           output is decoded to 1 to n code.
decoder: entity work.FL_EXTRACT_DECODER
  generic map(
   DECODER_WIDTH=>DW,
   POSITION_WIDTH=>PW
  )
  port map(
   CLK=>CLK,
   RESET=>RESET,
   SRC_RDY_N=>RX_SRC_RDY_N,
   DST_RDY_N=>TX_DST_RDY_N,
   EOP_N=>RX_EOP_N,
   EOF_N=>RX_EOF_N,
   HEAD_EN=>HEAD_EN,
   POSITION=>POSITION
  );

-- generate code when we don't need alignment 
gen8: if (OFFSET rem reduced_data_width + SIZE) <= (DATA_WIDTH/8) generate
  valid_in<= '1' when POSITION=conv_std_logic_vector(OFFSET / (DATA_WIDTH/8),PW) else '0';
  part_valid<=not RX_SRC_RDY_N and not TX_DST_RDY_N and HEAD_EN(PACKET_NO);
  data_valid<=valid_in and part_valid;

  EXT_DATA<=RX_DATA(OFFSET rem (DATA_WIDTH/8)*8 + SIZE*8-1 downto OFFSET rem (DATA_WIDTH/8)*8);
  EXT_DATA_VLD <= data_valid;
end generate gen8;

-- generate code when alignment is neccessery
gen3: if (OFFSET rem reduced_data_width + SIZE) > (DATA_WIDTH/8) generate

  -- first register
  process (clk, reset)
    begin
     if reset='1' then   --asynchronous reset active High
        EXT_DATA(first_reg_top downto 0) <= (others => '0');
     elsif (clk'event and clk='1' and WE(0)='1') then  -- clk rising edge
        EXT_DATA(first_reg_top downto 0) <= RX_DATA(first_reg_data_top downto first_reg_data_bottom);
     end if;
  end process;

  -- first register write enable
  WE(0)<=not RX_SRC_RDY_N and not TX_DST_RDY_N and HEAD_EN(PACKET_NO) when POSITION=conv_std_logic_vector(OFFSET / reduced_data_width,PW) else '0';

  -- generate when there is one register at the end which have width lower then DATA_WIDTH 
  gen5: if rem_of_ful_reg/=0 generate
    -- generate registers with width of DATA_WIDTH
    gen4: for i in 1 to number_of_ful_reg generate
      -- in registers
      process (clk, reset)
        begin
          if reset='1' then   --asynchronous reset active High
            EXT_DATA(i*DATA_WIDTH+in_reg_out-1 downto (i-1)*DATA_WIDTH+in_reg_out) <= (others => '0');
          elsif (clk'event and clk='1' and WE(i)='1') then  -- clk rising edge
            EXT_DATA(i*DATA_WIDTH+in_reg_out-1 downto (i-1)*DATA_WIDTH+in_reg_out)<=RX_DATA;
        end if;
      end process;

      -- in registers write enable
      WE(i)<=not RX_SRC_RDY_N and not TX_DST_RDY_N and HEAD_EN(PACKET_NO)  when POSITION=conv_std_logic_vector((OFFSET+i*reduced_data_width) / reduced_data_width,PW) else '0';
    end generate gen4;

    -- last part of data will go directly to the output
    EXT_DATA( last_top downto last_bottom) <= RX_DATA(last_data_top downto 0);
    
    -- output data valid signal
    EXT_DATA_VLD<=not RX_SRC_RDY_N and not TX_DST_RDY_N and HEAD_EN(PACKET_NO) when POSITION=conv_std_logic_vector((OFFSET+(number_of_ful_reg+1)*reduced_data_width) / reduced_data_width,PW+5) else '0';
  end generate gen5;
  
  -- generate when there isn't one register at the end which have width lower then DATA_WIDTH, so we
  -- have to generate n-1 register (n is number of full registers) and the last part will go directly
  -- to the output
  gen6: if rem_of_ful_reg=0 generate
    -- generate registers with width of DATA_WIDTH
    gen7: for i in 1 to number_of_ful_reg-1 generate
      -- in registers
      process (clk, reset)
        begin
         if reset='1' then   --asynchronous reset active High
           EXT_DATA(i*DATA_WIDTH+in_reg_out-1 downto (i-1)*DATA_WIDTH+in_reg_out) <= (others => '0');
         elsif (clk'event and clk='1' and WE(i)='1') then  -- clk rising edge
           EXT_DATA(i*DATA_WIDTH+in_reg_out-1 downto (i-1)*DATA_WIDTH+in_reg_out)<=RX_DATA;
        end if;
      end process;

      -- in registers write enable
      WE(i)<=not RX_SRC_RDY_N and not TX_DST_RDY_N and HEAD_EN(PACKET_NO) when POSITION=conv_std_logic_vector((OFFSET+i*reduced_data_width) / reduced_data_width,PW) else '0';
    end generate gen7;

    -- last part of data will go directly to the output
    EXT_DATA( last_top downto last_top-DATA_WIDTH+1) <= RX_DATA;
    -- output data valid signal
    EXT_DATA_VLD<=not RX_SRC_RDY_N and not TX_DST_RDY_N and HEAD_EN(PACKET_NO) when POSITION=conv_std_logic_vector((OFFSET+number_of_ful_reg*reduced_data_width) / reduced_data_width,PW) else '0';
  end generate gen6;

end generate gen3;

end architecture full;
