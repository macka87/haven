-- i2c_master.vhd - I2C master
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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
-- NOTE: There is no synchronisation and arbitration on I2C bus. We suppose
--       that there is only one MASTER on the bus. For proper functionality
--       slave doesn't have to set SCL low, when MASTERs high period is not
--       over. Slave can hold scl low in MASTERs low period.
--


library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
-- -------------------------------------------------------
--                 Entity declaration
-- -------------------------------------------------------
entity i2c_master is
   port (
      RESET   : in    std_logic;
      CLK     : in    std_logic; -- 100MHz

      DEV     : in    std_logic_vector(6 downto 0); -- device address (maybe 8bit)
      ADDR    : in    std_logic_vector(7 downto 0); -- data word adress
      RW      : in    std_logic; -- read/write
      EN      : in    std_logic; -- enable
      DI      : in    std_logic_vector(7 downto 0);
      DO      : out   std_logic_vector(7 downto 0); -- valid when op_done asserted
      OP_OK   : out   std_logic;
      OP_DONE : out   std_logic;
      BUSY    : out   std_logic;
      STATE   : out   std_logic_vector(1 downto 0);

      -- I2C interface
      --SCL_T   : out std_logic;  -- tri-state enable ('Z' 
      SCL_O   : out std_logic; -- master generate clock
      SCL_I   : in  std_logic; -- but design is synchronised with wire-anded clock (for slave synchronisation)
      
      --SDA_T   : out std_logic
      SDA_O   : out std_logic;
      SDA_I   : in  std_logic
   );
end i2c_master;
-------------------------------------------------------------------------------

architecture full of i2c_master is
   
   signal clk_i2c_high    : std_logic;
   signal clk_i2c_low     : std_logic;
   signal clk_i2c         : std_logic;
   signal cnt_clk         : std_logic_vector(9 downto 0);
   signal clk_i2c_en      : std_logic;
   signal cnt             : std_logic_vector(3 downto 0);
   signal reg_dev         : std_logic_vector(6 downto 0);
   signal reg_addr        : std_logic_vector(7 downto 0);
   signal reg_data        : std_logic_vector(7 downto 0);
   signal reg_rw          : std_logic;
   signal reg_en          : std_logic;
   signal reg_do          : std_logic_vector(7 downto 0);
   signal done            : std_logic;
   signal reg_ack         : std_logic;
   signal start_cmd       : std_logic;

   signal reg_stop_cmd    : std_logic;
   signal reg_start_cmd   : std_logic;

   signal mx_dev          : std_logic;
   signal mx_addr         : std_logic;
   signal mx_data         : std_logic;
   signal mx_sda          : std_logic;

   signal fsm_op_ok       : std_logic;
   signal fsm_op_done     : std_logic;
   signal fsm_busy        : std_logic;
   signal fsm_start_cmd   : std_logic;
   signal fsm_stop_cmd    : std_logic;
   signal fsm_dev_rw      : std_logic;
   signal fsm_dev         : std_logic;
   signal fsm_addr        : std_logic;
   signal fsm_wr_data     : std_logic;
   signal fsm_rd_data     : std_logic;
   signal fsm_cnt_clr     : std_logic;
   signal fsm_store_state : std_logic;
   signal fsm_state       : std_logic_vector(1 downto 0);

begin
   -- I2C clock generation ----------------------------------------------------
   clk_i2c_high    <= '1' when (conv_integer(cnt_clk)=249) else '0'; -- for stop and start command assertion
   clk_i2c_low     <= '1' when (conv_integer(cnt_clk)=749) else '0'; -- for proper timing of data transmission

   clk_i2c_p: process(RESET, CLK)
   begin
      if (RESET='1') then
         clk_i2c <= '1';
      elsif (CLK'event and CLK='1') then
         if (conv_integer(cnt_clk)<500) then
            clk_i2c <= '1';
         else
            clk_i2c <= '0';
         end if;
      end if;
   end process;
   
   clk_i2c_en <= '0' when ((conv_integer(cnt_clk)<500) and SCL_I='0') else '1'; --slave needs more time...

   cnt_clk_p: process(RESET, fsm_busy, CLK)
   begin
      if (RESET='1' or fsm_busy='0') then
         cnt_clk <= "0011111001"; -- 249 - we will start from half of high pulse
      elsif (CLK'event and CLK='1') then
         if (clk_i2c_en='1') then
            if (conv_integer(cnt_clk)=999) then
               cnt_clk <= (others=>'0');
            else
               cnt_clk <= cnt_clk + 1;
            end if;
         end if;
      end if;
   end process;
   
   -- bit counter -------------------------------------------------------------
   cnt_p: process(RESET, CLK)
   begin
      if (RESET='1') then
         cnt <= (others=>'0');
      elsif (CLK'event and CLK='1') then
         if (fsm_cnt_clr='1') then
            cnt <= (others=>'0');
         elsif (clk_i2c_low='1' and (fsm_dev='1' or fsm_addr='1' or fsm_wr_data='1' or fsm_rd_data='1')) then -- data changes in low clk
            if ((conv_integer(cnt)=8)) then
               cnt <= (others=>'0');
            else
               cnt <= cnt + 1;
            end if;
         end if;
      end if;
   end process;

   done <= '1' when (conv_integer(cnt)=8) else '0';
     
   -- registers ---------------------------------------------------------------
   reg_p: process(RESET, CLK)
   begin
      if (RESET='1') then
         reg_dev  <= (others=>'0');
         reg_addr <= (others=>'0');
         reg_data <= (others=>'0');
         reg_rw   <= '0';
      elsif (CLK'event and CLK='1') then
         if (EN='1' and fsm_busy='0') then
            reg_dev  <= DEV;
            reg_addr <= ADDR;
            reg_data <= DI;
            reg_rw   <= RW;
         end if;
      end if;
   end process;

   -- --------- output data shift register ------------------------------------
   reg_do_p: process(RESET, CLK) -- fixme may be reg_data
   begin
      if (RESET='1') then
         reg_do <= (others=>'0');
      elsif (CLK'event and CLK='1') then
         if (clk_i2c_high='1' and fsm_rd_data='1' and done='0') then -- don't save ack
            reg_do(7) <= reg_do(6);
            reg_do(6) <= reg_do(5);
            reg_do(5) <= reg_do(4);
            reg_do(4) <= reg_do(3);
            reg_do(3) <= reg_do(2);
            reg_do(2) <= reg_do(1);
            reg_do(1) <= reg_do(0);
            reg_do(0) <= SDA_I;
         end if;
      end if;
   end process;

   reg_ack_p: process(RESET, CLK)
   begin
      if (RESET='1') then
         reg_ack <= '0';
      elsif(CLK'event and CLK='1') then
         if (clk_i2c_high='1') then
            reg_ack <= not SDA_I;
         end if;
      end if;
   end process;

   reg_stop_cmd_p: process(RESET, CLK)
   begin
      if (RESET='1') then
         reg_stop_cmd <= '0';
      elsif(CLK'event and CLK='1') then
         if (clk_i2c_high='1') then
            reg_stop_cmd <= '1';
         elsif (clk_i2c_low='1') then
            reg_stop_cmd <= '0';
         end if;
      end if;
   end process;

   reg_start_cmd_p: process(RESET, CLK)
   begin
      if (RESET='1') then
         reg_start_cmd <= '0';
      elsif(CLK'event and CLK='1') then
         if (clk_i2c_high='1') then
            reg_start_cmd <= '0';
         elsif (clk_i2c_low='1') then
            reg_start_cmd <= '1';
         end if;
      end if;
   end process;

   -- multiplexors ------------------------------------------------------------
   mx_dev <= reg_dev(6) when (conv_integer(cnt)=0) else
             reg_dev(5) when (conv_integer(cnt)=1) else
             reg_dev(4) when (conv_integer(cnt)=2) else
             reg_dev(3) when (conv_integer(cnt)=3) else
             reg_dev(2) when (conv_integer(cnt)=4) else
             reg_dev(1) when (conv_integer(cnt)=5) else
             reg_dev(0) when (conv_integer(cnt)=6) else
             fsm_dev_rw when (conv_integer(cnt)=7) else
             '1';

   mx_addr <= reg_addr(7) when (conv_integer(cnt)=0) else -- dont'care bit for 1K eeprom
              reg_addr(6) when (conv_integer(cnt)=1) else
              reg_addr(5) when (conv_integer(cnt)=2) else
              reg_addr(4) when (conv_integer(cnt)=3) else
              reg_addr(3) when (conv_integer(cnt)=4) else
              reg_addr(2) when (conv_integer(cnt)=5) else
              reg_addr(1) when (conv_integer(cnt)=6) else
              reg_addr(0) when (conv_integer(cnt)=7) else
              '1';

   mx_data <= reg_data(7) when (conv_integer(cnt)=0) else
              reg_data(6) when (conv_integer(cnt)=1) else
              reg_data(5) when (conv_integer(cnt)=2) else
              reg_data(4) when (conv_integer(cnt)=3) else
              reg_data(3) when (conv_integer(cnt)=4) else
              reg_data(2) when (conv_integer(cnt)=5) else
              reg_data(1) when (conv_integer(cnt)=6) else
              reg_data(0) when (conv_integer(cnt)=7) else
              '1';
   
   mx_sda <= reg_start_cmd when (fsm_start_cmd='1')   else
             mx_dev        when (fsm_dev='1')         else
             mx_addr       when (fsm_addr='1')        else
             mx_data       when (fsm_wr_data='1')     else
             reg_stop_cmd  when (fsm_stop_cmd='1')    else
             '1';

   -- FSM instantination ---------------------------------------------------
   FSM_U : entity work.i2c_master_fsm
   port map (
      RESET     => RESET,
      CLK       => CLK,
      
      EN        => EN,
      DONE      => done,
      ACK       => reg_ack,
      RW        => reg_rw,
      LOP       => clk_i2c_low,
      
      OP_OK     => fsm_op_ok,
      OP_DONE   => fsm_op_done,
      BUSY      => fsm_busy,
      
      START_CMD => fsm_start_cmd,
      STOP_CMD  => fsm_stop_cmd,
      DEV_RW    => fsm_dev_rw,
      CNT_CLR   => fsm_cnt_clr,

      DEV       => fsm_dev,
      ADDR      => fsm_addr,
      WR_DATA   => fsm_wr_data,
      RD_DATA   => fsm_rd_data,
      STATE     => fsm_state,
      STORE_STATE => fsm_store_state
   );

   reg_state_p: process(RESET, CLK)
   begin
      if (RESET='1') then
         STATE <= (others=>'0');
      elsif(CLK'event and CLK='1') then
         if (fsm_store_state='1') then
            STATE <= fsm_state;
         end if;
      end if;
   end process;

   ----------------------------------------------------------------------------
   SDA_O   <= mx_sda   when (fsm_busy='1') else '1'; -- 1 when bus is free
   SCL_O   <= '1'      when (fsm_stop_cmd='1' and reg_stop_cmd='1') else -- in ending part of stop_cmd, SCL must be 1
               clk_i2c when (fsm_busy='1') else              
              '1'; -- 1 when bus is free
   OP_OK   <= fsm_op_ok;
   OP_DONE <= fsm_op_done;
   BUSY    <= fsm_busy;
   DO      <= reg_do;

end full;
