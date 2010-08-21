-- lctrl.vhd: Liberouter control component
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas  <martinek@liberouter.org>
--            Korenek Jan     <korenek@liberouter.org>
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
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of LCTRL is
   -- ID constant
   constant C_SWR_LEN : std_logic_vector(3 downto 0)  := "0111";

   -- internal registers
   signal reg_irq       : std_logic_vector(7 downto 0);
   signal reg_irq_mask  : std_logic_vector(7 downto 0);
   signal masked_irq    : std_logic_vector(7 downto 0);
   signal reg_irq_mask_we  : std_logic;
   signal reg_sw_reset     : std_logic;
   signal reg_adc_do       : std_logic_vector(15 downto 0);

   signal mx_lctrl_do         : std_logic_vector(15 downto 0);
   signal reg_lctrl_do        : std_logic_vector(15 downto 0);
   signal reg_lctrl_do1       : std_logic_vector(15 downto 0);
   signal reg_adc_addr        : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal reg_adc_addr1       : std_logic_vector(ADDR_WIDTH-1 downto 0);

   -- address decoder signals
   signal adc_di        : std_logic_vector(15 downto 0);
   signal adc_do        : std_logic_vector(15 downto 0);
   signal adc_addr      : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal adc_drdy      : std_logic;
   signal adc_drdy1     : std_logic;
   signal adc_drdy2     : std_logic;
   signal adc_drdy3     : std_logic;
   signal adc_rw        : std_logic;
   signal adc_en        : std_logic;

   signal cs_reg_irq_mask : std_logic;
   signal cs_sw_reset     : std_logic;
   signal cs_id           : std_logic;

   -- Reset counter
   signal sw_reset_we     : std_logic;
   signal cmp_neq_zero    : std_logic;
   signal cnt_sw_reset    : std_logic_vector(3 downto 0) := (others => '0');

   signal id_address      : std_logic_vector(7  downto 0);
   signal id_data_we      : std_logic;
   signal id_data_in      : std_logic_vector(15 downto 0);
   signal id_data_out     : std_logic_vector(15 downto 0);

begin

-- ---------------------------- Local bus --------------------------------
LBCOMMEM_U : entity work.lbconn_mem 
generic map ( 
   BASE       => BASE,
   ADDR_WIDTH => ADDR_WIDTH
)              
port map ( 
   DATA_OUT => adc_di,
   DATA_IN  => reg_adc_do,
   ADDR     => adc_addr,
   RW       => adc_rw,
   EN       => adc_en,
   SEL      => open,
   DRDY     => adc_drdy3,
   ARDY     => '1',

   -- local bus interconnection 
   RESET   => RESET,
   LBCLK   => LBCLK,
   LBFRAME => LBFRAME,
   LBAS    => LBAS,
   LBRW    => LBRW,
   LBLAST  => LBLAST,
   LBAD    => LBAD,
   LBHOLDA => LBHOLDA,
   LBRDY   => LBRDY
);

-- ---------------------------- ID component --------------------------------
   ID_U : entity work.ID_COMP 
   generic map(
      PROJECT_ID     => PROJECT_ID,
      SW_MAJOR       => SW_MAJOR,
      SW_MINOR       => SW_MINOR,
      HW_MAJOR       => HW_MAJOR,
      HW_MINOR       => HW_MINOR,
      PROJECT_TEXT   => PROJECT_TEXT
   )
   port map ( 
      -- ID component interface 
      CLK     => LBCLK,
      RESET   => RESET,

      ADDRESS => id_address,
      DATA_WE => id_data_we,
      DATA_IN => id_data_in,
      DATA_OUT=> id_data_out
   );

   id_data_we  <=  cs_id and adc_en and adc_rw;
   id_data_in  <=  adc_di;
   id_address  <=  "000"&adc_addr(4 downto 0);

-- ------------------------- Address decoder -----------------------------

-- -------- Pipelined signals ---------
reg_lb_pipe :  process (LBCLK, RESET)
begin  
   if (RESET = '1') then
      reg_adc_addr   <= (others=>'0');
      reg_adc_addr1  <= (others=>'0');
      adc_drdy1      <= '0';
      adc_drdy2      <= '0';
      adc_drdy3      <= '0';
      reg_lctrl_do   <= (others=>'0');
      reg_lctrl_do1  <= (others=>'0');
   elsif (LBCLK'event AND LBCLK = '1') then
      reg_adc_addr   <= adc_addr;
      reg_adc_addr1  <= reg_adc_addr;
      adc_drdy1      <= adc_en;
      adc_drdy2      <= adc_drdy1;
      adc_drdy3      <= adc_drdy2;
      reg_lctrl_do   <= mx_lctrl_do; 
      reg_lctrl_do1  <= reg_lctrl_do; 
   end if;
end process reg_lb_pipe;
   
-- ----- Chip select input decoder -----
process(adc_addr)
begin
   cs_reg_irq_mask   <= '0';
   cs_sw_reset       <= '0';
   cs_id             <= '0';

   if (adc_addr(5)='0') then 
         cs_id             <= '1';
   else
      case adc_addr(3 downto 0) is
         when "0100" => cs_reg_irq_mask   <= '1';
         when "0110" => cs_sw_reset       <= '1';
         when "0111" => cs_sw_reset       <= '1';
         when others =>
      end case;   
   end if;
end process;

-- ---- LCTRL Output Multiplexor -----
with adc_addr(3 downto 0) select
   mx_lctrl_do <=   "00000000"  & reg_irq          when "0010",
                    "00000000"  & reg_irq_mask     when "0100",
                    (others => '0')                when others;

-- ----- Output data multiplex -------
with reg_adc_addr1(5) select  adc_do  <=  id_data_out     when '0',
                                          reg_lctrl_do1   when others;

reg_irq_mask_we <= adc_en and adc_rw and cs_reg_irq_mask;
sw_reset_we     <= adc_en and adc_rw and cs_sw_reset;

-- --------------------------- SW reset ---------------------------------

SW_RESET    <= reg_sw_reset;

-- SW reset register
process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_sw_reset <= '0';
   elsif (LBCLK'event AND LBCLK = '1') then
      reg_sw_reset <= cmp_neq_zero;
   end if;
end process;

cmp_neq_zero <= '0' when (cnt_sw_reset = "0000") else '1';

-- reset counter
process(RESET, LBCLK)
begin
   if (RESET = '1') then
      cnt_sw_reset <= (others => '0');
   elsif (LBCLK'event AND LBCLK = '1') then
      if (sw_reset_we = '1') then
         cnt_sw_reset <= C_SWR_LEN;
      elsif (cmp_neq_zero='1') then
         cnt_sw_reset <= cnt_sw_reset - 1;
      end if;
   end if;
end process;

-- reg_adc_do register
process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_adc_do <= (others => '0');
   elsif (LBCLK'event AND LBCLK = '1') then
      reg_adc_do <= adc_do;
   end if;
end process;

-- ----------------------- Internal registers ----------------------------

-- reg_irq register
process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_irq <= (others => '0');
   elsif (LBCLK'event AND LBCLK = '1') then
      reg_irq <= IRQ_I;
   end if;
end process;

-- reg_irq_mask register
process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_irq_mask <= (others => '0');
   elsif (LBCLK'event AND LBCLK = '1') then
      if (reg_irq_mask_we = '1') then
         reg_irq_mask <= adc_di(reg_irq_mask'length -1  downto 0);
      end if;
   end if;
end process;

masked_irq <= reg_irq and reg_irq_mask;

-- ----------------------- Interface mapping ----------------------------
IRQ <= masked_irq(0) or masked_irq(1) or masked_irq(2) or masked_irq(3) or
       masked_irq(4) or masked_irq(5) or masked_irq(6) or masked_irq(7);

end architecture full;
-- ----------------------------------------------------------------------------
