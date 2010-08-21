-- ddm_arch.vhd: descriptor download manager architecture
-- Copyright (C) 2009 CESNET
-- Author(s): Petr Kastovsky <kastovsky@liberouter.org>
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
-- KEYWORDS : TODO, DEBUG
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;
use work.pac_dma_pkg.all;
-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture ddm_behav of ddm is

   -- round up number to the multiple of 8
   function ROUND_UP8 ( number : integer) return integer is
   variable ret : integer;
   begin
      ret := (number / 8)*8;
      if ( (number mod 8) /= 0) then
         ret := ret + 8;
      end if;
      return ret;
   end function;

   constant FLOWS          : integer := 2*IFCS;

   type T_ARRAY is array (0 to FLOWS-1) of std_logic_vector(1 downto 0);

   -- Chipscope ICON
   component icon3 is
      port (
              CONTROL0 : inout std_logic_vector(35 downto 0);
              CONTROL1 : inout std_logic_vector(35 downto 0);
              CONTROL2 : inout std_logic_vector(35 downto 0)
           );
   end component;

   -- Chipscope ILA (144-bit trigger port)
   component ila144 is
      port (
              CONTROL : inout std_logic_vector(35 downto 0);
              CLK     : in std_logic;
              TRIG0   : in std_logic_vector(143 downto 0)
           );
   end component;

   -- Chipscope signals
   signal control0            : std_logic_vector(35 downto 0);
   signal control1            : std_logic_vector(35 downto 0);
   signal control2            : std_logic_vector(35 downto 0);
   signal ila144_trig0        : std_logic_vector(143 downto 0);
   signal ila144_trig1        : std_logic_vector(143 downto 0);
   signal ila144_trig2        : std_logic_vector(143 downto 0);

   attribute noopt : boolean;
   attribute dont_touch : boolean;

   attribute noopt of icon3    : component is TRUE;
   attribute noopt of ila144   : component is TRUE;
   attribute dont_touch of icon3    : component is TRUE;
   attribute dont_touch of ila144   : component is TRUE;

   constant BM_REQ_DISTMEM_TYPE : integer := 16;

   constant PAGE_WIDTH     : integer := log2(4096);
   constant DESC_WIDTH     : integer := log2(16);

   -- position of bit in descriptor first 8B
   -- next desc pointer, desc type 1
   constant DF_NEXTDESC    : integer := PAC_DMA_NDF + 32;

   constant gndvec         : std_logic_vector(63 downto 0) := X"0000000000000000";
   -- width of registers/registers arrays
   constant REG_WIDTH      : integer := 32;
   -- width of next desc pointer
   constant PTR_WIDTH      : integer := 64;
   -- request length width - optimized - we probably wont utilize whole 12b
   -- as defined in ib_bm record
   constant LEN_WIDTH      : integer := log2(BLOCK_SIZE) + 1;
   -- width of reqlen reg array - multiple of 8
   constant REQLEN_DW      : integer := ROUND_UP8(LEN_WIDTH);
   -- type of transaction - RAM2FPGA
   constant TRANS_TYPE     : std_logic_vector(1 downto 0) := "00";
   constant NFIFO_OUTPUT_REG : boolean := false;

   signal cnt_block_size : std_logic_vector(LEN_WIDTH-1 downto 0);
   signal cnt_block_size_ld : std_logic;
   signal block_cnt_up   : std_logic;
   signal block_size_nn  : std_logic;

   signal mx_do_regs       : std_logic_vector(31 downto 0);
   signal reg_mx_do_regs   : std_logic_vector(31 downto 0);
   signal reg_mi_sw_rd     : std_logic;

   signal cs_reg_control   : std_logic;
   signal cs_reg_status    : std_logic;
   signal cs_reg_head      : std_logic;
   signal cs_reg_tail      : std_logic;
   signal cs_ddm           : std_logic;

   -- concatenation ra means reg_array
   signal ra_control       : T_ARRAY;
   signal ra_control_we    : std_logic;
   signal ra_control_do    : std_logic_vector(REG_WIDTH-1 downto 0);
   signal ra_status        : T_ARRAY;
   signal ra_status_do     : std_logic_vector(REG_WIDTH-1 downto 0);

   signal ra_status_set_stp: std_logic_vector(FLOWS-1 downto 0);
   signal ra_status_set_pau: std_logic_vector(FLOWS-1 downto 0);
   signal ra_status_set_run: std_logic_vector(FLOWS-1 downto 0);

   signal control_stp      : std_logic_vector(FLOWS-1 downto 0);
   signal control_pau      : std_logic_vector(FLOWS-1 downto 0);
   signal control_run      : std_logic_vector(FLOWS-1 downto 0);

   signal status_running   : std_logic_vector(FLOWS-1 downto 0);
   signal status_stopped   : std_logic_vector(FLOWS-1 downto 0);

   signal ra_rxrf_wea      : std_logic;
   signal ra_rxrf_bea      : std_logic_vector(7 downto 0);
   signal ra_rxrf_addra    : std_logic_vector(log2(FLOWS/2)-1 downto 0);
   signal ra_rxrf_dia      : std_logic_vector(63 downto 0);
   signal ra_rxrf_doa      : std_logic_vector(63 downto 0);
   signal ra_rxrf_addrb    : std_logic_vector(log2(FLOWS/2)-1 downto 0);
   signal ra_rxrf_dob      : std_logic_vector(63 downto 0);
   signal ra_rxrf_sclr     : std_logic;

   signal reg_head_dia         : std_logic_vector(REG_WIDTH-1 downto 0);
   signal deb_ra_head_wea      : std_logic;
   signal deb_ra_head_bea      : std_logic_vector((REG_WIDTH/8)-1 downto 0);
   signal deb_ra_head_addra    : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal deb_ra_head_dia      : std_logic_vector(REG_WIDTH-1 downto 0);
   signal deb_ra_head_doa      : std_logic_vector(REG_WIDTH-1 downto 0);
   signal deb_ra_head_addrb    : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal deb_ra_head_dob      : std_logic_vector(REG_WIDTH-1 downto 0);
   signal deb_ra_head_sclr     : std_logic;
   signal ra_head_wea      : std_logic;
   signal ra_head_bea      : std_logic_vector((REG_WIDTH/8)-1 downto 0);
   signal ra_head_addra    : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal ra_head_dia      : std_logic_vector(REG_WIDTH-1 downto 0);
   signal ra_head_doa      : std_logic_vector(REG_WIDTH-1 downto 0);
   signal ra_head_addrb    : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal ra_head_dob      : std_logic_vector(REG_WIDTH-1 downto 0);
   signal ra_head_sclr     : std_logic;
   signal ra_tail_wea      : std_logic;
   signal ra_tail_bea      : std_logic_vector((REG_WIDTH/8)-1 downto 0);
   signal ra_tail_addra    : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal ra_tail_dia      : std_logic_vector(REG_WIDTH-1 downto 0);
   signal ra_tail_doa      : std_logic_vector(REG_WIDTH-1 downto 0);
   signal ra_tail_addrb    : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal ra_tail_dob      : std_logic_vector(REG_WIDTH-1 downto 0);
   signal ra_tail_sclr     : std_logic;
   signal ra_nextd_wea     : std_logic;
   signal ra_nextd_bea     : std_logic_vector((PTR_WIDTH/8)-1 downto 0);
   signal ra_nextd_addra   : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal ra_nextd_dia     : std_logic_vector(PTR_WIDTH-1 downto 0);
   signal ra_nextd_doa     : std_logic_vector(PTR_WIDTH-1 downto 0);
   signal ra_nextd_addrb   : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal ra_nextd_dob     : std_logic_vector(PTR_WIDTH-1 downto 0);
   signal ra_nextd_sclr    : std_logic;
   signal ra_reqlen_wea    : std_logic;
   signal ra_reqlen_bea    : std_logic_vector((REQLEN_DW/8)-1 downto 0);
   signal ra_reqlen_addra  : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal ra_reqlen_dia    : std_logic_vector(REQLEN_DW-1 downto 0);
   signal ra_reqlen_doa    : std_logic_vector(REQLEN_DW-1 downto 0);
   signal ra_reqlen_addrb  : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal ra_reqlen_dob    : std_logic_vector(REQLEN_DW-1 downto 0);
   signal ra_reqlen_sclr   : std_logic;
   
   signal mux_ra_head_addra   : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal mux_ra_head_addra_sel : std_logic;

   signal reg_ib_channel_index : std_logic_vector(log2(PAC_MAX_IFCS)-1 downto 0);
   signal ib_channel_index : std_logic_vector(log2(PAC_MAX_IFCS)-1 downto 0) := (others => '0');
   signal cs_desc_init     : std_logic;
   signal cmp_last_one     : std_logic;
   signal cmp_ib_index     : std_logic;
   signal last_one         : std_logic;
   signal we_fsm_stopped   : std_logic;
   signal flag_clear       : std_logic;
   signal fifo_we          : std_logic;
   signal nextd_we         : std_logic;
   signal nextd_select     : std_logic;
   signal nextd_increment  : std_logic_vector(15 downto 0);

   -- cnt counts each 8B of ib write - descriptor has 16B => has to have 
   -- doubled precision
   signal cnt_ibwords      : std_logic_vector(LEN_WIDTH downto 0);
   signal cnt_ibwords_ce   : std_logic;
   signal cnt_ibwords_ld   : std_logic;
   signal cnt_ibwords_ld_1 : std_logic;
   signal cnt_ibwords_clr  : std_logic;
   signal cnt_ibwords_inc1 : std_logic_vector(LEN_WIDTH downto 0);

   signal flags_get        : std_logic;
   signal flags_get_addr   : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal flags_set        : std_logic;
   signal flags_set_addr   : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal flags_clr        : std_logic;
   signal flags_clr_addr   : std_logic_vector(log2(FLOWS)-1 downto 0);

   signal req_fifo_not_full   : std_logic_vector(FLOWS-1 downto 0);
   signal mux_enabled_in      : std_logic_vector(FLOWS-1 downto 0);
   signal nextd_fsm_enabled   : std_logic_vector(0 downto 0);
   signal nextd_fsm_bm_req    : std_logic;
   signal nextd_fsm_bm_reqw1  : std_logic;
   signal nextd_fsm_bm_reqw2  : std_logic;
   signal length_we           : std_logic;

   signal cnt_nextd_fsm_index    : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal cnt_nextd_fsm_index_ce : std_logic;
   signal cnt_nextd_fsm_index_ld : std_logic;

   signal fifo_status_msb  : std_logic_vector(FLOWS-1 downto 0);
   signal fifo_status      : std_logic_vector(0 downto 0);
   signal not_fifo_status  : std_logic;
   
   signal bm_req_length          : std_logic_vector(LEN_WIDTH-1 downto 0);
   signal tail_min_head          : std_logic_vector(REG_WIDTH-1 downto 0);
   signal head_tail_diff         : std_logic;
   signal reg_tail_min_head      : std_logic_vector(31 downto 0);
   signal reg_tail_min_head_we   : std_logic;

   signal rx_nfifo_init       : std_logic_vector(IFCS-1 downto 0);
   signal rx_nfifo_din        : std_logic_vector(PTR_WIDTH-1 downto 0);
   signal rx_nfifo_waddr      : std_logic_vector(abs(log2(IFCS)-1) downto 0);
   signal rx_nfifo_wr         : std_logic;
   signal rx_nfifo_full       : std_logic_vector((IFCS)-1 downto 0);
   signal rx_nfifo_status     : std_logic_vector(log2(BLOCK_SIZE*2*2+1)*IFCS-1 downto 0);
 
   signal tx_nfifo_init       : std_logic_vector(IFCS-1 downto 0);
   signal tx_nfifo_din        : std_logic_vector(PTR_WIDTH-1 downto 0);
   signal tx_nfifo_waddr      : std_logic_vector(abs(log2(IFCS)-1) downto 0);
   signal tx_nfifo_wr         : std_logic;
   signal tx_nfifo_full       : std_logic_vector((IFCS)-1 downto 0);
   signal tx_nfifo_status     : std_logic_vector(log2(BLOCK_SIZE*2*2+1)*IFCS-1 downto 0);

   signal mux_req_di_sel      : std_logic;

   signal bm_req_di        : std_logic_vector(63 downto 0);
   signal bm_req_we        : std_logic;
   signal bm_req_addra     : std_logic_vector(0 downto 0);
   signal bm_req_addrb     : std_logic_vector(0 downto 0);
   signal bm_req_dob       : std_logic_vector(63 downto 0);

   -- BM interface
   signal bm_gaddr    : std_logic_vector(63 downto 0); -- Global Address 
   signal bm_laddr    : std_logic_vector(31 downto 0); -- Local Address
   signal bm_length   : std_logic_vector(11 downto 0); -- Length
   signal bm_tag      : std_logic_vector(15 downto 0); -- Operation TAG
   signal bm_ttype    : std_logic_vector(1  downto 0); -- Type of transaction

   signal mi_channel_index : std_logic_vector(log2(FLOWS)-1 downto 0);
   signal dec_mi_chid      : std_logic_vector(FLOWS-1 downto 0);

   signal reg_max_length : std_logic_vector(LEN_WIDTH-1 downto 0);
   signal max_length     : std_logic_vector(LEN_WIDTH-1 downto 0);
   signal page_rest      : std_logic_vector(PAGE_WIDTH-DESC_WIDTH downto 0);

   signal nd_s1      : std_logic;
   signal nd_s2      : std_logic;
   signal nd_s3      : std_logic;
   signal nd_s4      : std_logic;

   signal wl_s1      : std_logic;
   signal wl_s2      : std_logic;
   signal wl_s3      : std_logic;
   signal wl_s4      : std_logic;
   signal wl_s5      : std_logic;

   signal sDMA_DOUT  : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);

   signal sTX_NFIFO_DOUT     : std_logic_vector(63 downto 0);
   signal sTX_NFIFO_DOUT_VLD : std_logic;
   signal sTX_NFIFO_RADDR    : std_logic_vector(abs(log2(IFCS)-1) downto 0);
   signal sTX_NFIFO_RD       : std_logic;
   signal sTX_NFIFO_EMPTY    : std_logic_vector(IFCS-1 downto 0);

begin

   -- we are always ready for writting from IB
   IB_WR_RDY <= '1';

   -- RxReqFifo interface
   RX_RF_ADDR <= ra_rxrf_addrb;
   -- concatenation of global addr and request length
   -- length is given by number of descriptors
   RX_RF_DATA <= cnt_block_size & ra_rxrf_dob;
   -- DMA DONE has been received and index(0) = 0, i.e. rx flow
   RX_RF_DATA_VLD <= DMA_DONE and (not ib_channel_index(0)) and block_size_nn; 
   cnt_block_size_ld <= DMA_DONE and (not ib_channel_index(0)) and block_size_nn;

   block_size_nn <= '0' when cnt_block_size = gndvec(cnt_block_size'length-1 downto 0)
                        else '1';
   gen_rx_rf_init_i: for i in 0 to IFCS-1 generate
      RX_RF_INIT(i) <= status_stopped(2*i);
--       ra_rxrf_sclr  <= status_stopped(2*i);
   end generate;


-- cnt_block_size counter
cnt_block_sizep: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         cnt_block_size <= (others => '0');
      elsif (cnt_block_size_ld = '1') then
            cnt_block_size <= (others => '0');
         elsif (block_cnt_up = '1' and ib_channel_index(0) = '0') then
            cnt_block_size <= cnt_block_size + 1;
      end if;
   end if;
end process;

-- registers of rx descriptors download requests global addresses
reg_array_rxrf_gaddr: entity work.reg_array_be
   generic map (
      DATA_WIDTH  => 64,
      ITEMS       => FLOWS/2,
      INIT_DATA   => gndvec(63 downto 0)
   )
   port map (
      CLK   => CLK,
      SCLR  => ra_rxrf_sclr,
      -- read/write PORT
      WEA   => ra_rxrf_wea,
      BEA   => ra_rxrf_bea,
      ADDRA => ra_rxrf_addra,
      DIA   => ra_rxrf_dia,
      DOA   => ra_rxrf_doa,
      -- readonly PORT
      ADDRB => ra_rxrf_addrb,
      DOB   => ra_rxrf_dob
   );


   ra_rxrf_sclr <= '0';
   ra_rxrf_wea <= length_we and (not cnt_nextd_fsm_index(0)); 
   ra_rxrf_bea <= (others => '1');
   ra_rxrf_addra <= cnt_nextd_fsm_index(cnt_nextd_fsm_index'length - 1 downto 1);
   ra_rxrf_dia <= ra_nextd_dob;

   ra_rxrf_addrb <= ib_channel_index(log2(FLOWS)-1 downto 1);
-- ----------------------------------------------------------------------------
-- MI address decoder to access registers 
-- ----------------------------------------------------------------------------
mi_channel_index <= MI_SW_ADDR(log2(PAC_MI32_ADDR_MAX) + log2(FLOWS)-1 
                               downto log2(PAC_MI32_ADDR_MAX));

dec1fn_mi_channel_index_i: entity work.dec1fn
   generic map (
      ITEMS    => FLOWS
   )
   port map (
      ADDR     => mi_channel_index,
      DO       => dec_mi_chid
   );


adr_dec : process(MI_SW_ADDR)
begin
   cs_reg_control    <= '0';
   cs_reg_status     <= '0';
   cs_reg_head       <= '0';
   cs_reg_tail       <= '0';

   case (MI_SW_ADDR(4 downto 2)) is
      when "000" => cs_reg_control    <= '1';
      when "001" => cs_reg_status     <= '1';
      when "010" => cs_reg_head       <= '1';
      when "011" => cs_reg_tail       <= '1';
      when others => null;
   end case;
end process;

cs_ddm <= cs_reg_control or cs_reg_status or cs_reg_head or cs_reg_tail;

ra_control_we  <= cs_reg_control AND MI_SW_WR;
ra_tail_wea    <= cs_reg_tail    AND MI_SW_WR;

-- output multiplexor
with MI_SW_ADDR(4 downto 2) select
mx_do_regs <=  ra_control_do     when "000",
               ra_status_do      when "001",
               deb_ra_head_dob   when "010",
               ra_tail_doa       when "011",
               (others => '0')   when others;

ra_control_do <= gndvec(REG_WIDTH-1 downto 2) & 
                 ra_control(conv_integer(mi_channel_index));

ra_status_do  <= gndvec(REG_WIDTH-1 downto 2) & 
                 ra_status(conv_integer(mi_channel_index));


-- register reg_mx_do_regs ----------------------------------------------------
reg_mx_do_regsp : process(CLK)
begin
   if (CLK'event and CLK = '1') then
      reg_mx_do_regs <= mx_do_regs;
   end if;
end process;

-- register reg_mi_sw_rd ------------------------------------------------------
reg_mi_sw_rdp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      reg_mi_sw_rd <= MI_SW_RD and cs_ddm;
   end if;
end process;

-- we have only registers here
MI_SW_ARDY <= (MI_SW_WR OR MI_SW_RD) and cs_ddm;
MI_SW_DRDY <= reg_mi_sw_rd;
MI_SW_DRD  <= reg_mx_do_regs;

-- ----------------------------------------------------------------------------
-- ra control register array
-- ----------------------------------------------------------------------------
gen_ra_control: for i in 0 to FLOWS-1 generate
   
   -- register ra_control ------------------------------------------------------
   ra_controlp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            ra_control(i) <= (others => '0');
         elsif (ra_control_we = '1' and dec_mi_chid(i) = '1') then
            ra_control(i) <= MI_SW_DWR(1 downto 0);
         end if;
      end if;
   end process;
   control_run(i) <= '1' when ra_control(i) = "10" else '0';
   control_stp(i) <= '1' when ra_control(i) = "00" else '0';
   control_pau(i) <= '1' when ra_control(i) = "01" else '0';

end generate;

INIT <= control_stp and status_stopped;
RUN <= control_run;
-- ----------------------------------------------------------------------------
-- ra status register array
-- ----------------------------------------------------------------------------
gen_ra_status: for i in 0 to FLOWS-1 generate
   
   -- register ra_status ------------------------------------------------------
   ra_statusp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            ra_status(i) <= (others => '0');
         elsif (ra_status_set_stp(i) = '1') then
            ra_status(i) <= "00";
         elsif (ra_status_set_pau(i) = '1') then
            ra_status(i) <= "01";
         elsif (ra_status_set_run(i) = '1') then
            ra_status(i) <= "10";
         end if;
      end if;
   end process;

   ra_status_set_run(i) <= '1' when ra_control_we = '1' and 
                                    dec_mi_chid(i) = '1' and
                                    MI_SW_DWR(1 downto 0) = "10"
                               else '0';

   ra_status_set_stp(i) <= control_stp(i) and IDLE(i) and status_running(i);
   ra_status_set_pau(i) <= control_pau(i) and IDLE(i) and status_running(i);

   status_running(i) <= '1' when ra_status(i) = "10" else '0';
   status_stopped(i) <= '1' when ra_status(i) = "00" else '0';

end generate;

-- write port - head update from we logic
-- read port - next desc fsm
-- driver does not need to know head value
reg_array_head_i: entity work.reg_array_be
   generic map (
      DATA_WIDTH  => REG_WIDTH,
      ITEMS       => FLOWS,
      INIT_DATA   => gndvec(REG_WIDTH-1 downto 0)
   )
   port map (
      CLK   => CLK,
      SCLR  => ra_head_sclr,
      -- read/write PORT
      WEA   => ra_head_wea,
      BEA   => ra_head_bea,
      ADDRA => ra_head_addra,
      DIA   => ra_head_dia,
      DOA   => ra_head_doa,
      -- readonly PORT
      ADDRB => ra_head_addrb,
      DOB   => ra_head_dob
   );

-- clear head when stop is set in status register
ra_head_sclr   <= status_stopped(conv_integer(ra_head_addra));

ra_head_bea    <= not gndvec(ra_head_bea'length -1 downto 0);
-- ordinary desc arrived to fifo - update only once for 16B
ra_head_wea    <= nextd_we AND nextd_select;
ra_head_addra  <= mux_ra_head_addra;
-- accumulate new descriptor
ra_head_dia    <= reg_head_dia;

ra_head_addrb  <= cnt_nextd_fsm_index;
DMA_IFC        <= cnt_nextd_fsm_index;


-- register reg_head_dia ------------------------------------------------------
reg_head_diap: process(RESET, CLK)
begin
   if (CLK'event AND CLK = '1') then
      reg_head_dia <= ra_head_doa + conv_std_logic_vector(1, REG_WIDTH);
   end if;
end process;

----- DEBUG -------------------------
reg_array_head_debug_i: entity work.reg_array_be
   generic map (
      DATA_WIDTH  => REG_WIDTH,
      ITEMS       => FLOWS,
      INIT_DATA   => gndvec(REG_WIDTH-1 downto 0)
   )
   port map (
      CLK   => CLK,
      SCLR  => ra_head_sclr,
      -- read/write PORT
      WEA   => ra_head_wea,
      BEA   => ra_head_bea,
      ADDRA => ra_head_addra,
      DIA   => ra_head_dia,
      DOA   => deb_ra_head_doa,
      -- readonly PORT
      ADDRB => deb_ra_head_addrb,
      DOB   => deb_ra_head_dob
   );

deb_ra_head_addrb  <= mi_channel_index;
----- DEBUG END -------------------------

-- select addra - if we are doing desc init, then the address
-- has to be set accordingly, most probably the channel is stopped
-- and head initialization is done (sclr = 1)
mux_ra_head_addra_sel <= cs_desc_init;
-- multiplexor mux_ra_head_addra ------------------------------------------------------
mux_ra_head_addrap: process(mux_ra_head_addra_sel, ib_channel_index, IB_WR_ADDR)
begin
   case mux_ra_head_addra_sel is
      when '0' => mux_ra_head_addra <= ib_channel_index(log2(FLOWS)-1 downto 0);
      when '1' => mux_ra_head_addra <= IB_WR_ADDR(3+log2(FLOWS)-1 downto 3);
      when others => mux_ra_head_addra <= (others => 'X');
   end case;
end process;

-- tail register array -- writable from sw
reg_array_tail_i: entity work.reg_array_be
   generic map (
      DATA_WIDTH  => REG_WIDTH,
      ITEMS       => FLOWS,
      INIT_DATA   => gndvec(REG_WIDTH-1 downto 0)
   )
   port map (
      CLK   => CLK,
      SCLR  => ra_tail_sclr,
      -- read/write PORT
      WEA   => ra_tail_wea,
      BEA   => ra_tail_bea,
      ADDRA => ra_tail_addra,
      DIA   => ra_tail_dia,
      DOA   => ra_tail_doa,
      -- readonly PORT
      ADDRB => ra_tail_addrb,
      DOB   => ra_tail_dob
   );

-- do not clear this as software is responsible for proper initialization
ra_tail_sclr   <= '0';
ra_tail_bea    <= MI_SW_BE;
ra_tail_addra  <= mi_channel_index;
ra_tail_dia    <= MI_SW_DWR;

ra_tail_addrb  <= cnt_nextd_fsm_index;
-- ----------------------------------------------------------------------------
-- IB address decoder
-- ----------------------------------------------------------------------------
   -- index of DMA channel, there are PAC_MAX_IFCS-1 channels at maximum
   -- one channel is reserved for descriptor initialization
ib_channel_index <= IB_WR_ADDR(12+log2(PAC_MAX_IFCS)-1 downto 12); 
   -- indicates descriptor initialization access
cs_desc_init <= '1' when (ib_channel_index = not gndvec(log2(PAC_MAX_IFCS)-1 downto 0)) else '0';


-- register reg_ib_channel_index ------------------------------------------------------
reg_ib_channel_indexp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      reg_ib_channel_index <= ib_channel_index;
   end if;
end process;

cmp_ib_index <= '1' when (ib_channel_index = reg_ib_channel_index) else '0';
-- ----------------------------------------------------------------------------
-- next descriptor register array
-- ----------------------------------------------------------------------------
-- next_desc register array -- writable from ib
reg_array_next_desc_i: entity work.reg_array_be
   generic map (
      DATA_WIDTH  => PTR_WIDTH,
      ITEMS       => FLOWS,
      INIT_DATA   => gndvec(PTR_WIDTH-1 downto 0)
   )
   port map (
      CLK   => CLK,
      SCLR  => ra_nextd_sclr,
      -- read/write PORT
      WEA   => ra_nextd_wea,
      BEA   => ra_nextd_bea,
      ADDRA => ra_nextd_addra,
      DIA   => ra_nextd_dia,
      DOA   => ra_nextd_doa,
      -- readonly PORT
      ADDRB => ra_nextd_addrb,
      DOB   => ra_nextd_dob
   );

-- do not clear this as software is responsible for proper initialization
ra_nextd_sclr  <= '0';
ra_nextd_wea   <= nextd_we;

ra_nextd_addrb <= cnt_nextd_fsm_index;

-- multiplexor MUX_NEXTD_ADDRA -------------------------------------------------
MUX_NEXTD_ADDRAp: process(cs_desc_init, ib_channel_index, IB_WR_ADDR)
begin
   case cs_desc_init is
      when '0' => ra_nextd_addra <= ib_channel_index(log2(FLOWS)-1 downto 0);
      when '1' => ra_nextd_addra <= IB_WR_ADDR(3+log2(FLOWS)-1 downto 3);
      when others => ra_nextd_addra <= (others => 'X');
   end case;
end process;

-- multiplexor MUX_NEXTD_BEA ------------------------------------------------------
MUX_NEXTD_BEAp: process(nextd_select, IB_WR_BE)
begin
   case nextd_select is
      when '0' => ra_nextd_bea <= IB_WR_BE;
      when '1' => ra_nextd_bea <= conv_std_logic_vector(3, ra_nextd_bea'length);
      when others => ra_nextd_bea <= (others => 'X');
   end case;
end process;

-- we should never overflow page size, hence we can
-- optimize adder to only the 16 lowest bits
nextd_increment <= ra_nextd_doa(15 downto 0) + X"0010";
-- multiplexor MUX_NEXTD_DIA ------------------------------------------------------
MUX_NEXTD_DIAp: process(nextd_select, IB_WR_DATA, nextd_increment)
begin
   case nextd_select is
      when '0' => ra_nextd_dia <= IB_WR_DATA;
      when '1' => ra_nextd_dia <= gndvec(47 downto 0) & nextd_increment;
      when others => ra_nextd_dia <= (others => 'X');
   end case;
end process;

-- ----------------------------------------------------------------------------
-- request length register array - to proper detection of download end
-- ----------------------------------------------------------------------------
reg_array_request_length_i: entity work.reg_array_be
   generic map (
      DATA_WIDTH  => REQLEN_DW,
      ITEMS       => FLOWS,
      INIT_DATA   => gndvec(REQLEN_DW-1 downto 0)
   )
   port map (
      CLK   => CLK,
      SCLR  => ra_reqlen_sclr,
      -- read/write PORT
      WEA   => ra_reqlen_wea,
      BEA   => ra_reqlen_bea,
      ADDRA => ra_reqlen_addra,
      DIA   => ra_reqlen_dia,
      DOA   => ra_reqlen_doa,
      -- readonly PORT
      ADDRB => ra_reqlen_addrb,
      DOB   => ra_reqlen_dob
   );

-- clear when stopped
ra_reqlen_sclr   <= '0'; -- status_stopped(conv_integer(ra_reqlen_addra));
ra_reqlen_wea    <= length_we;
ra_reqlen_bea    <= (others => '1');
ra_reqlen_addra  <= cnt_nextd_fsm_index;
-- store number of descriptors, i.e. size_of_transfer/16
ra_reqlen_dia    <= gndvec(REQLEN_DW-1 downto LEN_WIDTH) & bm_req_length;

ra_reqlen_addrb  <= ib_channel_index(log2(FLOWS)-1 downto 0);

-- ----------------------------------------------------------------------------
-- we logic fsm + additional components
-- ----------------------------------------------------------------------------
we_logic_fsm_i: entity work.we_logic_fsm
   port map (
      -- global signals 
      CLK            => CLK,
      RESET          => RESET,

      -- input signals
      WR_REQ         => IB_WR_REQ,
      STOPPED        => we_fsm_stopped,
      DESC_TYPE      => IB_WR_DATA(DF_NEXTDESC),
      DESC_INIT      => cs_desc_init,
      LAST_ONE       => last_one,
      
      WL_S1          => wl_s1,
      WL_S2          => wl_s2,
      WL_S3          => wl_s3,
      WL_S4          => wl_s4,
      WL_S5          => wl_s5,

      -- output signals
      FLAG_CLEAR     => flag_clear,
      FIFO_WE        => fifo_we,
      BLOCK_CNT      => block_cnt_up,
      NEXTD_WE       => nextd_we,
      NEXTD_SELECT   => nextd_select,   -- ib.data (0),  nextd increment (1)
      CNT_CLR        => cnt_ibwords_clr
   );

we_fsm_stopped <= status_stopped(conv_integer(
                                 ib_channel_index(log2(FLOWS)-1 downto 0)
                                ));

cnt_ibwords_inc1 <= cnt_ibwords + conv_std_logic_vector(1, cnt_ibwords'length);

cmp_last_one <= '1' when 
         (ra_reqlen_dob(LEN_WIDTH-1 downto 0) = cnt_ibwords_inc1(LEN_WIDTH downto 1))
               else '0';

last_one <= cmp_last_one and cmp_ib_index;

-- cnt_ibwords counter
cnt_ibwordsp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         cnt_ibwords <= (others => '0');
      elsif (cnt_ibwords_ce = '1') then
         if (cnt_ibwords_ld = '1') then
            cnt_ibwords <= (others => '0');
         elsif (cnt_ibwords_ld_1 = '1') then
            cnt_ibwords <= conv_std_logic_vector(1, cnt_ibwords'length);
         else
            cnt_ibwords <= cnt_ibwords + 1;
         end if;
      end if;
   end if;
end process;

-- enable clock only when writting descriptors after DMA request,i.e. not init
-- or when clear
cnt_ibwords_ce <= (IB_WR_REQ and (not cs_desc_init) and 
     (not status_stopped(conv_integer(ib_channel_index(log2(FLOWS)-1 downto 0))))
                  ) or cnt_ibwords_ld or cnt_ibwords_ld_1;

cnt_ibwords_ld <= cnt_ibwords_clr;
cnt_ibwords_ld_1 <= (not cmp_ib_index) and IB_WR_REQ;

-- ----------------------------------------------------------------------------
-- desc flags - lock to prevent more than one simultaneous DMAs for one channel
-- ----------------------------------------------------------------------------
desc_flags_i: entity work.SYNC_FLAGS
   generic map (
      ITEMS       => FLOWS,
      DATA_WIDTH  => 1
   )
   port map (
      CLK      => CLK,
      RESET    => RESET,

      -- get value
      GET      => flags_get,
      -- get address
      GET_ADDR => flags_get_addr,
      -- set enable
      SET      => flags_set,
      -- set address
      SET_ADDR => flags_set_addr,
      -- clear enable
      CLR      => flags_clr,
      -- clear address
      CLR_ADDR => flags_clr_addr

   );

flags_get_addr <= cnt_nextd_fsm_index;
flags_set_addr <= cnt_nextd_fsm_index;
flags_clr      <= flag_clear;
flags_clr_addr <= ib_channel_index(log2(FLOWS)-1 downto 0);
-- ----------------------------------------------------------------------------
-- next desc fsm - fsm for DMA request generating
-- ----------------------------------------------------------------------------
next_desc_fsm_i: entity work.next_desc_fsm
   port map (
      -- global signals 
      CLK            => CLK,
      RESET          => RESET,

      -- input signals
      ENABLED        => nextd_fsm_enabled(0), -- control from sw
      HEAD_TAIL_DIFF => head_tail_diff,       -- difference of head and tail
      FIFO_HEMPTY    => not_fifo_status,      -- fifo is half empty
      DMA_ACK        => DMA_ACK,            -- bm req has been acked
      DESC_FLAG      => flags_get,            -- next desc semafor value

      DEC_S_INIT     => nd_s1,
      DEC_S_REQ_W1   => nd_s2,
      DEC_S_REQ_W2   => nd_s3,
      DEC_S_WACK     => nd_s4,
      -- output signals
      NEXT_FLOW      => cnt_nextd_fsm_index_ce, -- change to next channel
      DESC_FLAG_SET  => flags_set,              -- set semafor
      BM_REQ         => nextd_fsm_bm_req,           -- generate request
      BM_REQW1       => nextd_fsm_bm_reqw1,
      BM_REQW2       => nextd_fsm_bm_reqw2,
      REGISTER_LEN   => reg_tail_min_head_we,   -- store tail-head to register
      LENGTH_WE      => length_we               -- write to ra_reqlen
   );

-- force counting up to FLOWS - 1
cnt_nextd_fsm_index_ld <= '1' when (cnt_nextd_fsm_index = 
                  conv_std_logic_vector(FLOWS - 1, cnt_nextd_fsm_index'length))
                  else '0';

-- cnt_nextd_fsm_index counter
cnt_nextd_fsm_indexp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         cnt_nextd_fsm_index <= (others => '0');
      elsif (cnt_nextd_fsm_index_ce = '1') then
         if (cnt_nextd_fsm_index_ld = '1') then
            cnt_nextd_fsm_index <= (others => '0');
         else
            cnt_nextd_fsm_index <= cnt_nextd_fsm_index + 1;
         end if;
      end if;
   end if;
end process;

-- mux_fifo_status_i fifo status multiplexor - select status according to index
mux_fifo_status_i: entity work.gen_mux
   generic map (
      DATA_WIDTH  => 1,
      MUX_WIDTH   => FLOWS
   )
   port map (
      DATA_IN  => fifo_status_msb,
      SEL      => cnt_nextd_fsm_index,
      DATA_OUT => fifo_status
   );

not_fifo_status <= not fifo_status(0);

gen_req_fifo_not_full: for i in 0 to IFCS-1 generate
   req_fifo_not_full(2*i) <= not RX_RF_FULL(i); -- indicate fullness of rx_rf
   req_fifo_not_full(2*i+1) <= '1'; -- there is no tx_rf hence always 1
end generate;

mux_enabled_in <= status_running and req_fifo_not_full;
-- mux_fifo_status_i fifo status multiplexor - select enable according to index
mux_enabled_i: entity work.gen_mux
   generic map (
      DATA_WIDTH  => 1,
      MUX_WIDTH   => FLOWS
   )
   port map (
      DATA_IN  => mux_enabled_in,
      SEL      => cnt_nextd_fsm_index,
      DATA_OUT => nextd_fsm_enabled
   );

-- maybe length of operands should be optimized according to ring size
tail_min_head  <= ra_tail_dob - ra_head_dob;
-- head_tail_diff is 1 when (tail - head != 0)
head_tail_diff <= '1' when (ra_tail_dob /= ra_head_dob)
                      else '0';

-- register reg_tail_min_head ------------------------------------------------------
reg_tail_min_headp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         reg_tail_min_head <= (others => '0');
      elsif (reg_tail_min_head_we = '1') then
         reg_tail_min_head <= tail_min_head;
      end if;
   end if;
end process;


page_rest <= ('1' & gndvec(PAGE_WIDTH-DESC_WIDTH-1 downto 0)) - 
             ('0' & ra_nextd_dob(PAGE_WIDTH-1 downto DESC_WIDTH));

max_length <= conv_std_logic_vector(BLOCK_SIZE, max_length'length)
     when (
     page_rest > conv_std_logic_vector(BLOCK_SIZE, page_rest'length)
     )
     else page_rest(max_length'length-1 downto 0);


-- register reg_max_length ------------------------------------------------------
reg_max_lengthp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      reg_max_length <= max_length;
   end if;
end process;

-- bm_req_length <= min(tail-head, BLOCK_SIZE);
bm_req_length <=  reg_max_length
     when (
     reg_tail_min_head > (gndvec(31 downto LEN_WIDTH) & reg_max_length)
     )
     else reg_tail_min_head(LEN_WIDTH-1 downto 0); -- we transfer 512 DESC at maximum

-- ----------------------------------------------------------------------------
-- bm req memory
-- ----------------------------------------------------------------------------
   -- BM signals assignment
   bm_gaddr <= ra_nextd_dob;
   bm_laddr <= BASE_ADDR + ( gndvec(31 downto log2(FLOWS) + 12) &
                                      cnt_nextd_fsm_index &
                                      gndvec(11 downto 0));

   -- desc. num * 16, i.e.  sizeof(desc)
   bm_length <= gndvec(11 downto 4+LEN_WIDTH) & bm_req_length & "0000";
   bm_tag    <= gndvec(DMA_TAG'length-1 downto DMA_ID'length) & DMA_ID;
   bm_ttype  <= TRANS_TYPE;


-- output multiplexor for DMA DOUT
-- multiplex 64bits of bm request to generic DMA_DATA_WIDTH
mux_dma_dout_i: entity work.gen_mux
   generic map (
      DATA_WIDTH => DMA_DATA_WIDTH,
      MUX_WIDTH  => 64/DMA_DATA_WIDTH
   )
   port map (
      DATA_IN  => bm_req_dob,
      SEL      => DMA_ADDR(DMA_ADDR'length-2 downto 0),
      DATA_OUT => sDMA_DOUT
   );

   DMA_DOUT <= sDMA_DOUT;

-- read first/second word of bm request
bm_req_addrb(0) <= DMA_ADDR(DMA_ADDR'length-1);

-- 2*64bit memory, store dma request as two parts
bm_req_mem_i: entity work.DP_DISTMEM
   generic map (
      -- one DMA  request == 2*64b
      DATA_WIDTH  => 64, 
      ITEMS       => 2,
      DISTMEM_TYPE=> BM_REQ_DISTMEM_TYPE,
      DEBUG       => false
   )
   port map (
      RESET    => RESET,

      DI       => bm_req_di,
      WE       => bm_req_we,
      WCLK     => CLK,
      ADDRA    => bm_req_addra,
      DOA      => open,

      ADDRB    => bm_req_addrb,
      DOB      => bm_req_dob
   );

-- write one part of dma request to memory
bm_req_we      <= nextd_fsm_bm_reqw1 or nextd_fsm_bm_reqw2;
-- if we are writting second word, set address to 1
bm_req_addra(0)<= nextd_fsm_bm_reqw2;
mux_req_di_sel <= nextd_fsm_bm_reqw2;
-- multiplexor mux_req_di ------------------------------------------------------
mux_req_dip: process(mux_req_di_sel, bm_laddr, bm_tag, bm_length, bm_ttype, 
                                     bm_gaddr)
begin
   case mux_req_di_sel is
      when '0' => bm_req_di <= bm_laddr & bm_tag &
                               bm_length & "00" & bm_ttype;
      when '1' => bm_req_di <= bm_gaddr;
      when others => bm_req_di <= (others => 'X');
   end case;
end process;

-- internal bus busmater signals
DMA_REQ  <= nextd_fsm_bm_req;
bm_ttype <= TRANS_TYPE;

-- ----------------------------------------------------------------------------
-- nfifos -- separated for rx and tx
-- ----------------------------------------------------------------------------
rx_nfifo_i: entity work.nfifo
  generic map (
    DATA_WIDTH => PTR_WIDTH,
    FLOWS      => IFCS,
    -- BLOCK_SIZE - max number of desc transfered in one DMA transfer
    -- *2 items per descriptor
    -- *2 there has to be space for enough descriptors
    BLOCK_SIZE => BLOCK_SIZE*2*2,
    LUT_MEMORY => NFIFO_LUT_MEMORY,
    OUTPUT_REG => NFIFO_OUTPUT_REG
  )
  port map (
    CLK         => CLK,
    RESET       => RESET,
    INIT        => rx_nfifo_init,

    -- Write interface
    DATA_IN     => rx_nfifo_din,
    WR_BLK_ADDR => rx_nfifo_waddr,
    WRITE       => rx_nfifo_wr,
    FULL        => rx_nfifo_full,

    -- Read interface
    DATA_OUT    => RX_NFIFO_DOUT,
    DATA_VLD    => RX_NFIFO_DOUT_VLD,
    RD_BLK_ADDR => RX_NFIFO_RADDR,
    READ        => RX_NFIFO_RD,
    PIPE_EN     => RX_NFIFO_RD,
    EMPTY       => RX_NFIFO_EMPTY,

    STATUS      => rx_nfifo_status
  );

rx_nfifo_wr    <= fifo_we and (not ib_channel_index(0));
rx_nfifo_din   <= IB_WR_DATA;
rx_nfifo_waddr <= ib_channel_index(log2(IFCS)-1 +1 downto 1);
   
   GEN_RX_STATUS: for i in 0 to IFCS-1 generate
      fifo_status_msb(2*i) <= rx_nfifo_status((i+1)*log2(BLOCK_SIZE*2*2+1) - 2);
   end generate;

tx_nfifo_i: entity work.nfifo
  generic map (
    DATA_WIDTH => PTR_WIDTH,
    FLOWS      => IFCS,
    -- BLOCK_SIZE - max number of desc transfered in one DMA transfer
    -- *2 items per descriptor
    -- *2 there has to be space for enough descriptors
    BLOCK_SIZE => BLOCK_SIZE*2*2,
    LUT_MEMORY => NFIFO_LUT_MEMORY,
    OUTPUT_REG => NFIFO_OUTPUT_REG
  )
  port map (
    CLK         => CLK,
    RESET       => RESET,
    INIT        => tx_nfifo_init,

    -- Write interface
    DATA_IN     => tx_nfifo_din,
    WR_BLK_ADDR => tx_nfifo_waddr,
    WRITE       => tx_nfifo_wr,
    FULL        => tx_nfifo_full,

    -- Read interface
    DATA_OUT    => sTX_NFIFO_DOUT,
    DATA_VLD    => sTX_NFIFO_DOUT_VLD,
    RD_BLK_ADDR => sTX_NFIFO_RADDR,
    READ        => sTX_NFIFO_RD,
    PIPE_EN     => sTX_NFIFO_RD,
    EMPTY       => sTX_NFIFO_EMPTY,

    STATUS      => tx_nfifo_status
  );

TX_NFIFO_DOUT     <= sTX_NFIFO_DOUT;
TX_NFIFO_DOUT_VLD <= sTX_NFIFO_DOUT_VLD;
sTX_NFIFO_RADDR   <= TX_NFIFO_RADDR;
sTX_NFIFO_RD      <= TX_NFIFO_RD;
TX_NFIFO_EMPTY    <= sTX_NFIFO_EMPTY;


tx_nfifo_wr    <= fifo_we and ib_channel_index(0);
tx_nfifo_din   <= IB_WR_DATA;
tx_nfifo_waddr <= ib_channel_index(log2(IFCS)-1 +1 downto 1);

   GEN_TX_STATUS: for i in 0 to IFCS-1 generate
      fifo_status_msb(2*i+1) <= tx_nfifo_status((i+1)*log2(BLOCK_SIZE*2*2+1) - 2);
   end generate;

   -- clear nfifo on set stop
   GEN_INIT: for i in 0 to IFCS-1 generate
      rx_nfifo_init(i) <= ra_status_set_stp(2*i);
      tx_nfifo_init(i) <= ra_status_set_stp(2*i+1);
   end generate;

-- -------------------------------------------------------------------------
--                             CHIPSCOPE
-- -------------------------------------------------------------------------
CHIPSCOPE_I: if (false) generate begin
   ICON3_I : icon3
   port map(  
              CONTROL0 => control0,
              CONTROL1 => control1,
              CONTROL2 => control2
           );

   ila144_trig0 <=  "0000" & "0000" & "0000" & "0000" -- 16
                  & "0000" & "0000" & "0000" & "0000" -- 16
                  & "0000" & "0000" & "0000" & "0000" -- 16
                  & "0000" & "0000" & "0000" & "0000" -- 16
                  & "0000"                   -- 68
                  & flags_clr                --  1
                  & flags_clr_addr           --  2
                  & flags_set_addr           --  2
                  & flags_get_addr           --  2
                  & DMA_ADDR                 --  2
                  & sDMA_DOUT                -- 32
                  & DMA_DONE                 --  1
                  & DMA_TAG                  -- 16
                  & cnt_nextd_fsm_index      --  2
                  & nd_s4                    --  1
                  & nd_s3                    --  1
                  & nd_s2                    --  1
                  & nd_s1                    --  1
                  & nextd_fsm_enabled(0)     --  1
                  & head_tail_diff           --  1
                  & not_fifo_status          --  1
                  & DMA_ACK                  --  1
                  & flags_get                --  1
                  & cnt_nextd_fsm_index_ce   --  1
                  & flags_set                --  1
                  & nextd_fsm_bm_req         --  1
                  & nextd_fsm_bm_reqw1       --  1
                  & nextd_fsm_bm_reqw2       --  1
                  & reg_tail_min_head_we     --  1
                  & length_we;               --  1


   ILA144_I0 : ila144
   port map(  
              CONTROL => control0,
              CLK     => CLK,
              TRIG0   => ila144_trig0
           );

   ila144_trig1 <=  "0000" & "0000" & "0000" & "0000" -- 16
                  & "0000" & "00"            -- 22
                  & IB_WR_ADDR               -- 32
                  & IB_WR_DATA               -- 64
                  & IB_WR_BE                 --  8
                  & IB_WR_REQ                --  1
                  & '1'                      --  1
                  & wl_s5                    --  1
                  & wl_s4                    --  1
                  & wl_s3                    --  1
                  & wl_s2                    --  1
                  & wl_s1                    --  1
                  & IB_WR_REQ                --  1
                  & we_fsm_stopped           --  1
                  & IB_WR_DATA(DF_NEXTDESC)  --  1
                  & cs_desc_init             --  1
                  & last_one                 --  1
                  & flag_clear               --  1
                  & fifo_we                  --  1
                  & block_cnt_up             --  1
                  & nextd_we                 --  1
                  & nextd_select             --  1
                  & cnt_ibwords_clr;         --  1


   ILA144_I1 : ila144
   port map(
              CONTROL => control1,
              CLK     => CLK,
              TRIG0   => ila144_trig1
           );

   ila144_trig2 <= "00000"                     --  5
                   & tx_nfifo_init             --  2
                   & tx_nfifo_din              -- 64
                   & tx_nfifo_waddr            --  1
                   & tx_nfifo_wr               --  1
                   & tx_nfifo_full             --  2
                   & sTX_NFIFO_DOUT            -- 64
                   & sTX_NFIFO_DOUT_VLD        --  1
                   & sTX_NFIFO_RADDR           --  1
                   & sTX_NFIFO_RD              --  1
                   & sTX_NFIFO_EMPTY;          --  2
                                               --===
                                               --144
   ILA144_I2 : ila144
   port map(
              CONTROL => control2,
              CLK     => CLK,
              TRIG0   => ila144_trig2
           );

end generate;
-- -------------------------------------------------------------------------
--                             END OF DEBUG
-- -------------------------------------------------------------------------
end architecture ddm_behav;
