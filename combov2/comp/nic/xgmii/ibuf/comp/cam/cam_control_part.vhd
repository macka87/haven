--
-- cam_control_part.vhd: Controls CAM reading and writing operations
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IBUF_CAM_CONTROL is
   generic(
      -- Data row width (bits, should be a multiple of 4)
      CAM_ROW_WIDTH     : integer;
      -- Number of data rows (depth of the CAM)
      CAM_ROW_COUNT     : integer
   );
   port(
      -- Common signals
      CLK               : in std_logic;
      RESET             : in std_logic;
      -- Data incoming to CAM Data Array
      DATA_IN           : in std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
      --Vector of data found in cAM while reading
      ROW_DATA_OK_BUS   : in std_logic_vector(CAM_ROW_COUNT*CAM_ROW_WIDTH/4-1
                                                                     downto 0);
      -- Address of the row to work with
      ADDR              : in std_logic_vector(log2(CAM_ROW_COUNT)-1 downto 0);
      -- Write enable, active in '1'
      WRITE_EN          : in std_logic;
      -- Read enable, active in '1'
      READ_EN           : in std_logic;
      
      -- Selects write enable signal of one row
      WRITE_ENABLE_BUS  : out std_logic_vector(CAM_ROW_COUNT-1 downto 0);
      -- Bits to be written into CAM elements
      DATA_FILL_BUS     : out std_logic_vector(CAM_ROW_WIDTH/4-1 downto 0);
      -- DAta driven to CAM elements
      DATA_SRL          : out std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
      -- Data outgoing from CAM
      DATA_OUT          : out std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
      -- Asserted when CAM output data is valid
      DATA_OUT_VLD      : out std_logic;
      -- Asserted when CAM is not ready for another operation
      CAM_BUSY          : out std_logic
   );
end entity IBUF_CAM_CONTROL;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IBUF_CAM_CONTROL_ARCH of IBUF_CAM_CONTROL is

   -- Signal declaration
   signal row_data_ok_bus_mask   : std_logic_vector
                                   (CAM_ROW_COUNT*CAM_ROW_WIDTH/4-1 downto 0);
   signal reg_row_data_ok_bus_in : std_logic_vector
                                   (CAM_ROW_COUNT*CAM_ROW_WIDTH/4-1 downto 0);
   signal reg_row_data_ok_bus_n  : std_logic_vector
                                   (CAM_ROW_COUNT*CAM_ROW_WIDTH/4-1 downto 0);
   signal mx_data_ok_bus_n       : std_logic_vector(CAM_ROW_WIDTH/4-1 downto 0);
   signal read_data_srl          : std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
   signal mx_data_out            : std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
   signal mx_data_out_sel        : std_logic;

   signal wr_req                 : std_logic;
   signal rd_req                 : std_logic;

   signal cnt_16                 : std_logic_vector(3 downto 0);
   signal cnt_16_ce              : std_logic;
   signal cnt_16_ld              : std_logic;

   signal cmp_cnt_0              : std_logic;

   signal reg_cnt_wr_busy        : std_logic;
   signal reg_cnt_rd_busy        : std_logic;
   signal cnt_busy               : std_logic;

   signal reg_data_out_vld       : std_logic;

begin

   -- CAM Filling Part
   ibuf_cam_filling_parti: entity work.ibuf_cam_filling_part
      generic map(
         CAM_ROW_WIDTH     => CAM_ROW_WIDTH,
         CAM_ROW_COUNT     => CAM_ROW_COUNT
      )
      port map(
         CNT_16            => cnt_16,
         DATA_IN           => DATA_IN,
         RESET             => RESET,
         CLK               => CLK,
         DATA_FILL_BUS     => DATA_FILL_BUS
      );

   -- register reg_row_data_ok_bus_n input logic
   row_data_ok_bus_mask <= (others => cnt_16_ld);
   reg_row_data_ok_bus_in <= (not ROW_DATA_OK_BUS) or row_data_ok_bus_mask;

   -- register reg_row_data_ok_bus_n
   reg_row_data_ok_bus_np: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_row_data_ok_bus_n <= (others => '1');
      elsif (CLK'event AND CLK = '1') then
         reg_row_data_ok_bus_n <= reg_row_data_ok_bus_in;
      end if;
   end process;

   -- Generic multiplexer selects active row to be read
   gen_muxi: entity work.gen_mux
      generic map(
         DATA_WIDTH  => CAM_ROW_WIDTH/4,
         MUX_WIDTH   => CAM_ROW_COUNT
      )
      port map(
         DATA_IN     => reg_row_data_ok_bus_n,
         SEL         => ADDR,
         DATA_OUT    => mx_data_ok_bus_n
      );

   -- CAM Reading Part
   ibuf_cam_reading_parti: entity work.ibuf_cam_reading_part
      generic map(
         CAM_ROW_WIDTH     => CAM_ROW_WIDTH
      )
      port map(
         CLK               => CLK,
         RESET             => RESET,
         DATA_NEXT_BUS     => mx_data_ok_bus_n,
         READ_CNTS_RST     => cnt_16_ld,
   
         DATA_SRL          => read_data_srl,
         DATA_OUT          => DATA_OUT
      );

   -- multiplexor mx_data_out
   mx_data_out_sel <= reg_cnt_rd_busy;
   mx_data_outp: process(mx_data_out_sel, DATA_IN, read_data_srl)
   begin
      case mx_data_out_sel is
         when '0' => mx_data_out <= DATA_IN;
         when '1' => mx_data_out <= read_data_srl;
         when others => mx_data_out <= (others => 'X');
      end case;
   end process;

   -- Multiplexer is connected to the output
   DATA_SRL <= mx_data_out;

   -- Write enable bus decoder
   dec1fn_enablei: entity work.dec1fn_enable
      generic map(
         ITEMS       => CAM_ROW_COUNT
      )
      port map(
         ADDR        => ADDR,
         ENABLE      => reg_cnt_wr_busy,
         DO          => WRITE_ENABLE_BUS
      );

   -- Control logic
   wr_req      <= WRITE_EN and not cnt_busy;
   rd_req      <= READ_EN and not cnt_busy;
   cnt_16_ce   <= cnt_busy;
   cnt_16_ld   <= wr_req or rd_req;
   cnt_busy    <= reg_cnt_wr_busy or reg_cnt_rd_busy;

   -- Compares counter to be "0000"
   cmp_cnt_0p: process(cnt_16)
   begin
      if cnt_16 = "0000" then
         cmp_cnt_0 <= '1';
      else
         cmp_cnt_0 <= '0';
      end if;
   end process;

   -- cnt_16 counter
   cnt_16p: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_16 <= (others => '1');
      elsif (CLK'event AND CLK = '1') then
         if (cnt_16_ld = '1') then
            cnt_16 <= "1111";
         elsif (cnt_16_ce = '1') then
            cnt_16 <= cnt_16 - 1;
         end if;
      end if;
   end process;

   -- register reg_cnt_wr_busy
   reg_cnt_wr_busyp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_cnt_wr_busy <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_cnt_wr_busy <= (not cmp_cnt_0 and reg_cnt_wr_busy) or wr_req;
      end if;
   end process;

   -- register reg_cnt_rd_busy
   reg_cnt_rd_busyp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_cnt_rd_busy <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_cnt_rd_busy <= (not cmp_cnt_0 and reg_cnt_rd_busy) or rd_req;
      end if;
   end process;

   -- register reg_data_out_vld
   reg_data_out_vldp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_data_out_vld <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_data_out_vld <= reg_cnt_rd_busy and cmp_cnt_0;
      end if;
   end process;

   -- DATA_OUT_VLD output
   DATA_OUT_VLD <= reg_data_out_vld;

   -- CAM_BUSY output
   CAM_BUSY <= READ_EN or WRITE_EN or cnt_busy;

end architecture IBUF_CAM_CONTROL_ARCH;
