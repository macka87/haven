--
-- rx.vhd: Input buffer for EMAC - RX part
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
--            Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use work.math_pack.all;
use work.ibuf_emac_pkg.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity ibuf_emac_rx is
   generic (
      -- Determines if FCS is passed to the IBUF (true) or not (false).
      INBANDFCS	     : boolean := true
   );
   port (
      -- Input common signals
      CLK            : in std_logic; -- EMAC clock
      RESET          : in std_logic; -- Asynchronous reset, active in '1'
      CE             : in std_logic; -- EMAC clock enable

      -- Input data
      DI             : in std_logic_vector(7 downto 0);
      DI_DV          : in std_logic;

      -- EMAC signals that separate packets, active in '1'
      GOOD_FRAME     : in std_logic;
      BAD_FRAME      : in std_logic;

      -- EMAC statistic data
      RX_STAT        : in std_logic_vector(6 downto 0);
      RX_STAT_VLD    : in std_logic;

      -- Output data
      DO             : out std_logic_vector(7 downto 0);
      DO_DV          : out std_logic;

      -- Packet control
      SOP            : out std_logic;
      EOP            : out std_logic;
      FRAME_SENT     : out std_logic;
      FRAME_ERR      : out std_logic;

      -- Statistic data
      TX_STAT        : out t_ibuf_emac_rx_stat;
      TX_STAT_VLD    : out std_logic;
      CRC_ERROR      : out std_logic;
      CRC_ERROR_VLD  : out std_logic
   );

end entity ibuf_emac_rx;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ibuf_emac_rx is

   -- Signal declaration
   -- pipeline stage 1
   signal reg1_data           : std_logic_vector(7 downto 0);
   signal reg1_data_vld       : std_logic;
   signal reg1_frame_sent     : std_logic;
   signal reg1_frame_err      : std_logic;

   -- statistic information
   signal reg_stat_vector     : std_logic_vector(26 downto 0);
   signal reg_stat_vld        : std_logic;
   signal cnt_stat_part       : std_logic_vector(3 downto 0);

   -- pipeline stage 2
   signal reg2_data           : std_logic_vector(7 downto 0);
   signal reg2_data_vld       : std_logic;
   signal reg2_frame_sent     : std_logic;
   signal reg2_frame_err      : std_logic;
   
   -- pipeline stage 3
   signal reg3_data           : std_logic_vector(7 downto 0);
   signal reg3_data_vld       : std_logic;
   signal reg3_frame_sent     : std_logic;
   signal reg3_frame_err      : std_logic;
   
   -- pipeline stage 4
   signal reg4_sop            : std_logic;
   signal reg4_data           : std_logic_vector(7 downto 0);
   signal reg4_data_vld       : std_logic;
   signal reg4_frame_sent     : std_logic;
   signal reg4_frame_err      : std_logic;
   
   -- pipeline stage 5
   signal reg5_data           : std_logic_vector(7 downto 0);
   signal reg5_data_vld       : std_logic;
   signal reg5_frame_sent     : std_logic;
   signal reg5_frame_err      : std_logic;
   
   -- pipeline stage 6
   signal reg6_data           : std_logic_vector(7 downto 0);
   signal reg6_data_vld       : std_logic;
   signal reg6_frame_sent     : std_logic;
   signal reg6_frame_err      : std_logic;
   
   -- pipeline stage 7
   signal reg7_data           : std_logic_vector(7 downto 0);
   signal reg7_data_vld       : std_logic;
   signal reg7_frame_sent     : std_logic;
   signal reg7_frame_err      : std_logic;

   -- pipeline stage 8
   signal reg8_sop            : std_logic;
   signal reg8_data           : std_logic_vector(7 downto 0);
   signal reg8_data_vld       : std_logic;
   signal reg8_frame_sent     : std_logic;
   signal reg8_frame_err      : std_logic;

begin

   -- -------------------------------------------------------------------------
   --                          Pipeline stage 1
   -- -------------------------------------------------------------------------

   -- register reg1_data
   reg1_datap: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg1_data <= DI;
         end if;
      end if;
   end process;

   -- register reg1_data_vld
   reg1_data_vldp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg1_data_vld <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg1_data_vld <= DI_DV;
         end if;
      end if;
   end process;

   -- register reg1_frame_sent
   reg1_frame_sentp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg1_frame_sent <= GOOD_FRAME or BAD_FRAME;
         end if;
      end if;
   end process;

   -- register reg1_frame_err
   reg1_frame_errp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg1_frame_err <= BAD_FRAME;
         end if;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                        Statistic information
   -- -------------------------------------------------------------------------
   
   -- register reg_stat_vector
   reg_stat_vectorp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CE = '1' and RX_STAT_VLD = '1') then
            if (cnt_stat_part(0) = '1') then
               reg_stat_vector(6 downto 0) <= RX_STAT;
            end if;
            if (cnt_stat_part(1) = '1') then
               reg_stat_vector(13 downto 7) <= RX_STAT;
            end if;
            if (cnt_stat_part(2) = '1') then
               reg_stat_vector(20 downto 14) <= RX_STAT;
            end if;
            if (cnt_stat_part(3) = '1') then
               reg_stat_vector(26 downto 21) <= RX_STAT(5 downto 0);
            end if;
         end if;
      end if;
   end process;

   -- register reg_stat_vld
   reg_stat_vldp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_stat_vld <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_stat_vld <= CE and RX_STAT_VLD and cnt_stat_part(3);
      end if;
   end process;

   -- cnt_stat_part counter
   cnt_stat_partp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_stat_part <= "0001";
      elsif (CLK'event AND CLK = '1') then
         if (CE = '1' and RX_STAT_VLD = '1') then
            cnt_stat_part <= cnt_stat_part(2 downto 0) & cnt_stat_part(3);
         end if;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                          Pipeline stage 2
   -- -------------------------------------------------------------------------

   -- register reg2_data
   reg2_datap: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg2_data <= reg1_data;
         end if;
      end if;
   end process;

   -- register reg2_data_vld
   reg2_data_vldp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg2_data_vld <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg2_data_vld <= reg1_data_vld;
         end if;
      end if;
   end process;

   -- register reg2_frame_sent
   reg2_frame_sentp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg2_frame_sent <= reg1_frame_sent;
         end if;
      end if;
   end process;

   -- register reg2_frame_err
   reg2_frame_errp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg2_frame_err <= reg1_frame_err;
         end if;
      end if;
   end process;
   
   
   -- -------------------------------------------------------------------------
   --                          Pipeline stage 3
   -- -------------------------------------------------------------------------
 
   -- register reg3_data
   reg3_datap: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg3_data <= reg2_data;
         end if;
      end if;
   end process;

   -- register reg3_data_vld
   reg3_data_vldp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg3_data_vld <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg3_data_vld <= reg2_data_vld;
         end if;
      end if;
   end process;

   -- register reg3_frame_sent
   reg3_frame_sentp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg3_frame_sent <= reg2_frame_sent;
         end if;
      end if;
   end process;

   -- register reg3_frame_err
   reg3_frame_errp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg3_frame_err <= reg2_frame_err;
         end if;
      end if;
   end process;
   
   
   -- -------------------------------------------------------------------------
   --                          Pipeline stage 4
   -- -------------------------------------------------------------------------
   
   -- register reg4_data
   reg4_datap: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg4_data <= reg3_data;
         end if;
      end if;
   end process;

   -- register reg4_data_vld
   reg4_data_vldp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg4_data_vld <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg4_data_vld <= reg3_data_vld;
         end if;
      end if;
   end process;

   -- register reg4_frame_sent
   reg4_frame_sentp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg4_frame_sent <= reg3_frame_sent;
         end if;
      end if;
   end process;

   -- register reg4_frame_err
   reg4_frame_errp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CE = '1') then
            reg4_frame_err <= reg3_frame_err;
         end if;
      end if;
   end process;
   

   -- -------------------------------------------------------------------------
   --                            Generic pipeline length
   -- -------------------------------------------------------------------------

   -- short pipeline
   pipeline_short : if (INBANDFCS = true) generate 
   begin

      -- register reg4_sop
      reg4_sopp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg4_sop <= '0';
         elsif (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg4_sop <= not reg4_data_vld and reg3_data_vld;
            end if;
         end if;
      end process;
   
      -- ----------------------------------------------------------------------
      --                           Output interface
      -- ----------------------------------------------------------------------
      
      SOP                  <= reg4_sop and CE;
      EOP                  <= reg4_data_vld and not reg3_data_vld and CE;
      DO                   <= reg4_data;
      DO_DV                <= reg4_data_vld and CE;
      FRAME_SENT           <= reg4_frame_sent and CE;
      FRAME_ERR            <= reg4_frame_err and CE;
      TX_STAT.STAT_VECTOR  <= reg_stat_vector;
      TX_STAT_VLD          <= reg_stat_vld;
      CRC_ERROR            <= RX_STAT(EMAC_STAT_VECTOR_FCS_ERR);
      CRC_ERROR_VLD        <= CE and RX_STAT_VLD and cnt_stat_part(0);

   end generate pipeline_short;

   
   -- long pipeline
   pipeline_long : if (INBANDFCS = false) generate 
   
      -- ----------------------------------------------------------------------
      --                          Pipeline stage 5
      -- ----------------------------------------------------------------------

      -- register reg5_data
      reg5_datap: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg5_data <= reg4_data;
            end if;
         end if;
      end process;

      -- register reg5_data_vld
      reg5_data_vldp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg5_data_vld <= '0';
         elsif (CLK'event AND CLK = '1') then
            if (CE = '1') then
              reg5_data_vld <= reg4_data_vld;
            end if;
         end if;
      end process;

      -- register reg5_frame_sent
      reg5_frame_sentp: process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg5_frame_sent <= reg4_frame_sent;
            end if;
         end if;
      end process;

      -- register reg5_frame_err
      reg5_frame_errp: process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg5_frame_err <= reg4_frame_err;
            end if;
         end if;
      end process;
   
   
   
      -- ----------------------------------------------------------------------
      --                          Pipeline stage 6
      -- ----------------------------------------------------------------------

      -- register reg6_data
      reg6_datap: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg6_data <= reg5_data;
            end if;
         end if;
      end process;

      -- register reg6_data_vld
      reg6_data_vldp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg6_data_vld <= '0';
         elsif (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg6_data_vld <= reg5_data_vld;
            end if;
         end if;
      end process;

      -- register reg6_frame_sent
      reg6_frame_sentp: process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg6_frame_sent <= reg5_frame_sent;
            end if;
         end if;
      end process;

      -- register reg6_frame_err
      reg6_frame_errp: process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg6_frame_err <= reg5_frame_err;
            end if;
         end if;
      end process;
     
 
      -- ----------------------------------------------------------------------
      --                          Pipeline stage 7
      -- ----------------------------------------------------------------------

      -- register reg7_data
      reg7_datap: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg7_data <= reg6_data;
            end if;
         end if;
      end process;

      -- register reg7_data_vld
      reg7_data_vldp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg7_data_vld <= '0';
         elsif (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg7_data_vld <= reg6_data_vld;
            end if;
         end if;
      end process;

      -- register reg7_frame_sent
      reg7_frame_sentp: process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg7_frame_sent <= reg6_frame_sent;
            end if;
         end if;
      end process;

      -- register reg7_frame_err
      reg7_frame_errp: process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg7_frame_err <= reg6_frame_err;
            end if;
         end if;
      end process;

      
      -- ----------------------------------------------------------------------
      --                          Pipeline stage 8
      -- ----------------------------------------------------------------------
      
      -- register reg8_sop
      reg8_sopp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg8_sop <= '0';
         elsif (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg8_sop <= not reg8_data_vld and reg7_data_vld;
            end if;
         end if;
      end process;

      -- register reg8_data
      reg8_datap: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg8_data <= reg7_data;
            end if;
         end if;
      end process;

      -- register reg8_data_vld
      reg8_data_vldp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg8_data_vld <= '0';
         elsif (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg8_data_vld <= reg7_data_vld;
            end if;
         end if;
      end process;

      -- register reg8_frame_sent
      reg8_frame_sentp: process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg8_frame_sent <= reg7_frame_sent;
            end if;
         end if;
      end process;

      -- register reg8_frame_err
      reg8_frame_errp: process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg8_frame_err <= reg7_frame_err;
            end if;
         end if;
      end process;


      -- ----------------------------------------------------------------------
      --                           Output interface
      -- ----------------------------------------------------------------------
   
      SOP                  <= reg8_sop and CE;
      EOP                  <= reg8_data_vld and not reg7_data_vld and CE;
      DO                   <= reg8_data;
      DO_DV                <= reg8_data_vld and CE;
      FRAME_SENT           <= reg8_frame_sent and CE;
      FRAME_ERR            <= reg8_frame_err and CE;
      TX_STAT.STAT_VECTOR  <= reg_stat_vector;
      TX_STAT_VLD          <= reg_stat_vld;
      CRC_ERROR            <= RX_STAT(EMAC_STAT_VECTOR_FCS_ERR);
      CRC_ERROR_VLD        <= CE and RX_STAT_VLD and cnt_stat_part(0);

   end generate pipeline_long;

end architecture full;
