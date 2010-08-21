 --
-- pcie_tx_generator.vhd : PCIE TX generator
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


-- -------------------------
-- Interface from IB_DECODER
----------------------------
--                          25         22   14        2       0
-- ------------------------------------------------------------
-- |          RESERVED        | FIRST_BE | TAG  | LEN |  TYPE |
-- |                          | SRC_ADDR | G2LR |     |       |
-- ------------------------------------------------------------
-- |     ADDR_HIGH/RESERVED   |         ADDR_LOW              |
-- |                          | LOWER_ADDR | REQ_ID | CPL_TAG |
-- ------------------------------------------------------------
-- |            DATA1         |           DATA0               |
-- ------------------------------------------------------------

-- TYPE:          "00"  - Read
--                "10"  - Write
--                "11"  - Completition
-- LEN:           Length in bytes, 12 bits
-- TAG:           Transaction TAG, 8 bit (G2LR Tag, or CPL Tag)
-- FIRST_BE:      (Valid for Write and Completitions)
--                "000" - 1st byte valid 
--                "001" - 2th byte valid
--                "010" - 3th byte valid
--                "011" - 4th byte valid
--                "100" - 5th byte valid
--                     .
--                     .
-- SRC_ADDR:     (Valid for Reads)
-- ADDR_LOW:     Low Write address (32 bit)  - Valid for Read and Write
-- ADDR_HIGH:    High write address (32 bit) - Valid for Read and Write
-- REQUESTER_ID: Requester ID (16 bitu)   - Valid for Completitions
-- LOWER_ADDR:   (7bit) Lower address       - Valid for completitions
-- DATAx:        Data a) First valid byte is denoted by FIST_BE for
--               (Write and Completitions)


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity PCIE_TX_GENERATOR is
  generic (   
     OUTPUT_REG_EN    : boolean := true
     );
  port (
    -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N           : in  std_logic; 
      TRN_CLK               : in  std_logic; 
                                                                         
    -- ----------- PCIe Generator interface ----------------------------------
      GEN_DATA              : in  std_logic_vector( 63 downto 0 );    -- Data or Header
      GEN_SOP_N             : in  std_logic;                          -- Start of Packet
      GEN_EOP_N             : in  std_logic;                          -- End of Packet
      GEN_SRC_RDY_N         : in  std_logic;                          -- Source Ready
      GEN_DST_RDY_N         : out std_logic;                          -- Destination Ready
      GEN_DW4               : in  std_logic;
      GEN_DW4_VLD           : in  std_logic;
                                                                         
    -- PCI Express TX interface ---------------------------------------------
      TRN_LNK_UP_N          : in  std_logic;                          -- Transaction Link Up
      TRN_TD                : out std_logic_vector(63 downto 0);      -- Transmit Data
      TRN_TREM_N            : out std_logic_vector(7 downto 0);       -- Transmit Data Reminder
      TRN_TSOF_N            : out std_logic;                          -- Transmit SOF
      TRN_TEOF_N            : out std_logic;                          -- Transmit EOF
      TRN_TSRC_RDY_N        : out std_logic;                          -- Trnasmit Source Ready
      TRN_TDST_RDY_N        : in  std_logic;                          -- Transmit Destination Ready
      TRN_TBUF_AV           : in  std_logic_vector(3 downto 0);       -- Transmit Buffers Available
                                                                      -- trn_tbuf_av[0] => Non Posted Queue
                                                                      -- trn_tbuf_av[1] => Posted Queue
                                                                      -- trn_tbuf_av[2] => Completion Queue
    -- PCI Express Configuration interface ----------------------------------
      CFG_BUS_NUMBER        : in  std_logic_vector(7 downto 0);       -- Bus number
      CFG_DEVICE_NUMBER     : in  std_logic_vector(4 downto 0);       -- Device Number
      CFG_FUNCTION_NUMBER   : in  std_logic_vector(2 downto 0);       -- Function number
      CFG_DCOMMAND          : in  std_logic_vector(15 downto 0)       -- cfg_dcommand[14:12] - Max_Read_Request_Size
                                                                      -- cfg_dcommand[11]    - Enable No Snoop
                                                                      -- cfg_dcommand[8]     - Extended Tag Field Enable
                                                                      -- cfg_dcommand[7:5]   - Max_Payload_Size
                                                                      -- cfg_dcommand[4]     - Enable Relaxed Ordering
  );
end PCIE_TX_GENERATOR;


-- For Memory Read Requests, Length must not exceed the value specified by Max_Read_Request_Size (see Section 7.8.4)

-- Use of Max_Read_Request_Size The Max_Read_Request_Size mechanism allows improved control of bandwidth allocation in
-- 25 systems where quality of service (QoS) is important for the target applications. For example, an
-- arbitration scheme based on counting requests (and not the sizes of those requests) provides
-- imprecise bandwidth allocation when some Requesters use much larger sizes than others. The
-- Max_Read_Request_Size mechanism can be used to force more uniform allocation of bandwidth,
-- by restricting the upper size of read requests.

-- Max_Read_Request_Size – This field sets the maximum Read
-- Request size for the Device as a Requester. The Device must
-- not generate read requests with size exceeding the set value.
-- Defined encodings for this field are:
-- 000b 128 bytes max read request size
-- 001b 256 bytes max read request size
-- 010b 512 bytes max read request size
-- 011b 1024 bytes max read request size
-- 100b 2048 bytes max read request size
-- 101b 4096 bytes max read request size

-- Max_Payload_Size field of the Transmitter’s Device Control register taken as an integral number
-- of DW (see Section 7.8.4).

-- Max_Payload_Size Supported – This field indicates the
-- maximum payload size that the device/function can support for
-- TLPs.
-- Defined encodings are:
-- 000b 128 bytes max payload size
-- 001b 256 bytes max payload size
-- 010b 512 bytes max payload size
-- 011b 1024 bytes max payload size
-- 100b 2048 bytes max payload size
-- 101b 4096 bytes max payload size


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of PCIE_TX_GENERATOR is

   -- Empty signal
   signal empty : std_logic;

   -- Toplevel registers
   signal type_reg                 : std_logic_vector(1 downto 0);
   signal tag_reg                  : std_logic_vector(4 downto 0);
   signal tag_reg_we               : std_logic;
   signal first_be_src_addr_reg    : std_logic_vector(2 downto 0);
   signal first_be_src_addr_reg_we : std_logic;
   signal addr_reg                 : std_logic_vector(63 downto 0);
   signal addr_reg_we              : std_logic;
   signal requester_id_reg         : std_logic_vector(15 downto 0);
   signal requester_id_reg_we      : std_logic;
   signal cpl_tag_reg              : std_logic_vector(7 downto 0);
   signal lower_addr_reg           : std_logic_vector(6 downto 0);
   signal lower_addr_reg_we        : std_logic;
   signal length_reg               : std_logic_vector(11 downto 0);
   signal length_reg_we            : std_logic;
   signal dw4_reg                  : std_logic;

   -- Output pipeline
   signal trn_reset                 : std_logic;
   signal data_pipe                 : std_logic_vector(63 downto 0);
   signal rem_pipe                  : std_logic_vector(7 downto 0);
   signal sof_n_pipe                : std_logic;
   signal eof_n_pipe                : std_logic;
   signal src_rdy_n_pipe            : std_logic;
   signal dst_rdy_n_pipe            : std_logic;
   signal data_output_pipe_in       : std_logic_vector(71 downto 0);
   signal data_output_pipe_out      : std_logic_vector(71 downto 0);

   -- Output FSM signals
   signal out_fsm_hdr0_rdy          : std_logic;
   signal out_fsm_hdr1_rdy          : std_logic;
   signal out_fsm_hdr0_ack          : std_logic;
   signal out_fsm_hdr1_ack          : std_logic;
   signal out_fsm_next_part         : std_logic;
   signal out_fsm_split_trans       : std_logic;
   signal out_fsm_sel               : std_logic_vector(1 downto 0);


   -- Realign circuit signals
   signal realign_sop_n             : std_logic;
   signal realign_eop_n             : std_logic;
   signal realign_src_rdy_n         : std_logic;
   signal realign_dst_rdy_n         : std_logic;
   signal realign_rdy               : std_logic;
   signal realign_init              : std_logic;

   signal out_fsm_realign_data      : std_logic_vector(63 downto 0);
   signal out_fsm_realign_sop_n     : std_logic;
   signal out_fsm_realign_eop_n     : std_logic;
   signal out_fsm_realign_src_rdy_n : std_logic;
   signal out_fsm_realign_dst_rdy_n : std_logic;
   signal out_fsm_realign_rem_n     : std_logic;


   -- DW Length
   signal dw_len                    : std_logic_vector(9 downto 0);
   signal addr_dec_out              : std_logic_vector(11 downto 0);

   signal cfg_max_read_req_size     : std_logic_vector(2 downto 0);
   signal cfg_max_payload_size      : std_logic_vector(2 downto 0);
   signal max_read_size             : std_logic_vector(9 downto 0);
   signal max_payload_size          : std_logic_vector(9 downto 0);
   signal cfg_requester_id          : std_logic_vector(15 downto 0);
   
   signal first_be                  : std_logic_vector(3 downto 0);
   signal last_be                   : std_logic_vector(3 downto 0);

   signal byte_count                : std_logic_vector(11 downto 0);
   signal low_addr                  : std_logic_vector(31 downto 0);
   signal high_addr                 : std_logic_vector(31 downto 0);

   signal hdr0_0                    : std_logic_vector(31 downto 0);
   signal hdr0_1_rd_wr              : std_logic_vector(31 downto 0); 
   signal hdr0_1_cpl                : std_logic_vector(31 downto 0);
   signal hdr1_0_rd_wr_3dw          : std_logic_vector(31 downto 0);
   signal hdr1_0_rd_wr_4dw          : std_logic_vector(31 downto 0);
   signal hdr1_1_rd_wr_4dw          : std_logic_vector(31 downto 0);
   signal hdr1_0_rd_cpl             : std_logic_vector(31 downto 0);

   signal low_trn_data_out_mux      : std_logic_vector(31 downto 0);
   signal low_trn_data_out_mux_sel  : std_logic_vector(2 downto 0);
   signal high_trn_data_out_mux     : std_logic_vector(31 downto 0);
   signal high_trn_data_out_mux_sel : std_logic_vector(1 downto 0);

   signal low_mux_dec_in            : std_logic_vector(4 downto 0);
   signal high_mux_dec_in           : std_logic_vector(4 downto 0);
   signal second_hdr                : std_logic;
   signal out_fsm_type              : std_logic_vector(1 downto 0);
   signal out_fsm_dw4               : std_logic;
   signal type_reg_we               : std_logic;
   signal tag_4_bit                 : std_logic;

begin


trn_reset      <= not TRN_RESET_N;


-- Input FSM --------------------------------------------------------------------
PCIE_TX_IN_FSM_U : entity work.PCIE_TX_IN_FSM
   port map (
     -- PCI Express Common signals -------------------------------------------
       TRN_RESET_N          => TRN_RESET_N,
       TRN_CLK              => TRN_CLK,
     -- Data Input Interface -------------------------------------------------
       IN_SOP_N             => GEN_SOP_N,    
       IN_EOP_N             => GEN_EOP_N,
       IN_SRC_RDY_N         => GEN_SRC_RDY_N,
       IN_DST_RDY_N         => GEN_DST_RDY_N,
       IN_DW4_VLD           => GEN_DW4_VLD,
     -- Realign Input Interface ----------------------------------------------
       REALIGN_SOP_N        => realign_sop_n,
       REALIGN_EOP_N        => realign_eop_n,
       REALIGN_SRC_RDY_N    => realign_src_rdy_n,
       REALIGN_DST_RDY_N    => realign_dst_rdy_n,
       REALIGN_RDY          => realign_rdy,
       REALIGN_INIT         => realign_init,
     -- Output FSM Interface -------------------------------------------------
       HDR0_RDY             => out_fsm_hdr0_rdy,
       HDR1_RDY             => out_fsm_hdr1_rdy,
       HDR0_ACK             => out_fsm_hdr0_ack,
       HDR1_ACK             => out_fsm_hdr1_ack,
     -- Control Interface ----------------------------------------------------
       TYPE_WE              => type_reg_we,
       LEN_WE               => length_reg_we,
       TAG_WE               => tag_reg_we,
       FIRST_BE_SRC_ADDR_WE => first_be_src_addr_reg_we,
       ADDR_WE              => addr_reg_we,
       LOWER_ADDR_WE        => lower_addr_reg_we,
       REQUESTER_ID_WE      => requester_id_reg_we,
       SECOND_HDR           => second_hdr
    );

-- ----------------------------------------------------------------------------
--   TX_REGISTERS
-- ----------------------------------------------------------------------------

-- register type_reg ----------------------------------------------------------
type_regp: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
         -- type_reg <= (others => '0');
      elsif (type_reg_we = '1') then
         type_reg <= GEN_DATA(1 downto 0);
      end if;
   end if;
end process;

-- register tag_reg ------------------------------------------------------
tag_regp: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
         -- tag_reg <= (others => '0');
      elsif (tag_reg_we = '1') then
         tag_reg <= GEN_DATA(18 downto 14);
      end if;
   end if;
end process;

-- register first_be_src_addr_reg ------------------------------------------------------
first_be_src_addr_regp: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      -- Set reset after NEXT_PART
      if (TRN_RESET_N = '0') then
         first_be_src_addr_reg <= (others => '0');  
      elsif (out_fsm_next_part='1') then
         first_be_src_addr_reg <= (others => '0');  
      elsif (first_be_src_addr_reg_we = '1') then
         first_be_src_addr_reg <= GEN_DATA(24 downto 22);
      end if;
   end if;
end process;


-- register length_reg ------------------------------------------------------
length_regp: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
         -- length_reg <= (others => '0');
      elsif (length_reg_we = '1') then
         length_reg <= GEN_DATA(13 downto 2);
      end if;
   end if;
end process;

-- register addr_reg ------------------------------------------------------
addr_regp: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
         -- addr_reg <= (others => '0');
      elsif (addr_reg_we = '1') then
         addr_reg <= GEN_DATA;
      end if;
   end if;
end process;


-- register requester_id_reg ------------------------------------------------------
requester_id_regp: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
         -- requester_id_reg <= (others => '0');
      elsif (requester_id_reg_we = '1') then
         requester_id_reg <= GEN_DATA(23 downto 8);
      end if;
   end if;
end process;

-- register cpl_tag ---------------------------------------------------------------
cpl_tag_regp: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
         -- cpl_tag_reg <= (others => '0');
      elsif (requester_id_reg_we = '1') then
         cpl_tag_reg <= GEN_DATA(7 downto 0);
      end if;
   end if;
end process;

-- register lower_addr_reg ------------------------------------------------------
lower_addr_regp: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0' or out_fsm_next_part='1') then
         lower_addr_reg <= (others => '0');
      elsif (lower_addr_reg_we = '1') then
         lower_addr_reg <= GEN_DATA(30 downto 24);
      end if;
   end if;
end process;

-- register dw4_reg ------------------------------------------------------
dw4_regp: process(TRN_RESET_N, TRN_CLK)
begin
   if (TRN_CLK'event AND TRN_CLK = '1') then
      if (TRN_RESET_N = '0') then
         dw4_reg <= '0';
      elsif (type_reg_we = '1') then
         dw4_reg <= GEN_DW4;
      end if;
   end if;
end process;


-- ----------------------------------------------------------------------------
--   MAX READ AND WRITE DECODERS
-- ----------------------------------------------------------------------------

-- -- Max Read Request Size Decoder-------------------------------------------
max_read_size_decp: process(cfg_max_read_req_size)
begin
   case cfg_max_read_req_size is
      when "000"  => max_read_size <= "0000100000"; -- transaction(128 b)
      when "001"  => max_read_size <= "0001000000"; -- transaction(256 b)
      when "010"  => max_read_size <= "0010000000"; -- transaction(512 b)
      when "011"  => max_read_size <= "0100000000"; -- transaction(1024 b)
      when "100"  => max_read_size <= "1000000000"; -- transaction(2048 b)
      when "101"  => max_read_size <= "0000000000"; -- transaction(4096 b)
      when others => max_read_size <= "0000000000"; -- transaction(4096 b)
   end case;
end process;

-- -- Max Paylod Size Decoder ------------------------------------------------
max_payload_size_decp: process(cfg_max_payload_size)
begin
   case cfg_max_payload_size is
      when "000"  => max_payload_size <= "0000100000"; -- transaction(128 b)
      when "001"  => max_payload_size <= "0001000000"; -- transaction(256 b)
      when "010"  => max_payload_size <= "0010000000"; -- transaction(512 b)
      when "011"  => max_payload_size <= "0100000000"; -- transaction(1024 b)
      when "100"  => max_payload_size <= "1000000000"; -- transaction(2048 b)
      when "101"  => max_payload_size <= "0000000000"; -- transaction(4096 b)
      when others => max_payload_size <= "0000000000"; -- transaction(4096 b)
   end case;
end process;

-- -- Tag 7 bit decoder ------------------------------------------------------
-- Set 7 bit to 1 for last part of Read request
tag_4_bit_decoderp: process(type_reg, out_fsm_split_trans, tag_reg)
begin
   case type_reg(1) is
      when '1'    => tag_4_bit <= tag_reg(4);              -- WR/CPL
      when '0'    => tag_4_bit <= not out_fsm_split_trans; -- Read
      when others => tag_4_bit <= 'X';
   end case;
end process;

-- ----------------------------------------------------------------------------
--   LENGTH DECODER
-- ----------------------------------------------------------------------------

-- -- Length decoder ---------------------------------------------------------
PCIE_TX_LEN_DECODER_U : entity work.PCIE_TX_LEN_DECODER
  port map (
     -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N           => TRN_RESET_N,
      TRN_CLK               => TRN_CLK,
     -- Data Input Interface -------------------------------------------------
      TYPE_REG               => type_reg,
      MAX_READ_SIZE          => max_read_size,
      MAX_PAYLOAD_SIZE       => max_payload_size,
      FIRST_BE_SRC_ADDR_REG  => first_be_src_addr_reg,
      LEN_IN                 => GEN_DATA(13 downto 2),
      LEN_IN_WE              => length_reg_we,
    -- Output FSM Interface -------------------------------------------------
      SPLIT_TRANS            => out_fsm_split_trans,
      NEXT_PART              => out_fsm_next_part,
    -- Output Interface -----------------------------------------------------
      DW_LEN_OUT             => dw_len,
      FIRST_BE_OUT           => first_be,
      LAST_BE_OUT            => last_be,
      BYTE_COUNT             => byte_count
   );

-- ----------------------------------------------------------------------------
--   ADDRESS DECODER
-- ----------------------------------------------------------------------------

-- -- Address Decoder --------------------------------------------------------
PCIE_TX_ADDR_DECODER_U : entity work.PCIE_TX_ADDR_DECODER
  port map (
     -- PCI Express Common signals -------------------------------------------
       TRN_RESET_N            => TRN_RESET_N,
       TRN_CLK                => TRN_CLK,
     -- Data Input Interface -------------------------------------------------
       ADDR_IN                => GEN_DATA(11 downto 0),
       ADDR_IN_WE             => addr_reg_we,
       TYPE_REG               => type_reg,
       MAX_READ_SIZE          => max_read_size,
       MAX_PAYLOAD_SIZE       => max_payload_size,
     -- Output FSM Interface -------------------------------------------------
       NEXT_PART              => out_fsm_next_part,
     -- Output Interface -----------------------------------------------------
       ADDR_OUT               => addr_dec_out 
   );


-- ----------------------------------------------------------------------------
--   REALIGN CIRCUIT
-- ----------------------------------------------------------------------------

-- -- Realign circuit --------------------------------------------------------
PCIE_TX_DATA_REALIGN_U : entity work.PCIE_TX_DATA_REALIGN
  port map (
     -- PCI Express Common signals -------------------------------------------
       TRN_RESET_N          => TRN_RESET_N,
       TRN_CLK              => TRN_CLK,

    -- Data Input Interface -------------------------------------------------
      IN_DATA               => GEN_DATA,                  -- Data or Header
      IN_SOP_N              => realign_sop_n,             -- Start of Packet
      IN_EOP_N              => realign_eop_n,             -- End of Packet
      IN_SRC_RDY_N          => realign_src_rdy_n,         -- Source Ready
      IN_DST_RDY_N          => realign_dst_rdy_n,         -- Destination Ready
    -- Data Output Interface ------------------------------------------------
      OUT_DATA              => out_fsm_realign_data,      -- Data or Header
      OUT_SOP_N             => out_fsm_realign_sop_n,     -- Data or Header
      OUT_EOP_N             => out_fsm_realign_eop_n,     -- Data or Header
      OUT_SRC_RDY_N         => out_fsm_realign_src_rdy_n, -- Data or Header
      OUT_DST_RDY_N         => out_fsm_realign_dst_rdy_n, -- Data or Header
      OUT_REM_N             => out_fsm_realign_rem_n,     -- Output REM
    -- Control Interface ----------------------------------------------------
      LEN_IN                => length_reg(2 downto 0),    -- Low bits from length
      FIRST_BE              => first_be_src_addr_reg,     -- First BE
      DW4                   => dw4_reg,                   -- DW4
      INIT                  => realign_init,              -- Init   
      INIT_RDY              => realign_rdy,               -- Data realign unit ready
      MAX_PAYLOAD_SIZE      => max_payload_size
   );



-- ----------------------------------------------------------------------------
--   PCIe OUTPUT LOGIC     PCIe OUTPUT LOGIC    PCIe OUTPUT LOGIC
--           PCIe OUTPUT LOGIC       PCIe OUTPUT LOGIC    PCIe OUTPUT LOGIC
-- ----------------------------------------------------------------------------



-- ----------------------------------------------------------------------------
--   OUTPUT FSM
-- ----------------------------------------------------------------------------
PCIE_TX_OUT_FSM_U : entity work.PCIE_TX_OUT_FSM
  port map (
     -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N          => TRN_RESET_N,
      TRN_CLK              => TRN_CLK,
    -- Data Input Interface -------------------------------------------------
      TRN_LNK_UP_N         => TRN_LNK_UP_N, -- trn_lnk_up_n_pipe,     -- Transaction Link Up
      TRN_TREM_N           => rem_pipe,                               -- Transmit Data Reminder
      TRN_TSOF_N           => sof_n_pipe,                             -- Transmit SOF
      TRN_TEOF_N           => eof_n_pipe,                             -- Transmit EOF
      TRN_TSRC_RDY_N       => src_rdy_n_pipe,                         -- Trnasmit Source Ready
      TRN_TDST_RDY_N       => dst_rdy_n_pipe,                         -- Transmit Destination Ready
      TRN_TBUF_AV          => TRN_TBUF_AV, -- trn_tbuf_av_pipe,       -- Transmit Buffers Available
                                                                      -- trn_tbuf_av[0] => Non Posted Queue
                                                                      -- trn_tbuf_av[1] => Posted Queue
                                                                      -- trn_tbuf_av[2] => Completion Queue
    -- Type Control Interface -----------------------------------------------
      SPLIT_TRANS          => out_fsm_split_trans,
      WITH_DATA            => type_reg(1),                            -- Type
      DW4_REG              => dw4_reg,                                -- Type                
      TR_TYPE              => type_reg,                               -- Type

    -- Realign circuit ------------------------------------------------------
      REALIGN_SOP_N        => out_fsm_realign_sop_n,                  -- Start of Packet
      REALIGN_EOP_N        => out_fsm_realign_eop_n,                  -- End of Packet
      REALIGN_SRC_RDY_N    => out_fsm_realign_src_rdy_n,              -- Source Ready
      REALIGN_DST_RDY_N    => out_fsm_realign_dst_rdy_n,              -- Destination Ready
      REALIGN_REM_N        => out_fsm_realign_rem_n,                  -- Realign circuit ready

    -- Input FSM Interface --------------------------------------------------
      HDR0_RDY             => out_fsm_hdr0_rdy,
      HDR1_RDY             => out_fsm_hdr1_rdy,
      HDR0_ACK             => out_fsm_hdr0_ack,
      HDR1_ACK             => out_fsm_hdr1_ack,

    -- Control Interface ----------------------------------------------------
      DATA_SEL             => out_fsm_sel,                            -- Data select
      TYPE_OUT             => out_fsm_type,                           -- Out FSM Type
      DW4_OUT              => out_fsm_dw4,
      NEXT_PART            => out_fsm_next_part                       -- Next part
   );


-- ----------------------------------------------------------------------------
-- HEADERS GENERATION
-- ----------------------------------------------------------------------------
low_addr  <= addr_reg(31 downto 12) & addr_dec_out;
high_addr <= addr_reg(63 downto 32);


-- HDR 0_0 (Common for all transactions)
hdr0_0 <= '0' & out_fsm_type(1) & out_fsm_dw4 & '0' & out_fsm_type(0) & '0' & out_fsm_type(0) & '0' & -- +0
          '0' & "000" & "0000" &                                                                      -- +1
          '0' & '0' & "00" & "00" & dw_len(9 downto 8) &                                              -- +2
          dw_len(7 downto 0);                                                                         -- +3

-- HDR 0_1_RD_WR (Common for Read and write transactions)
hdr0_1_rd_wr <= cfg_requester_id(15 downto 8) &           -- +0
                cfg_requester_id(7 downto 0) &            -- +1
                "000" & tag_4_bit & tag_reg(3 downto 0) & -- +2
                last_be & first_be;                       -- +3

-- HDR 0_1_CPL (Common for Completitions)
hdr0_1_cpl   <= cfg_requester_id(15 downto 8) &           -- +0
                cfg_requester_id(7 downto 0) &            -- +1
                "000" & '0' & byte_count(11 downto 8) &   -- +2
                byte_count(7 downto 0);                   -- +3

hdr1_0_rd_wr_3dw <= low_addr(31 downto 0);
hdr1_0_rd_wr_4dw <= high_addr(31 downto 0);
hdr1_1_rd_wr_4dw <= low_addr( 31 downto 0);

hdr1_0_rd_cpl    <=  requester_id_reg(15 downto 8)  &    -- +0
                     requester_id_reg( 7 downto 0)  &    -- +1
                     cpl_tag_reg                    &    -- +2
                     '0' & lower_addr_reg;               -- +4 

-- ----------------------------------------------------------------------------
-- DATA OUT MULTIPLEXORS AND DECODERS
-- ----------------------------------------------------------------------------

low_mux_dec_in  <= out_fsm_type & out_fsm_dw4 & out_fsm_sel;
high_mux_dec_in <= out_fsm_type & out_fsm_dw4 & out_fsm_sel;

-- -- Max Read Request Size Decoder-------------------------------------------
low_mux_decp: process(low_mux_dec_in)
begin
   case low_mux_dec_in is
      when "00000"  => low_trn_data_out_mux_sel <= "000"; -- Read(32) HDR0
      when "00001"  => low_trn_data_out_mux_sel <= "001"; -- Read(32) HDR1
      when "00010"  => low_trn_data_out_mux_sel <= "100"; -- Read(32) DATA
      when "00100"  => low_trn_data_out_mux_sel <= "000"; -- Read(64) HDR0
      when "00101"  => low_trn_data_out_mux_sel <= "010"; -- Read(64) HDR1
      when "00110"  => low_trn_data_out_mux_sel <= "100"; -- Read(64) DATA
      when "10000"  => low_trn_data_out_mux_sel <= "000"; -- Write(32) HDR0
      when "10001"  => low_trn_data_out_mux_sel <= "001"; -- Write(32) HDR1
      when "10010"  => low_trn_data_out_mux_sel <= "100"; -- Write(32) DATA
      when "10100"  => low_trn_data_out_mux_sel <= "000"; -- Write(64) HDR0
      when "10101"  => low_trn_data_out_mux_sel <= "010"; -- Write(64) HDR1
      when "10110"  => low_trn_data_out_mux_sel <= "100"; -- Write(64) DATA
      when "11000"  => low_trn_data_out_mux_sel <= "000"; -- CPL(32) HDR0
      when "11001"  => low_trn_data_out_mux_sel <= "011"; -- CPL(32) HDR1
      when "11010"  => low_trn_data_out_mux_sel <= "100"; -- CPL(32) DATA
      when others   => low_trn_data_out_mux_sel <= "XXX"; -- transaction(4096 b)
   end case;
end process;

--multiplexor low_trn_data_out_mux---------------------------------------------
low_trn_data_out_muxp: process(low_trn_data_out_mux_sel, hdr0_0, hdr1_0_rd_wr_3dw,
                               hdr1_0_rd_wr_4dw, hdr1_0_rd_cpl, out_fsm_realign_data)
begin
   case low_trn_data_out_mux_sel is
      when "000"  => low_trn_data_out_mux <= hdr0_0;
      when "001"  => low_trn_data_out_mux <= hdr1_0_rd_wr_3dw;
      when "010"  => low_trn_data_out_mux <= hdr1_0_rd_wr_4dw;
      when "011"  => low_trn_data_out_mux <= hdr1_0_rd_cpl;
      when "100"  => low_trn_data_out_mux <= out_fsm_realign_data(7 downto 0) & out_fsm_realign_data(15 downto 8) & out_fsm_realign_data(23 downto 16) & out_fsm_realign_data(31 downto 24);
      when others => low_trn_data_out_mux <= (others => 'X');
   end case;
end process;

-- -- Max Read Request Size Decoder-------------------------------------------
high_mux_decp: process(high_mux_dec_in)
begin
   case high_mux_dec_in is
      when "00000"  => high_trn_data_out_mux_sel <= "00";  -- Read(32) HDR0
      when "00001"  => high_trn_data_out_mux_sel <= "11";  -- Read(32) HDR1
      when "00010"  => high_trn_data_out_mux_sel <= "11";  -- Read(32) DATA
      when "00100"  => high_trn_data_out_mux_sel <= "00";  -- Read(64) HDR0
      when "00101"  => high_trn_data_out_mux_sel <= "10";  -- Read(64) HDR1
      when "00110"  => high_trn_data_out_mux_sel <= "11";  -- Read(64) DATA
      when "10000"  => high_trn_data_out_mux_sel <= "00";  -- Write(32) HDR0
      when "10001"  => high_trn_data_out_mux_sel <= "11";  -- Write(32) HDR1
      when "10010"  => high_trn_data_out_mux_sel <= "11";  -- Write(32) DATA
      when "10100"  => high_trn_data_out_mux_sel <= "00";  -- Write(64) HDR0
      when "10101"  => high_trn_data_out_mux_sel <= "10";  -- Write(64) HDR1
      when "10110"  => high_trn_data_out_mux_sel <= "11";  -- Write(64) DATA
      when "11000"  => high_trn_data_out_mux_sel <= "01";  -- CPL(32) HDR0
      when "11001"  => high_trn_data_out_mux_sel <= "11";  -- CPL(32) HDR1
      when "11010"  => high_trn_data_out_mux_sel <= "11";  -- CPL(32) DATA
      when others   => high_trn_data_out_mux_sel <= "XX";  -- transaction(4096 b)
   end case;
end process;

--multiplexor high_trn_data_out------------------------------------------------------
high_trn_data_outp: process(high_trn_data_out_mux_sel, hdr0_1_rd_wr, hdr0_1_cpl, hdr1_1_rd_wr_4dw, out_fsm_realign_data)
begin
   case high_trn_data_out_mux_sel is
      when "00"   => high_trn_data_out_mux <= hdr0_1_rd_wr;
      when "01"   => high_trn_data_out_mux <= hdr0_1_cpl;
      when "10"   => high_trn_data_out_mux <= hdr1_1_rd_wr_4dw;
      when "11"   => high_trn_data_out_mux <= out_fsm_realign_data(39 downto 32) & out_fsm_realign_data(47 downto 40) & out_fsm_realign_data(55 downto 48) & out_fsm_realign_data(63 downto 56);
      when others => high_trn_data_out_mux <= (others => 'X');
   end case;
end process;


-------------------------------------------------------------------------------
-- Output pipeline (START)                                                               
-------------------------------------------------------------------------------
  data_pipe           <= low_trn_data_out_mux & high_trn_data_out_mux;

  GEN_OUTPUT_REG : if (OUTPUT_REG_EN) generate

   data_output_pipe_in <= data_pipe & rem_pipe;

   OUT_IB_PIPE_U : entity work.IB_PIPE
   generic map (
      DATA_WIDTH     => 72
      )   
   port map (
      -- Common interface --------------------------------------------------
      CLK            => TRN_CLK,
      RESET          => trn_reset,
      -- Input interface ---------------------------------------------------
      IN_DATA        => data_output_pipe_in,
      IN_SOF_N       => sof_n_pipe,
      IN_EOF_N       => eof_n_pipe,
      IN_SRC_RDY_N   => src_rdy_n_pipe,
      IN_DST_RDY_N   => dst_rdy_n_pipe,
      -- Output interface --------------------------------------------------
      OUT_DATA       => data_output_pipe_out,
      OUT_SOF_N      => TRN_TSOF_N,
      OUT_EOF_N      => TRN_TEOF_N,
      OUT_SRC_RDY_N  => TRN_TSRC_RDY_N,
      OUT_DST_RDY_N  => TRN_TDST_RDY_N
   );

    TRN_TREM_N <= data_output_pipe_out(7 downto 0);
    TRN_TD     <= data_output_pipe_out(71 downto 8);

    -- register output_pipe_reg ------------------------------------------------------
    output_pipe_regp: process(TRN_RESET_N, TRN_CLK)
    begin
      if (TRN_CLK'event AND TRN_CLK = '1') then
         if (TRN_RESET_N = '0') then
            cfg_max_read_req_size <= "000";
            cfg_max_payload_size  <= "000";
            cfg_requester_id          <= (others => '0');
         else
            cfg_max_read_req_size <= CFG_DCOMMAND(14 downto 12);
            cfg_max_payload_size  <= CFG_DCOMMAND(7 downto 5);
            cfg_requester_id      <= CFG_BUS_NUMBER & CFG_DEVICE_NUMBER & CFG_FUNCTION_NUMBER;
         end if;
       end if;
    end process;
  end generate;

  GEN_NOT_OUTPUT_REG : if (not OUTPUT_REG_EN) generate
    TRN_TSOF_N            <= sof_n_pipe;
    TRN_TEOF_N            <= eof_n_pipe;
    TRN_TSRC_RDY_N        <= src_rdy_n_pipe;
    dst_rdy_n_pipe        <= TRN_TDST_RDY_N;
    TRN_TREM_N            <= rem_pipe;
    TRN_TD                <= data_pipe;
    cfg_max_read_req_size <= CFG_DCOMMAND(14 downto 12);
    cfg_max_payload_size  <= CFG_DCOMMAND(7 downto 5);
    cfg_requester_id      <= CFG_BUS_NUMBER & CFG_DEVICE_NUMBER & CFG_FUNCTION_NUMBER;
  end generate;

-------------------------------------------------------------------------------
-- Output pipeline (END)                                                               
-------------------------------------------------------------------------------

end architecture FULL;

