 --
-- data_realign.vhd : PCI-e Data realign unit
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kobierský <kobiersky@liberouter.org>
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
entity PCIE_TX_DATA_REALIGN is
  port (
    -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N           : in  std_logic; 
      TRN_CLK               : in  std_logic; 

    -- Data Input Interface -------------------------------------------------
      IN_DATA               : in  std_logic_vector( 63 downto 0 ); -- Data or Header
      IN_SOP_N              : in  std_logic;                       -- Start of Packet
      IN_EOP_N              : in  std_logic;                       -- End of Packet
      IN_SRC_RDY_N          : in  std_logic;                       -- Source Ready
      IN_DST_RDY_N          : out std_logic;                       -- Destination Ready
    -- Data Output Interface ------------------------------------------------
      OUT_DATA              : out std_logic_vector( 63 downto 0 ); -- Data or Header
      OUT_SOP_N             : out std_logic;                       -- Start of Packet
      OUT_EOP_N             : out std_logic;                       -- End of Packet
      OUT_SRC_RDY_N         : out std_logic;                       -- Source Ready
      OUT_DST_RDY_N         : in  std_logic;                       -- Destination Ready
      OUT_REM_N             : out std_logic;                       -- Output REM

    -- Control Interface ----------------------------------------------------
      LEN_IN                : in  std_logic_vector(2 downto 0);    -- Low bits from length
      FIRST_BE              : in  std_logic_vector(2 downto 0);    -- First BE
      DW4                   : in  std_logic;                       -- 4 DW 
      INIT                  : in  std_logic;                       -- Init   
      INIT_RDY              : out std_logic;                       -- Data realign unit ready
    -- Spliting interface ---------------------------------------------------
      MAX_PAYLOAD_SIZE      : in  std_logic_vector(9 downto 0)
   );
end PCIE_TX_DATA_REALIGN;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of PCIE_TX_DATA_REALIGN  is
-- TODO: Addr assertion to toplevel (check for out of 4kb aligment)

   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   -- registred variables --
   signal len_in_reg                : std_logic_vector(2 downto 0);
   signal first_be_reg              : std_logic_vector(2 downto 0);
   signal dw4_reg                   : std_logic;
   signal in_data_reg               : std_logic_vector(31 downto 0);
   signal init_rdy_reg              : std_logic;

   -- registred controls -- 
   signal in_sop_reg_n              : std_logic;
   signal out_sop_sig_n             : std_logic;
   signal in_eop_reg_n              : std_logic;
   signal out_eop_sig_n             : std_logic;

      -- control signals allowance --
   signal init_load                 : std_logic;
   signal eop_load                  : std_logic;
   signal en_init_load              : std_logic;

   -- align detector --
   signal go_align                  : std_logic;

   -- output rem decoder signals --
   signal last_rem_n                : std_logic;
   signal in_rem_n                  : std_logic;

   -- pipe signals --
   signal trn_reset                 : std_logic;
   signal data_output_pipe_in       : std_logic_vector(64 downto 0);
   signal data_pipe                 : std_logic_vector(63 downto 0);
   signal rem_n_pipe                : std_logic;
   signal src_rdy_n_pipe            : std_logic;
   signal dst_rdy_n_pipe            : std_logic;
   signal data_output_pipe_out      : std_logic_vector(64 downto 0);
   signal in_rem_dec_in             : std_logic_vector(5 downto 0);

   -- spliter out --
   signal splitter_data             : std_logic_vector(63 downto 0);
   signal splitter_rem_n            : std_logic;
   signal splitter_src_rdy_n        : std_logic;
   signal splitter_dst_rdy_n        : std_logic;
   signal splitter_sop_n            : std_logic;
   signal splitter_eop_n            : std_logic;


begin

-------------------------------------------------------------------------------
-- Output pipeline (START)                                                               
-------------------------------------------------------------------------------
   trn_reset <= not TRN_RESET_N;

   data_output_pipe_in <= splitter_rem_n & splitter_data;

      OUT_IB_PIPE_U : entity work.IB_PIPE
      generic map (
         DATA_WIDTH  => 65  -- data + rem
      )
      port map (
         -- Common interface --------------------------------------------------
         CLK            => TRN_CLK,
         RESET          => trn_reset,
         -- Input interface ---------------------------------------------------
         IN_DATA        => data_output_pipe_in,
         IN_SOF_N       => splitter_sop_n,
         IN_EOF_N       => splitter_eop_n,
         IN_SRC_RDY_N   => splitter_src_rdy_n,
         IN_DST_RDY_N   => splitter_dst_rdy_n,
         -- Output interface --------------------------------------------------
         OUT_DATA       => data_output_pipe_out,
         OUT_SOF_N      => OUT_SOP_N,
         OUT_EOF_N      => OUT_EOP_N,
         OUT_SRC_RDY_N  => OUT_SRC_RDY_N,
         OUT_DST_RDY_N  => OUT_DST_RDY_N
      );

   OUT_DATA    <= data_output_pipe_out(63 downto 0);
   OUT_REM_N   <= data_output_pipe_out(64); 

-------------------------------------------------------------------------------
-- Output pipeline (END)                                                               
-------------------------------------------------------------------------------


-------------------------------------------------------------------------------
-- Spliter (START)                                                               
-------------------------------------------------------------------------------
PCIE_SPLITER_U : entity work.PCIE_SPLITER
  port map (
    -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N           => TRN_RESET_N,
      TRN_CLK               => TRN_CLK,

    -- Data Input Interface -------------------------------------------------
      IN_DATA               => data_pipe,                 -- Data or Header
      IN_SOP_N              => out_sop_sig_n,             -- Start of Packet
      IN_EOP_N              => out_eop_sig_n,             -- End of Packet
      IN_SRC_RDY_N          => src_rdy_n_pipe,            -- Source Ready
      IN_DST_RDY_N          => dst_rdy_n_pipe,            -- Destination Ready
      IN_REM_N              => rem_n_pipe,                -- Output REM
    -- Data Output Interface ------------------------------------------------
      OUT_DATA              => splitter_data,             -- Data or Header
      OUT_SOP_N             => splitter_sop_n,            -- Start of Packet
      OUT_EOP_N             => splitter_eop_n,            -- End of Packet
      OUT_SRC_RDY_N         => splitter_src_rdy_n,        -- Source Ready
      OUT_DST_RDY_N         => splitter_dst_rdy_n,        -- Destination Ready
      OUT_REM_N             => splitter_rem_n,            -- Output REM

    -- Control Interface ----------------------------------------------------
      MAX_PAYLOAD_SIZE      => MAX_PAYLOAD_SIZE,
      DW4                   => DW4,
      DW4_REG               => dw4_reg,
      INIT                  => INIT
   );
-------------------------------------------------------------------------------
-- Spliter (END)                                                               
-------------------------------------------------------------------------------

   -- length register ---------------------------------------------------------
   LEN_IN_REG_P : process (TRN_CLK, TRN_RESET_N, LEN_IN, INIT ) 
      begin
         if (TRN_CLK = '1' and TRN_CLK'event) then
           if (TRN_RESET_N = '0') then 
            -- len_in_reg  <= (others => '0');
           elsif (INIT = '1') then     -- INIT
             len_in_reg <=  LEN_IN;
           end if;
         end if;
      end process;

   -- first_be register -------------------------------------------------------
   FIRST_BE_REG_P : process (TRN_CLK, TRN_RESET_N, FIRST_BE, INIT ) 
      begin
        if (TRN_CLK = '1' and TRN_CLK'event) then
           if (TRN_RESET_N = '0') then 
             first_be_reg  <= (others => '0');
           elsif (INIT = '1') then   -- INIT
             first_be_reg <=  FIRST_BE;
           end if;
         end if;
      end process;

   -- dw4 register ------------------------------------------------------------
   DW4_REG_P : process (TRN_CLK, TRN_RESET_N, DW4, INIT ) 
      begin
         if (TRN_CLK = '1' and TRN_CLK'event) then
            if (TRN_RESET_N = '0') then 
               dw4_reg  <= '0';
            elsif (INIT = '1') then        -- INIT
               dw4_reg <=  DW4;
            end if;
         end if;
      end process;
   
   in_rem_dec_in <= len_in_reg & first_be_reg;
   -- ---------------------------------------------------------------------------
   in_rem_decp: process(in_rem_dec_in)
   begin
      case in_rem_dec_in is
         when "000000"  => in_rem_n <= '0';
         when "000001"  => in_rem_n <= '1';
         when "000010"  => in_rem_n <= '1';
         when "000011"  => in_rem_n <= '1';
         when "000100"  => in_rem_n <= '1';
         when "000101"  => in_rem_n <= '0';
         when "000110"  => in_rem_n <= '0';
         when "000111"  => in_rem_n <= '0';

         when "001000"  => in_rem_n <= '1';
         when "001001"  => in_rem_n <= '1';
         when "001010"  => in_rem_n <= '1';
         when "001011"  => in_rem_n <= '1';
         when "001100"  => in_rem_n <= '0';
         when "001101"  => in_rem_n <= '0';
         when "001110"  => in_rem_n <= '0';
         when "001111"  => in_rem_n <= '0';
  
         when "010000"  => in_rem_n <= '1';
         when "010001"  => in_rem_n <= '1';
         when "010010"  => in_rem_n <= '1';
         when "010011"  => in_rem_n <= '0';
         when "010100"  => in_rem_n <= '0';
         when "010101"  => in_rem_n <= '0';
         when "010110"  => in_rem_n <= '0';
         when "010111"  => in_rem_n <= '1';
   
         when "011000"  => in_rem_n <= '1';
         when "011001"  => in_rem_n <= '1';
         when "011010"  => in_rem_n <= '0';
         when "011011"  => in_rem_n <= '0';
         when "011100"  => in_rem_n <= '0';
         when "011101"  => in_rem_n <= '0';
         when "011110"  => in_rem_n <= '1';
         when "011111"  => in_rem_n <= '1';
  
         when "100000"  => in_rem_n <= '1';
         when "100001"  => in_rem_n <= '0';
         when "100010"  => in_rem_n <= '0';
         when "100011"  => in_rem_n <= '0';
         when "100100"  => in_rem_n <= '0';
         when "100101"  => in_rem_n <= '1';
         when "100110"  => in_rem_n <= '1';
         when "100111"  => in_rem_n <= '1';
   
         when "101000"  => in_rem_n <= '0';
         when "101001"  => in_rem_n <= '0';
         when "101010"  => in_rem_n <= '0';
         when "101011"  => in_rem_n <= '0';
         when "101100"  => in_rem_n <= '1';
         when "101101"  => in_rem_n <= '1';
         when "101110"  => in_rem_n <= '1';
         when "101111"  => in_rem_n <= '1';
  
         when "110000"  => in_rem_n <= '0';
         when "110001"  => in_rem_n <= '0';
         when "110010"  => in_rem_n <= '0';
         when "110011"  => in_rem_n <= '1';
         when "110100"  => in_rem_n <= '1';
         when "110101"  => in_rem_n <= '1';
         when "110110"  => in_rem_n <= '1';
         when "110111"  => in_rem_n <= '0';
   
         when "111000"  => in_rem_n <= '0';
         when "111001"  => in_rem_n <= '0';
         when "111010"  => in_rem_n <= '1';
         when "111011"  => in_rem_n <= '1';
         when "111100"  => in_rem_n <= '1';
         when "111101"  => in_rem_n <= '1';
         when "111110"  => in_rem_n <= '0';
         when "111111"  => in_rem_n <= '0';
         when others    => in_rem_n <= 'X';
      end case;
  end process;


   init_load    <= '1' when (IN_SRC_RDY_N='0' and IN_SOP_N='0' and dw4_reg ='1' and first_be_reg(2)='1') else '0';

   eop_load     <= '1' when (IN_SRC_RDY_N='0' and IN_EOP_N='0' and ((dw4_reg ='1' and first_be_reg(2)='1') or (dw4_reg ='0' and first_be_reg(2)='0')) and in_rem_n='0') else '0';

   en_init_load <= '1' when (in_eop_reg_n = '1') or (in_eop_reg_n = '0' and dst_rdy_n_pipe ='0') else '0';


   --(OKI)
   -- data register -----------------------------------------------------------
   IN_DATA_REG_P : process (TRN_CLK) 
      begin
         if (TRN_CLK = '1' and TRN_CLK'event) then
           if (TRN_RESET_N = '0') then 
              -- in_data_reg  <= (others => '0');
           elsif ((IN_SRC_RDY_N='0' and dst_rdy_n_pipe='0') or (init_load='1' and en_init_load = '1')) then      
              in_data_reg <=IN_DATA(63 downto 32);
           end if;
         end if;
   end process;

   --(OKI)
   -- detect if align is need -------------------------------------------------
   go_align <= (first_be_reg(2) xor (not dw4_reg));

   --(OKI)
   -- multiplexor DATA_OUTPUT_MUX ---------------------------------------------
   OUT_DATA_MUX_P: process(go_align, IN_DATA, in_data_reg)
   begin
    case go_align is
         when '0' => data_pipe <= IN_DATA;
         when '1' => data_pipe <= IN_DATA(31 downto 0) & in_data_reg;
         when others => null;
    end case;
   end process;

   -- OUT_SOP register --------------------------------------------------------
   OUT_SOP_REG_P : process (TRN_RESET_N, TRN_CLK) 
      begin
         if (TRN_CLK = '1' and TRN_CLK'event) then
           if (TRN_RESET_N = '0') then 
              in_sop_reg_n <= '1';
           elsif (init_load = '1') then       
             in_sop_reg_n <= '0';
           elsif (dst_rdy_n_pipe='0') then
             in_sop_reg_n <= '1';
           end if;
         end if;
      end process;
  
   out_sop_sig_n <= '0' when (IN_SOP_N='0' and init_load = '0') or (in_sop_reg_n = '0') else '1';


   -- OUT_EOP register --------------------------------------------------------
   OUT_EOP_REG_P : process (TRN_RESET_N, TRN_CLK) 
      begin
         if (TRN_CLK = '1' and TRN_CLK'event) then
           if (TRN_RESET_N = '0') then 
              in_eop_reg_n <= '1';
           elsif ( (eop_load = '1' and dst_rdy_n_pipe='0') or (eop_load = '1' and init_load='1' and en_init_load = '1') ) then       
             in_eop_reg_n <= '0';
           elsif (dst_rdy_n_pipe='0') then
             in_eop_reg_n <= '1';
           end if;
         end if;
      end process;
   out_eop_sig_n <=  '0' when (IN_EOP_N='0' and eop_load = '0') or (in_eop_reg_n = '0') else '1';

   -- RDY logic ---------------------------------------------------------------   
   src_rdy_n_pipe <= not ((not IN_SRC_RDY_N and not init_load) or not in_eop_reg_n);

   IN_DST_RDY_N <= '0' when (dst_rdy_n_pipe='0' or (init_load='1' and en_init_load = '1')) else '1';

   -- INIT_RDY register ---------------------------------------------------------
   INIT_RDY_P : process (TRN_CLK, TRN_RESET_N, out_eop_sig_n, dst_rdy_n_pipe, INIT ) 
      begin
         if (TRN_CLK = '1' and TRN_CLK'event) then
            if (TRN_RESET_N = '0') then 
               init_rdy_reg  <= '1';
            elsif (INIT = '1') then                                    -- CLEAR
               init_rdy_reg <= '0';
            elsif (out_eop_sig_n='0' and dst_rdy_n_pipe='0') then    -- SET   
               init_rdy_reg <= '1';
            end if;
         end if;
      end process;

   -- init RDY logic ----------------------------------------------------------
   INIT_RDY <= init_rdy_reg or (not (out_eop_sig_n or dst_rdy_n_pipe));


   -- rem logic ---------------------------------------------------------------
   OUT_REM_N_P: process(out_sop_sig_n, out_eop_sig_n, last_rem_n)
    begin
      case out_eop_sig_n is        
         when '0' =>  rem_n_pipe <= last_rem_n;       -- EOP active
         when '1' =>  rem_n_pipe <= '0';            -- other states
         when others => null;
      end case;
   end process;

   -- last rem multiplexor ----------------------------------------------------
   LAST_REM_MUX_P: process(first_be_reg, dw4_reg, in_rem_n, in_eop_reg_n)
    begin
      case dw4_reg is
         when '1' =>
            case first_be_reg(2) is
                 when '0' => last_rem_n <= in_rem_n; 
                 when '1' => last_rem_n <= not in_rem_n;
                 when others => null;
            end case;
         when '0' =>
            case first_be_reg(2) is
                 when '0' => last_rem_n <= not in_eop_reg_n;
                 when '1' => last_rem_n <= in_rem_n;
                 when others => null;
            end case;
         when others => null;
      end case;
   end process;

end architecture FULL;


