--
-- fifo_bram_discard.vhd: Block RAM Fifo with Discard feature.
-- Copyright (C) 2006 CESNET
-- Author(s): Martinek Tomas martinek@liberouter.org
--            Pus Viktor     pus@liberouter.org
--            Kosek Martin   kosek@liberouter.org
--            Lukas Solanka  solanka@liberouter.org
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

-- library containing log2 function
use work.math_pack.all;

-- auxilarity function needed to compute address width
use WORK.bmem_func.all;

-- pragma translate_off
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
-- pragma translate_on
--
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FIFO_BRAM_DISCARD is
   generic(
      -- ITEMS = Numer of items in FIFO
      ITEMS       : integer := 512;

      -- BLOCK_SIZE = Number of items in one block
      BLOCK_SIZE  : integer := 1;

      -- Block Ram Type, only 1, 2, 4, 9, 18, 36 bits
      BRAM_TYPE   : integer := 36;

      -- Data Width, DATA_WIDTH mod BRAM_TYPE must be 0
      DATA_WIDTH  : integer := 128;
      
      -- STATUS word width. Has to be less or equal to DATA_WIDTH
      STATUS_WIDTH : integer := 4;

      -- Maximal namuber of blocks to be able to discard
      MAX_DISCARD_BLOCKS : integer := 10;

      -- Automatic transfer of valid data to the output of the FIFO
      AUTO_PIPELINE : boolean := false
   );
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;

      -- Write interface
      WR       : in  std_logic;
      EOB      : in  std_logic;
      DI       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      FULL     : out std_logic;
      LSTBLK   : out std_logic;
      STATUS   : out std_logic_vector(STATUS_WIDTH-1 downto 0);

      -- Read interface
      RD       : in  std_logic;
      DISCARD  : in  std_logic;
      DO       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DV       : out std_logic;
      EMPTY    : out std_logic;
      FRAME_RDY : out std_logic
   );
end entity FIFO_BRAM_DISCARD;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of FIFO_BRAM_DISCARD is

   -- Number of address bits
   constant FADDR       : integer := LOG2(ITEMS)-1;

   signal wr_int                 : std_logic;
   signal eob_int                : std_logic;
   signal di_int                 : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal rd_int                 : std_logic;
   signal discard_int            : std_logic;
   signal do_int                 : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal do_dv_int              : std_logic;

   signal write_allow            : std_logic;
   signal read_allow             : std_logic;
   signal discard_allow          : std_logic;
   signal write_req              : std_logic;
   signal empty_int              : std_logic;
   signal full_int               : std_logic;

   signal reg_empty              : std_logic;
   signal reg_full               : std_logic;
   signal reg_lstblk             : std_logic;

   signal cnt_write_addr         : std_logic_vector((FADDR+1) downto 0);
   signal reg_cnt_read           : std_logic_vector((FADDR+1) downto 0);
   signal reg_cnt_read_we        : std_logic;

   signal reg_read_addr          : std_logic_vector((FADDR+1) downto 0);
   signal reg_write_addr         : std_logic_vector((FADDR+1) downto 0);

   signal cnt_diff_dir           : std_logic;
   signal sig_updn               : std_logic_vector((FADDR+1) downto 0);

   signal data_out               : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal data_valid             : std_logic;

   constant gndvec               : std_logic_vector(DATA_WIDTH-1 downto 0)
                                 := (others => '0');

   signal lstblk_plus_one        : std_logic;
   signal lstblk_minus_one       : std_logic;

   signal reg_discard            : std_logic;
   signal reg_discard_set        : std_logic;
   signal reg_discard_clr        : std_logic;

   signal mux_reg_read_addr      : std_logic_vector((FADDR+1) downto 0);
   signal mux_reg_read_addr_sel  : std_logic_vector(1 downto 0);

   signal block_fifo_write_req   : std_logic;
   signal block_fifo_full        : std_logic;
   signal block_fifo_lstblk      : std_logic;
   signal block_fifo_data_out    : std_logic_vector((FADDR+1) downto 0);
   signal block_fifo_read_req    : std_logic;
   signal block_fifo_empty       : std_logic;

   signal mem_reb                : std_logic;
   signal mem_pipe_enb           : std_logic;

   signal mux_cnt_read_addr      : std_logic_vector((FADDR+1) downto 0);
   signal mux_cnt_read_addr_sel  : std_logic_vector(1 downto 0);

   signal mux_new_write_addr     : std_logic_vector((FADDR+1) downto 0);
   signal mux_new_write_addr_sel : std_logic;

   signal sig_diff               : std_logic_vector((FADDR+1) downto 0);
   signal cin                    : std_logic;

   signal reg_diff               : std_logic_vector((FADDR+1) downto 0);
   signal reg_diff_we            : std_logic;

   signal lstblk_discard         : std_logic;

   signal reg_do_dv              : std_logic;
   signal reg_mem_pipe_enb       : std_logic;

   signal reg_do                 : std_logic_vector(DATA_WIDTH - 1 downto 0);

   signal full_out               : std_logic;

   signal latch_do_dv            : std_logic;
   signal sig_read_plus          : std_logic_vector((FADDR+1) downto 0);

   signal mux_diff               : std_logic_vector((FADDR+1) downto 0);
   signal mux_diff_sel           : std_logic_vector(1 downto 0);

-- ----------------------------------------------------------------------------
begin

mem_reb <= read_allow and (not discard_int);
mem_pipe_enb <= rd_int or discard_int;

memory : entity work.sdp_bmem(behavioral)
generic map(
   DATA_WIDTH  => DATA_WIDTH,
   ITEMS       => ITEMS,
   OUTPUT_REG  => FALSE,         -- This output register will be
                                 -- thrown out - for better control over it
   DEBUG       => false
)
port map(
   RESET       => RESET,

   -- Interface A, will be used for writing only
   CLKA        => CLK,
   WEA         => write_allow,
   ADDRA       => reg_write_addr(FADDR downto 0),
   DIA         => di_int,

   -- Interface B, will be used for reading only
   CLKB        => CLK,
   PIPE_ENB    => mem_pipe_enb,
   REB         => mem_reb,
   ADDRB       => reg_read_addr(FADDR downto 0),
   DOB_DV      => data_valid,
   DOB         => data_out
);

-- register reg_do - thrown out from BRAM -------------------------------------
reg_dop: process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_do      <= (others => '0');
      reg_do_dv   <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (mem_pipe_enb = '1') then
         reg_do      <= data_out;
         reg_do_dv   <= latch_do_dv and not discard_int;
      end if;
   end if;
end process;

-- register reg_do - thrown out from BRAM  -------------------------------------
latch_dop: process(RESET, reg_mem_pipe_enb, data_valid, discard_int)
begin
   if (RESET = '1') then
      latch_do_dv   <= '0';
--    elsif (discard_int = '1') then
--       latch_do_dv   <= '0';
   elsif (reg_mem_pipe_enb = '1') then
      latch_do_dv   <= data_valid;
   end if;
end process;



-- Due to the DP_BMEM NOOUTPUT_REG option, this must be pipelined
-- register reg_mem_pipe_enb --------------------------------------------------
reg_mem_pipe_enbp: process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_mem_pipe_enb <= '0';
   elsif (CLK'event AND CLK = '1') then
      reg_mem_pipe_enb <= mem_pipe_enb;
   end if;
end process;


wr_int   <= WR;
eob_int  <= EOB;
di_int   <= DI;


gen_auto_pipe: if (AUTO_PIPELINE = true) generate
   rd_int      <= RD or not do_dv_int;
end generate;

gen_nauto_pipe: if (AUTO_PIPELINE = false) generate
   rd_int      <= RD;
end generate;

discard_int <= DISCARD;
do_int      <= reg_do;
do_dv_int   <= reg_do_dv;

-- ----------------------------------------------------------------------------
--                   Address counters and registers
-- ----------------------------------------------------------------------------
-- cnt_write_addr counter
process(RESET, CLK)
begin
   if (RESET = '1') then
      cnt_write_addr <= conv_std_logic_vector(1, cnt_write_addr'length);
   elsif (CLK'event AND CLK = '1') then
      if (write_allow = '1') then
         cnt_write_addr <= cnt_write_addr + 1;

         if (cnt_write_addr(FADDR downto 0) = ITEMS-1) then
            cnt_write_addr(FADDR downto 0) <= (others => '0');
            cnt_write_addr(FADDR + 1) <= not cnt_write_addr(FADDR + 1);
         end if;

      end if;
   end if;
end process;


-- register reg_cnt_read ------------------------------------------------------
reg_cnt_readp: process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_cnt_read <= conv_std_logic_vector(1, reg_cnt_read'length);
   elsif (CLK'event AND CLK = '1') then
      if (read_allow = '1') then
         reg_cnt_read <= mux_cnt_read_addr;
      end if;
   end if;
end process;


-- reg_write_addr register
process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_write_addr <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (write_allow = '1') then
         reg_write_addr <= cnt_write_addr;
      end if;
   end if;
end process;


-- reg_read_addr register
process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_read_addr <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (read_allow = '1') then
         reg_read_addr <= mux_reg_read_addr;
      end if;
   end if;
end process;


-- multiplexor mux_reg_read_addr --------------------------------------------
mux_reg_read_addr_sel <= block_fifo_empty & discard_int;
mux_reg_read_addrp: process(mux_reg_read_addr_sel, reg_cnt_read,
                            block_fifo_data_out, reg_write_addr)
begin
   case mux_reg_read_addr_sel is
      when "00" => mux_reg_read_addr <= reg_cnt_read;
      when "01" => mux_reg_read_addr <= block_fifo_data_out;
      when "10" => mux_reg_read_addr <= reg_cnt_read;
      when "11" => mux_reg_read_addr <= reg_write_addr;
      when others => mux_reg_read_addr <= (others => 'X');
   end case;
end process;


-- multiplexor mux_cnt_read_addr ----------------------------------------------
mux_cnt_read_addr_sel <= block_fifo_empty & (read_allow and discard_int);
mux_cnt_read_addrp: process(mux_cnt_read_addr_sel,
                            block_fifo_data_out,
                            cnt_write_addr,
                            reg_cnt_read)
begin
   case mux_cnt_read_addr_sel is
      when "00" => mux_cnt_read_addr <= reg_cnt_read + 1;
      when "01" => mux_cnt_read_addr <= block_fifo_data_out + 1;
      when "10" => mux_cnt_read_addr <= reg_cnt_read + 1;
      when "11" => mux_cnt_read_addr <= cnt_write_addr;
      when others => mux_cnt_read_addr <= (others => 'X');
   end case;
end process;


-- ----------------------------------------------------------------------------
--                            Control Logic
-- ----------------------------------------------------------------------------
-- allow logic
discard_allow <= discard_int and not reg_empty;

read_allow <= (rd_int and not reg_empty) or discard_allow;

write_req  <= wr_int and not full_out;
write_allow <= write_req
                  and 
               (not     -- Do not write when discarding and EOB comes
                        -- or when reg_discard is being set
                  ((discard_allow and block_fifo_empty) or reg_discard));

-- empty, full logic
process(mux_reg_read_addr, reg_write_addr, read_allow, write_allow)
begin
	if ((mux_reg_read_addr = reg_write_addr) and (read_allow = '1') and (write_allow = '0')) then
		empty_int <= '1';
	else
		empty_int <= '0';
	end if;
end process;     
  
process(reg_read_addr, cnt_write_addr, write_allow, read_allow)
begin
	if ((reg_read_addr(FADDR downto 0) = cnt_write_addr(FADDR downto 0))
        and (reg_read_addr(FADDR+1) /= cnt_write_addr(FADDR+1))
        and (write_allow = '1') and (read_allow = '0')) then
		full_int <= '1';
	else
		full_int <= '0';
	end if;
end process;  

-- reg_empty register
process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_empty <= '1';
   elsif (CLK'event AND CLK = '1') then
      if ((read_allow = '1') or (write_allow = '1')) then
         reg_empty <= empty_int;
      end if;
   end if;
end process;

-- reg_full register
process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_full <= '0';
   elsif (CLK'event AND CLK = '1') then
      if ((write_allow = '1') or (read_allow = '1')) then
         reg_full <= full_int;
      end if;
   end if;
end process;

-- ----------------------------------------------------------------------------
-- LAST_BLOCK_DETECTION : if (BLOCK_SIZE > 0) generate


process(reg_diff, read_allow, write_allow)
begin
	if (reg_diff = BLOCK_SIZE) and (read_allow = '1') and (write_allow = '0') then
		lstblk_plus_one <= '1';
	else
		lstblk_plus_one <= '0';
	end if;
end process;  

process(reg_diff, write_allow, read_allow)
begin
	if (reg_diff = BLOCK_SIZE + 1 ) and (write_allow = '1') and (read_allow = '0') then
		lstblk_minus_one <= '1';
	else
		lstblk_minus_one <= '0';
	end if;
end process;

process(sig_diff, mux_new_write_addr, mux_reg_read_addr, discard_int)
begin
  if (sig_diff <= BLOCK_SIZE) and 
      (mux_new_write_addr(FADDR+1) /= mux_reg_read_addr(FADDR+1))
      and (discard_int = '1') then
          lstblk_discard <= '1';
      else
          lstblk_discard <= '0';
  end if;
end process;

-- multiplexor mux_new_write_addr ---------------------------------------------
mux_new_write_addr_sel <= write_allow;
mux_new_write_addrp: process(mux_new_write_addr_sel, reg_write_addr,
                             cnt_write_addr)
begin
   case mux_new_write_addr_sel is
      when '0' => mux_new_write_addr <= reg_write_addr;
      when '1' => mux_new_write_addr <= cnt_write_addr;
      when others => mux_new_write_addr <= (others => 'X');
   end case;
end process;


cin <= write_allow;
sig_diff <= (block_fifo_data_out - reg_write_addr - cin);

cnt_diff_dir <= read_allow;
sig_updnp: process(cnt_diff_dir, reg_diff)
begin
   if (cnt_diff_dir = '1') then
      sig_updn <= reg_diff + 1;
   else
      sig_updn <= reg_diff - 1;
   end if;
end process;


-- multiplexor mux_diff ---------------------------------------------------
mux_diff_sel <= discard_int & empty_int;
mux_diffp: process(mux_diff_sel, sig_diff, sig_updn)
begin
   case mux_diff_sel is
      when "00" => mux_diff <= sig_updn;
      when "01" => mux_diff <= sig_updn;
      when "10" => mux_diff <= sig_diff;
      when "11" => mux_diff <= conv_std_logic_vector(ITEMS, mux_diff'length);
      when others => mux_diff <= (others => 'X');
   end case;
end process;


-- register reg_diff ------------------------------------------------------
reg_diff_we <= ((read_allow xor write_allow) and (not discard_int)) or
               (discard_int and read_allow);
reg_diffp: process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_diff <= conv_std_logic_vector(ITEMS, reg_diff'length);
   elsif (CLK'event AND CLK = '1') then
      if (reg_diff_we = '1') then
         reg_diff <= mux_diff;
      end if;
   end if;
end process;



-- register reg_lstblk
reg_lstblkp: process(RESET, CLK)
begin
   if (RESET = '1') then
      if (BLOCK_SIZE < ITEMS) then
         reg_lstblk <= '0';
      else
         reg_lstblk <= '1';
      end if;
   elsif (CLK'event AND CLK = '1') then
      if (lstblk_plus_one = '1') or (lstblk_minus_one = '1') or
         (discard_int = '1') then
         reg_lstblk <= ((lstblk_minus_one and not lstblk_plus_one) and
                        (not discard_int)) or
                        lstblk_discard;
      end if;
   end if;
end process;


-- end generate;

-- ----------------------------------------------------------------------------
block_fifo_write_req <= write_allow and eob_int;
process(read_allow, discard_int, block_fifo_data_out, reg_cnt_read,
        block_fifo_empty)
begin
  if (read_allow = '1' and discard_int = '1')
     or (read_allow = '1' 
     and (block_fifo_data_out = reg_cnt_read)
     and block_fifo_empty = '0') then
         block_fifo_read_req <= '1';
  else
         block_fifo_read_req <= '0';
  end if;
end process;

blocks_fifo: entity work.fifo
   generic map (
      -- Set data width here
      DATA_WIDTH     => FADDR + 2,

      -- Distributed RAM type, only 16, 32, 64 bits
      DISTMEM_TYPE   => 16,

      -- Set number of items in FIFO here
      ITEMS          => MAX_DISCARD_BLOCKS,

      -- for last block identification
      BLOCK_SIZE     => 1
   )
   port map (
      RESET       => RESET,
      CLK         => CLK,

      -- Write interface
      DATA_IN     => cnt_write_addr,
      WRITE_REQ   => block_fifo_write_req,
      FULL        => block_fifo_full,
      LSTBLK      => block_fifo_lstblk,

      -- Read interface
      DATA_OUT    => block_fifo_data_out,
      READ_REQ    => block_fifo_read_req,
      EMPTY       => block_fifo_empty
   );


-- register reg_discard ------------------------------------------------------
                   --      Discard is allowed    and   block not complete and
                   --            |                              |
                   --  -------------------------     -----------------
reg_discard_set <= not reg_empty and discard_int and block_fifo_empty and
                  -- not trying to write EOB simultaneously
                  --           |
                  --   --------------------
                   not (write_req and eob);
reg_discard_clr <= write_req and eob_int;
reg_discardp: process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_discard <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (reg_discard_clr = '1') then
         reg_discard <= '0';
      elsif (reg_discard_set = '1') then
         reg_discard <= '1';
      end if;
   end if;
end process;


-- ----------------------------------------------------------------------------
full_out <= reg_full or block_fifo_full;

-- interface mapping
FULL        <= full_out;
EMPTY       <= reg_empty;
LSTBLK      <= reg_lstblk;
DO          <= do_int;
DV          <= do_dv_int;
STATUS      <= reg_diff((FADDR+1) downto (FADDR+1)-STATUS_WIDTH+1);
FRAME_RDY   <= not block_fifo_empty;

end architecture behavioral;
-- ----------------------------------------------------------------------------

