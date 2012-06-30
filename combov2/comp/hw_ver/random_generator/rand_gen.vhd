-- Copyright (C) 2012 
-- Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================

-- generator of a stream of random numbers of specified width
entity RAND_GEN is
  generic(
     OUTPUT_WIDTH   : integer := 64
  );
  
  port
  (
     -- common signals
     CLK         : in  std_logic;
     RESET       : in  std_logic;

     -- MI32 interface
     MI_DWR    :  in std_logic_vector(31 downto 0);
     MI_ADDR   :  in std_logic_vector(31 downto 0);
     MI_RD     :  in std_logic;
     MI_WR     :  in std_logic;
     MI_BE     :  in std_logic_vector( 3 downto 0);
     MI_DRD    : out std_logic_vector(31 downto 0);
     MI_ARDY   : out std_logic;
     MI_DRDY   : out std_logic;

     -- output
     RND_VAL     : out std_logic;
     RND_NUM     : out std_logic_vector(OUTPUT_WIDTH-1 downto 0);
     RND_RUN     :  in std_logic
  );
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of RAND_GEN is

-- ==========================================================================
--                               CONSTANTS
-- ==========================================================================

-- ==========================================================================
--                                SIGNALS
-- ==========================================================================

-- input signals
signal sig_mi_dwr       : std_logic_vector(31 downto 0);
signal sig_mi_addr      : std_logic_vector(31 downto 0);
signal sig_mi_rd        : std_logic;
signal sig_mi_wr        : std_logic;
signal sig_mi_be        : std_logic_vector( 3 downto 0);
signal sig_mi_drd       : std_logic_vector(31 downto 0);
signal sig_mi_ardy      : std_logic;
signal sig_mi_drdy      : std_logic;

-- output signals
signal sig_rnd_val      : std_logic;
signal sig_rnd_num      : std_logic_vector(OUTPUT_WIDTH-1 downto 0);
signal sig_rnd_run      : std_logic;

-- the address decoder
signal sig_sel_run      : std_logic;
signal sig_sel_seed     : std_logic;

-- the Run register
signal reg_run          : std_logic;
signal reg_run_in       : std_logic;
signal reg_run_en       : std_logic;
signal reg_run_out      : std_logic_vector(31 downto 0);

-- the Seed register
signal reg_seed         : std_logic_vector(31 downto 0);
signal reg_seed_in      : std_logic_vector(31 downto 0);
signal reg_seed_en      : std_logic;

-- the register orchestrating initialisation
signal reg_init         : std_logic;
signal reg_init_set     : std_logic;
signal reg_init_clr     : std_logic;

-- Mersenne Twister signals
signal mt_init          : std_logic;
signal mt_seed          : std_logic_vector(31 downto 0);
signal mt_rnd_run       : std_logic;
signal mt_rnd_val       : std_logic;
signal mt_rnd_num       : std_logic_vector(OUTPUT_WIDTH-1 downto 0);

-- MI32 output multiplexer
signal mux_mi_out       : std_logic_vector(31 downto 0);


-- ==========================================================================
--                           ARCHITECTURE BODY
-- ==========================================================================
begin

   -- mapping input signals
   sig_mi_dwr    <= MI_DWR;
   sig_mi_addr   <= MI_ADDR;
   sig_mi_rd     <= MI_RD;
   sig_mi_wr     <= MI_WR;
   sig_mi_be     <= MI_BE;
   MI_DRD        <= sig_mi_drd;
   MI_ARDY       <= sig_mi_ardy;
   MI_DRDY       <= sig_mi_drdy;

   -- mapping MI32 signals
   sig_mi_ardy   <= sig_mi_rd OR sig_mi_wr;
   sig_mi_drdy   <= sig_mi_rd;
   sig_mi_drd    <= mux_mi_out;

   -- -----------------------------------------------------------------------
   --                      The Address Space (in binary)
   --
   --  0000 : The Run register
   --  0100 : The Seed register - writing into this register also triggers
   --                             initialisation
   -- -----------------------------------------------------------------------

   -- the address decoder
   addr_dec_p: process(sig_mi_addr, reg_run_out, reg_seed)
   begin
      sig_sel_run  <= '0';
      sig_sel_seed <= '0';

      mux_mi_out   <= reg_run_out;

      case (sig_mi_addr(2)) is
         when '0'    => sig_sel_run  <= '1';
                        mux_mi_out   <= reg_run_out;
         when '1'    => sig_sel_seed <= '1';
                        mux_mi_out   <= reg_seed;
         when others => null;
      end case;
   end process;

   --
   reg_run_en <= sig_sel_run AND sig_mi_wr;
   reg_run_in <= sig_mi_dwr(0);

   -- the Run register
   reg_run_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_run <= '0';
         elsif (reg_run_en = '1') then
            reg_run <= reg_run_in;
         end if;
      end if;
   end process;

   reg_run_out <= X"2A1D6E1" & "000" & reg_run;

   --
   reg_seed_en <= sig_sel_seed AND sig_mi_wr;
   reg_seed_in <= sig_mi_dwr;

   -- the Seed register
   reg_seed_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (reg_seed_en = '1') then
            reg_seed <= reg_seed_in;
         end if;
      end if;
   end process;

   --
   reg_init_set  <= reg_seed_en;
   reg_init_clr  <= reg_init;

   -- the register that orchestrates initialiasation of tthe generator in the
   -- clock cycle following the write into the seed register
   reg_init_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then 
            reg_init <= '0';
         elsif (reg_init_set = '1') then
            reg_init <= '1';
         elsif (reg_init_clr = '1') then
            reg_init <= '0';
         end if;
      end if;
   end process;

   --
   mt_init <= reg_init;
   mt_seed <= reg_seed;
   mt_rnd_run <= sig_rnd_run AND reg_run;

   -- the Pan-Galactic Mega-Twister... ehm... Mersenne Twister...
   MT_N_I : entity work.MT_N
   generic map(
      OUTPUT_WIDTH  => OUTPUT_WIDTH
   )
   port map(
      CLK         => CLK,
      RST         => RESET,

      INIT        => mt_init,
      SEED        => mt_seed,
      RND_RUN     => mt_rnd_run,
      RND_VAL     => mt_rnd_val,
      RND_NUM     => mt_rnd_num
   );
  
   sig_rnd_val  <= mt_rnd_val AND reg_run;
   sig_rnd_num  <= mt_rnd_num;

   -- mapping outputs
   RND_VAL      <= sig_rnd_val;
   RND_NUM      <= sig_rnd_num;
   sig_rnd_run  <= RND_RUN;
 
end architecture;
