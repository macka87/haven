-- Copyright (C) 2012 
-- Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

library ieee;
use ieee.std_logic_1164.all;
--use ieee.std_logic_arith.all;
use ieee.numeric_std.all;
use work.TINYMT32.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity MT_N is
  generic(
     -- number of generated words (1 word = 32 bit)
     OUTPUT_WIDTH   : integer
  );
  
  port
  (
     CLK         : in  std_logic;
     RST         : in  std_logic;
     INIT        : in  std_logic;
     SEED        : in  std_logic_vector(31 downto 0);
     RND_RUN     : in  std_logic;
     RND_VAL     : out std_logic;
     RND_NUM     : out std_logic_vector(OUTPUT_WIDTH-1 downto 0)
     
  );
end entity MT_N;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of MT_N is

-- ==========================================================================
--                           CONSTANTS
-- ==========================================================================
constant COUNT : integer := (OUTPUT_WIDTH-1)/32 + 1;

type param_arr is array (0 to COUNT-1) of PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;

type run_num_arr is array (0 to COUNT-1) of RANDOM_NUMBER_TYPE;

-- default initialization settings
constant DEFAULT_PARAM   : PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE :=
                           NEW_PSEUDO_RANDOM_NUMBER_GENERATOR(
                             X"8f7011ee",
                             X"fc78ff1f",
                             X"3793fdff",
                             X"00000001"
                           );

-- ==========================================================================
--                           SIGNALS
-- ==========================================================================
signal params          : param_arr;
signal sig_rnd_num     : run_num_arr;
signal sig_valid       : std_logic_vector(COUNT-1 downto 0);

-- ==========================================================================
--                           ARCHITECTURE BODY
-- ==========================================================================
begin

  -- Assertions
  assert (OUTPUT_WIDTH > 0)
    report "Unsupported OUTPUT_WIDTH!"
    severity failure;
  
  -- instanciate Marsenne twister generators
  GEN_MT: for i in 0 to COUNT-1 generate

      MT_I : entity work.TINYMT32_GEN
         port map(
            CLK            => CLK,
            RST            => RST,
            INIT           => INIT,
            INIT_PARAM     => params(i),
            RND_RUN        => RND_RUN,
            RND_VAL        => sig_valid(i),
            RND_NUM        => sig_rnd_num(i) 
         );
  end generate;    
  
  -- set parameters of MT generators
  set_parameters : process(CLK)
    variable new_param : PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
  begin
    new_param := DEFAULT_PARAM;
    new_param.status(0) := unsigned(SEED);  
    
    for i in 0 to COUNT-1 loop
      new_param.status(0) := new_param.status(0) + 1;
      params(i) <= new_param;
    end loop;
  end process; 
  
  -- set output valid signal
  set_valid : process(CLK)
    variable out_valid : std_logic;
  begin
    out_valid := '1';
    for i in 0 to COUNT-1 loop
      out_valid := out_valid and sig_valid(i);
    end loop;
  
    RND_VAL <= out_valid;
  end process;   
  
  -- create output random number according to values from generators
  set_rnd_num : process (CLK)
    variable rnd_num_var : std_logic_vector(COUNT*32-1 downto 0);
  begin
    for i in 0 to COUNT-1 loop
      rnd_num_var(i*32+31 downto i*32) :=  std_logic_vector(sig_rnd_num(i));
    end loop;
    
    RND_NUM <= rnd_num_var(OUTPUT_WIDTH-1 downto 0);
  end process;
 
end architecture;