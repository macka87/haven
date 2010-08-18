library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.math_pack.all;

-- -----------------------------------------------------------------------
--                       Entity declaration
-- -----------------------------------------------------------------------
entity testbench is
end entity testbench;

-- -----------------------------------------------------------------------
--                    Architecture declaration
-- -----------------------------------------------------------------------
architecture behavioral of testbench is

component cmd_dec is
   generic(
      NUM_PATHS : integer
   );
   port(
      -- Input interface
      DI       : in    std_logic_vector((NUM_PATHS*8)-1 downto 0); -- Input Data
      DI_CMD   : in    std_logic_vector((NUM_PATHS-1) downto 0);
      EN       : in    std_logic;

      -- Output interface
      DO       : out   std_logic_vector((NUM_PATHS*8)-1 downto 0); -- Output Data
      CMD_SOP  : out   std_logic;
      CMD_SOC  : out   std_logic;
      CMD_IDLE : out   std_logic;
      CMD_TERM : out   std_logic;
      CMD_DATA : out   std_logic;
      LEN      : out   std_logic_vector(log2(NUM_PATHS)-1 downto 0)
   );
end component cmd_dec;


   constant clkper : time := 10 ns;
   constant NUM_PATHS : integer:= 4;
   signal di_f     : std_logic_vector((NUM_PATHS*8)-1 downto 0)
                     := (others => '0');
   signal di_cmd_f : std_logic_vector((NUM_PATHS-1) downto 0)
                     := (others => '1');

   signal clk      : std_logic;
   signal di       : std_logic_vector((NUM_PATHS*8)-1 downto 0);
   signal di_cmd   : std_logic_vector((NUM_PATHS-1) downto 0);
   signal en       : std_logic;
   signal do       : std_logic_vector((NUM_PATHS*8)-1 downto 0);
   signal cmd_sop  : std_logic;
   signal cmd_soc  : std_logic;
   signal cmd_idle : std_logic;
   signal cmd_term : std_logic;
   signal cmd_data : std_logic;
   signal len      : std_logic_vector(log2(NUM_PATHS+1)-1 downto 0);


begin

-- ----------------------------------------------------
uut : cmd_dec
generic map(
   NUM_PATHS => NUM_PATHS
)
port map(
   -- Input interface
   DI       => di,
   DI_CMD   => di_cmd,
   EN       => en,

   -- Output interface
   DO       => do,
   CMD_SOP  => cmd_sop,
   CMD_SOC  => cmd_soc,
   CMD_IDLE => cmd_idle,
   CMD_TERM => cmd_term,
   CMD_DATA => cmd_data,
   LEN      => len
);

-- ----------------------------------------------------
clkgen : process
begin
	clk <= '1';
	wait for clkper/2;
	clk <= '0';
	wait for clkper/2;
end process;


-- ----------------------------------------------------
tb: process

-- ----------------------------------------------------
procedure get_input_data(file_name   : in string) is
file in_file      : text;
variable in_line  : line;
variable data     : std_logic_vector((NUM_PATHS*9)-1 downto 0);
variable good     : boolean;

begin
   -- inicialization
   di_cmd_f <= (others => '1');

   -- open input file
   file_open(in_file, file_name, READ_MODE);
   wait until (clk'event and clk='1');

   -- write packet
   while not (endfile(in_file)) loop
      readline(in_file, in_line);
      hread(in_line, data, good);
      di_f <= data((NUM_PATHS*8)-1 downto 0);
      di_cmd_f <= data((NUM_PATHS*9)-1 downto (NUM_PATHS*8));
      wait for clkper;
   end loop;
   di_f <= (others => '0');
   di_cmd_f <= (others => '1');
   wait for 0 ns;

   -- close input file
   file_close(in_file);

   -- synchronization with LCLKF
   wait until (clk'event and clk='1');

end get_input_data;

begin
   en <= '0';

   wait for 5*clkper;
   en <= '1';
   get_input_data("data4.txt");

	wait;
end process;

di       <= di_f;
di_cmd   <= di_cmd_f;

end architecture behavioral;

