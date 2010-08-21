-------------------------------------------------------------------
--                                                               --
-- Copyright 1991-2009 Mentor Graphics Corporation.              --
-- All rights reserved.                                          --
--                                                               --
-------------------------------------------------------------------
--                                                               --
-- Project   :   DK                                              --
-- Date      :   22 MAR 2000                                     --
-- File      :   dk.vhd                                          --
-- Author    :   Andy Rushton (AR)                               --
-- Contributors:                                                 --
--     James Rowland (JR)                                        --
--     Carlos M. Rincón (CMR)                                    --
--     John Alexander (JA)                                       --
--     Johan Ditmar (JD)                                         --
--                                                               --
-- Description:                                                  --
--     Support library for DK generated VHDL                     --
--                                                               --
-- Date         Version  Author  Reason for change               --
--                                                               --
-- 22 MAR 2000    1.00    AR     Created                         --
-- 29 SEP 2000    1.01    JR     Added pulse sequence generator  --
--                               component                       --
-- 14 DEC 2000    1.02    CMR    Renamed package to avoid name   --
--                               conflicts in 3rd party VHDL     --
--                               tools                           --
-- 19 DEC 2000    1.03    JA     Modified clockdiv component to  --
--                               bring in line with the pulse    --
--                               generator component             --
-- 10 JAN 2001    1.04    JA     Further changes to clockdiv for --
--                               compatibility with the old      --
--                               version of clockdiv             --
-- 10 JAN 2002    2.00    JD     Updated for version 3.1         --
-- 02 MAR 2002    2.01    JD     Changed the reset statements to --
--                               make hardware run for Altera    --
-- 02 JUN 2004    3.00    JD     Updated for IEEE 1076.6         --
-- 29 OCT 2004    3.01    JD     Updated for DK3.1               --
-- 22 JUN 2005    4.00    JD     Updated for DK4                 --
-- 03 APR 2006    5.00    JD     Updated for DK5                 --
-- 06 OCT 2006    5.01    JD     Added safe startup component    --
-- 31 MAR 2008    5.02    CMR    Renamed from 'celoxica.vhd'     --
-- 31 MAR 2009    5.05    KH     Renamed from 'agility.vhd'      --
--                                                               --
-------------------------------------------------------------------

LIBRARY ieee;
USE IEEE.std_logic_1164.ALL;
USE IEEE.numeric_std.ALL;
PACKAGE DKPackage IS

  -- Conditional Functions
  FUNCTION cond (c : std_logic; t, f : std_logic) RETURN std_logic;
  FUNCTION cond (c : std_logic; t, f : std_logic_vector) RETURN std_logic_vector;
  FUNCTION cond (c : std_logic; t, f : unsigned) RETURN unsigned;

  -- Synthesizable Arithmetic Functions
  FUNCTION div (x, y : unsigned) RETURN unsigned;
  FUNCTION div (x, y : signed) RETURN signed;
  FUNCTION modulus (x, y : unsigned) RETURN unsigned;
  FUNCTION modulus (x, y : signed) RETURN signed;

  -- Conversion Functions
  FUNCTION to_signed (x : std_logic) RETURN signed;
  FUNCTION to_unsigned (x : std_logic) RETURN unsigned;
  FUNCTION to_stdlogic (x : signed) RETURN std_logic;
  FUNCTION to_stdlogic (x : unsigned) RETURN std_logic;
  FUNCTION to_stdlogic (x : std_logic_vector) RETURN std_logic;
  FUNCTION to_stdlogic (x : boolean) RETURN std_logic;
  FUNCTION to_stdlogicvector (x : std_logic) RETURN std_logic_vector;
  FUNCTION to_integer (x : std_logic) RETURN integer;
  FUNCTION to_integer (x : std_logic_vector) RETURN integer;
  FUNCTION to_boolean (x : signed) RETURN boolean;
  FUNCTION to_boolean (x : unsigned) RETURN boolean;
  FUNCTION to_boolean (x : std_logic) RETURN boolean;

  COMPONENT CrossdomainSynchroniser IS
    generic (
      width : integer;
      paranoia : integer);
    port (
      clockin  : in  std_logic;
      clockout : in  std_logic;
      syncresetin : in std_logic;
      asyncresetin :in std_logic;
      syncresetout : std_logic;
      asyncresetout : std_logic;
      datain   : in  std_logic_vector;
      dataout  : out std_logic_vector);
  end COMPONENT;

  COMPONENT RegisterPair IS
    generic (
      width : integer);
    port (
      clockin  : in  std_logic;
      clockout : in  std_logic;
      syncresetin : in std_logic;
      asyncresetin :in std_logic;
      syncresetout : std_logic;
      asyncresetout : std_logic;
      datain   : in  std_logic_vector;
      dataout  : out std_logic_vector;
      enablein : in std_logic;
      enableout : in std_logic);
  end COMPONENT;

  COMPONENT BlackBoxFIFO IS
    generic (
      datawidth : integer;
      addrwidth : integer;
      fifodepth : integer );
    port (
      clockin  : in  std_logic;
      clockout : in  std_logic;
      readenable : in std_logic;
      writeenable : in std_logic;
      asyncreset : in std_logic;
      datain   : in  std_logic_vector;
      dataout  : out std_logic_vector;
      full : out std_logic;
      empty : out std_logic
    );
  end COMPONENT BlackBoxFIFO;

  COMPONENT CelStart IS
    GENERIC (inpipelength : integer;
             outpipelength : integer);
    PORT(clk : in std_logic;
         aclr : in std_logic;
         sclr : in std_logic;
         start : out std_logic);
  END COMPONENT;

  COMPONENT clockdiv
      GENERIC (high1 : integer;
             low   : integer;
             high2 : integer);
      PORT (ckout : OUT std_logic;                   -- divided clock output
            ckin  : IN std_logic;                    -- original clock input
            rst   : IN std_logic := '0');            -- asynchronous reset (active high)
  END COMPONENT;

  COMPONENT pulsegen
    GENERIC(pulse : integer;
            length : integer);
      PORT (ckout : OUT std_logic;                   -- pulse sequence generated
            ckin  : IN std_logic;                    -- original clock input
            rst   : IN std_logic);                   -- asynchronous reset (active high)
  END COMPONENT;

END;

PACKAGE BODY DKPackage IS

  -- internal division procedure performs unsigned division with remainder
  -- compensates for the lack of synthesizable division operator in numeric_std
  PROCEDURE divmod (xnum, xdenom: unsigned; xquot, xremain: OUT unsigned) is
      VARIABLE denominator : unsigned(xdenom'LENGTH-1 DOWNTO 0);
      VARIABLE numerator : unsigned(xnum'LENGTH-1 DOWNTO 0);
      VARIABLE remainder : unsigned(xnum'LENGTH+xdenom'LENGTH-2 DOWNTO 0);
      VARIABLE quotient : unsigned(xnum'LENGTH-1 DOWNTO 0);

    BEGIN
        denominator := xdenom;
      numerator := xnum;

        -- synopsys synthesis_off
        ASSERT denominator /= to_unsigned(0,denominator'LENGTH) REPORT "divide by zero" SEVERITY WARNING;
      -- synopsys synthesis_on
        remainder := RESIZE(numerator, remainder'length);
        quotient := TO_UNSIGNED(0, quotient'length);

        FOR i IN quotient'range LOOP
          IF remainder(i+denominator'LEFT DOWNTO i) >= denominator THEN
              remainder(i+denominator'LEFT DOWNTO i) := remainder(i+denominator'LEFT DOWNTO i) - denominator;
              quotient(i) := '1';
          END IF;
        END LOOP;

      xquot := RESIZE(quotient, xquot'length);
        xremain := RESIZE(remainder, xremain'length);

    END divmod;

    FUNCTION div (x, y : unsigned) RETURN unsigned IS
        VARIABLE quotient : unsigned(x'LENGTH-1 DOWNTO 0);
        VARIABLE remainder : unsigned(x'LENGTH-1 DOWNTO 0);

      BEGIN
          -- synopsys synthesis_off
          ASSERT x'LENGTH = y'LENGTH REPORT "arguments must be the same size";
        -- synopsys synthesis_on
          divmod(x, y, quotient, remainder);
          RETURN quotient;
      END;

    -- signed divide is defined in terms of unsigned divide with negations
    FUNCTION div (x, y : signed) RETURN signed IS
        VARIABLE quotient : unsigned(x'LENGTH-1 DOWNTO 0);
        VARIABLE remainder : unsigned(x'LENGTH-1 DOWNTO 0);

      BEGIN
          -- synopsys synthesis_off
          ASSERT x'LENGTH = y'LENGTH report "arguments must be the same size";
        ASSERT x'LENGTH >= 1 and y'LENGTH >= 1 report "arguments must be at least one bit";
        -- synopsys synthesis_on

          divmod(unsigned(signed'(abs x)), unsigned(signed'(abs y)), quotient, remainder);
          -- result is negated if the signs are different
          IF to_boolean(x(x'LEFT)) /= to_boolean(y(y'LEFT)) THEN
          RETURN -signed(quotient);
          ELSE
            RETURN signed(quotient);
          END IF;
      END;

    -- the C % operator is equivalent to the VHDL rem operator
    FUNCTION modulus (x, y : unsigned) RETURN unsigned is
        VARIABLE quotient : unsigned(x'length-1 downto 0);
        VARIABLE remainder : unsigned(x'length-1 downto 0);

      BEGIN
          -- synopsys synthesis_off
          assert x'length = y'length report "arguments must be the same size";
        -- synopsys synthesis_on
        divmod(x, y, quotient, remainder);
          RETURN remainder;
      END;

    FUNCTION modulus (x, y : signed) RETURN signed is
        VARIABLE quotient : unsigned(x'LENGTH-1 downto 0);
        VARIABLE remainder : unsigned(x'LENGTH-1 downto 0);

      BEGIN
          -- synopsys synthesis_off
          ASSERT x'LENGTH = y'LENGTH report "arguments must be the same size";
          ASSERT x'LENGTH >= 1 and y'LENGTh >= 1 report "arguments must be at least one bit";
        -- synopsys synthesis_on

        divmod(unsigned(signed'(abs x)), unsigned(signed'(abs y)), quotient, remainder);
        -- result is negated if the numerator was negative
        IF to_boolean(x(x'left)) THEN
          RETURN -signed(remainder);
        ELSE
          RETURN signed(remainder);
        END IF;
      END;

    FUNCTION cond (c : std_logic; t, f : std_logic) RETURN std_logic IS
    BEGIN
        IF c = '1' or c = 'H' THEN
          RETURN t;
        ELSIF c = '0' or c = 'L' THEN
          RETURN f;
        ELSE
          RETURN 'X';
        END IF;
    END;

    FUNCTION cond (c : std_logic; t, f : std_logic_vector) RETURN std_logic_vector IS
    BEGIN
        IF c = '1' or c = 'H' THEN
          RETURN t;
        ELSIF c = '0' or c = 'L' THEN
          RETURN f;
        ELSE
          RETURN (t'RANGE => 'X');
        END IF;
    END;

    FUNCTION cond (c : std_logic; t, f : unsigned) RETURN unsigned IS
    BEGIN
        -- synopsys synthesis_off
        ASSERT t'LENGTH = f'LENGTH REPORT "arguments must be the same size";
      -- synopsys synthesis_on
      IF c = '1' or c = 'H' THEN
        RETURN t;
      ELSIF c = '0' or c = 'L' THEN
        RETURN f;
      ELSE
        RETURN (t'RANGE => 'X');
      END IF;
    END;

    FUNCTION to_signed (x : std_logic) RETURN signed IS
    BEGIN
      return SIGNED(to_stdlogicvector(x));
    END;

    FUNCTION to_unsigned (x : std_logic) RETURN unsigned IS
    BEGIN
      return UNSIGNED(to_stdlogicvector(x));
    END;

    FUNCTION to_stdlogic (x : signed) RETURN std_logic IS
      VARIABLE result : std_logic_vector(x'LENGTH-1 DOWNTO 0);
    BEGIN
      result := STD_LOGIC_VECTOR(x);
      RETURN result(0);
    END;

    FUNCTION test (x, y : signed) RETURN signed IS
    BEGIN
      RETURN RESIZE(x*y, 4);
    END;

    FUNCTION to_stdlogic (x : unsigned) RETURN std_logic IS
      VARIABLE result : std_logic_vector(x'LENGTH-1 DOWNTO 0);
    BEGIN
      result := STD_LOGIC_VECTOR(x);
      RETURN result(0);
    END;

    FUNCTION to_stdlogic (x : std_logic_vector) RETURN std_logic IS
    BEGIN
      RETURN x(0);
    END;

    FUNCTION to_stdlogic (x : boolean) RETURN std_logic IS
    BEGIN
        CASE x IS
          WHEN true => RETURN '1';
          WHEN false => RETURN '0';
      END CASE;
    END;

    FUNCTION to_stdlogicvector (x : std_logic) RETURN std_logic_vector IS
      VARIABLE result : std_logic_vector(0 DOWNTO 0);
    BEGIN
      result(0) := x;
      RETURN result;
    END;

    FUNCTION to_integer(x : std_logic_vector) RETURN integer IS
       VARIABLE result: integer;
    BEGIN
    --synopsys synthesis_off
       ASSERT x'length <= 31
       REPORT "x is too large in CONV_INTEGER"
       SEVERITY FAILURE;
    --synopsys synthesis_on
       result := 0;
       FOR i IN x'reverse_range LOOP
           IF x(i) = '1' THEN
               result := result + 2 ** i;
           END IF;
       END LOOP;
       RETURN result;
    END;

    FUNCTION to_integer (x : std_logic) RETURN integer IS
    BEGIN
        IF (x='1') THEN
            RETURN (1);
        ELSE
            RETURN (0);
        END IF;
    END;

    FUNCTION to_boolean (x : signed) RETURN boolean IS
    BEGIN
        RETURN to_boolean(to_stdlogic(x));
    END;

    FUNCTION to_boolean (x : unsigned) RETURN boolean IS
    BEGIN
        RETURN to_boolean(to_stdlogic(x));
    END;

    FUNCTION to_boolean (x : std_logic) RETURN boolean IS
    BEGIN
      CASE x IS
          WHEN '0' | 'L' => RETURN false;
          WHEN others => RETURN true;
      END CASE;
    END;

END;

-------------------------------------------------------------------------------

LIBRARY IEEE;
USE IEEE.std_logic_1164.ALL;
ENTITY BlackBoxFIFO IS
    generic (
      datawidth : integer;
      addrwidth : integer;
      fifodepth : integer);
    port (
      clockin  : in  std_logic;
      clockout : in  std_logic;
      readenable : in std_logic;
      writeenable : in std_logic;
      asyncreset : in std_logic;
      datain   : in  std_logic_vector(datawidth-1 downto 0);
      dataout  : out std_logic_vector(datawidth-1 downto 0);
      full : out std_logic;
      empty : out std_logic
  );
  end entity BlackBoxFIFO;


-- BlackBoxFIFO is intended for simulation and as an example. It will not work if synthesised.
architecture Behave of BlackBoxFIFO is

      signal readptr : integer := 0;
      signal writeptr : integer := 0;
      type fiforam is array (0 to fifodepth) of std_logic_vector(datawidth-1 downto 0);
      signal a : fiforam := ( others => ( others => '0' ) );

      FUNCTION nextaddr(x : integer) RETURN integer is

      BEGIN

          assert 0 <= x and x <= fifodepth report "FIFO address out of range";

          if x=fifodepth then
             return 0;
          else
             return x+1;
          end if;

      end nextaddr;

    begin  -- Behave

      process(clockout,asyncreset)
        begin

        if asyncreset='1' then

          empty <= '1';
          readptr <= 0;

        elsif rising_edge(clockout) then

          assert not( readptr=writeptr and readenable = '1') report "Reading from an empty FIFO" severity failure;

          if readenable = '1' then

            readptr <= nextaddr(readptr);
            dataout <= a( nextaddr(readptr) );
            if nextaddr(readptr)=writeptr then
              empty <= '1';
            else
              empty <= '0';
            end if;

          else

            dataout <= a( readptr );
            if readptr=writeptr then
              empty <= '1';
            else
              empty <= '0';
            end if;

          end if;

        end if;
      end process;

      process(clockin,asyncreset)
        begin
        if asyncreset='1' then

          full <= '0';
          writeptr <= 0;

        elsif rising_edge(clockin) then

          if writeenable='1' then

              assert not(nextaddr(writeptr) = readptr) report "Writing to a full FIFO" severity failure;

              a(writeptr) <= datain;
              writeptr <= nextaddr(writeptr);
              if nextaddr(nextaddr(writeptr)) = readptr then
                full <= '1';
              else
                full <= '0';
              end if;
          else
              if nextaddr(writeptr) = readptr then
                full <= '1';
              else
                full <= '0';
              end if;
          end if;

        end if;
      end process;

    end Behave;


LIBRARY IEEE;
USE IEEE.std_logic_1164.ALL;
ENTITY CrossdomainSynchroniser IS
    generic (
      width : integer;
      paranoia : integer);
    port (
      clockin  : in  std_logic;
      clockout : in  std_logic;
      syncresetin : in std_logic;
      asyncresetin :in std_logic;
      syncresetout : in std_logic;
      asyncresetout : in std_logic;
      datain   : in  std_logic_vector(width-1 downto 0);
      dataout  : out std_logic_vector(width-1 downto 0) := (others => '0' ) );
  end entity CrossdomainSynchroniser;

-- This implementation is suitable for simulation but not synthesis
-- It must be replaced by a correctly constrained alternative. See documentation.
architecture Behave of CrossdomainSynchroniser is

    signal crossing : std_logic_vector(width-1 downto 0) := (others => '0' );
    constant zero : std_logic_vector(width-1 downto 0) := (others => '0');

    TYPE pipelinetype IS ARRAY (paranoia DOWNTO 0) of STD_LOGIC_VECTOR(width-1 downto 0);
    SIGNAL pipeline : pipelinetype := ( OTHERS => zero );

    begin  -- Behave

      process(clockin,asyncresetin)
        begin
        if asyncresetin='1' then
          crossing <= zero;
        elsif rising_edge(clockin) then
          if syncresetin='1' then
            crossing <= zero;
          else
            crossing <= datain;
          end if;
        end if;
      end process;

     PROCESS (clockout, asyncresetout)
      BEGIN
        IF asyncresetout='1' THEN
          pipeline <= ( OTHERS => zero );
        ELSIF rising_edge(clockout) THEN
          IF syncresetout='1' THEN
            pipeline <= ( OTHERS => zero );
          ELSE
            FOR i IN 0 TO paranoia-1 LOOP
              pipeline(i+1) <= pipeline(i);
            END LOOP;
            pipeline(0) <= crossing;
          END IF;
        END IF;
      END PROCESS;

      dataout <= pipeline(paranoia);

    end Behave;

LIBRARY IEEE;
USE IEEE.std_logic_1164.ALL;
ENTITY RegisterPair IS
    generic (
      width : integer);
    port (
      clockin  : in  std_logic;
      clockout : in  std_logic;
      syncresetin : in std_logic;
      asyncresetin : in std_logic;
      syncresetout : in std_logic;
      asyncresetout : in std_logic;
      datain   : in  std_logic_vector(width-1 downto 0);
      dataout  : out std_logic_vector(width-1 downto 0) := (others => '0' );
      enablein : in std_logic;
      enableout : in std_logic
    );
  end entity RegisterPair;

-- This implementation is suitable for simulation but not synthesis
-- It must be replaced by a correctly constrained alternative. See documentation.
architecture Behave of RegisterPair is

    signal crossing : std_logic_vector(width-1 downto 0) := (others => '0' );
    constant zero : std_logic_vector(width-1 downto 0) := (others => '0');

    begin  -- Behave

      process(clockin,asyncresetin)
        begin
        if asyncresetin='1' then
          crossing <= zero;
        elsif rising_edge(clockin) then
          if syncresetin='1' then
            crossing <= zero;
          elsif enablein='1' then
            crossing <= datain;
          end if;
        end if;
      end process;

      process(clockout,asyncresetout)
        begin
        if asyncresetout='1' then
           dataout <= zero;
        elsif rising_edge(clockout) then
           if syncresetout='1' then
              dataout <= zero;
           elsif enableout='1' then
              dataout <= crossing;
           end if;
        end if;
      end process;

    end Behave;



--- Safe startup component ---

LIBRARY IEEE;
USE IEEE.std_logic_1164.ALL;
ENTITY CelStart IS
  GENERIC (inpipelength : integer := 11;
           outpipelength : integer := 4);
  PORT(clk : in std_logic;
       aclr : in std_logic;
       sclr : in std_logic;
       start : out std_logic);
END ENTITY CelStart;

ARCHITECTURE Behave of CelStart IS

  SIGNAL inpipeline : std_logic_vector( inpipelength-1 DOWNTO 0 ) := (OTHERS=>'0');
  SIGNAL outpipeline : std_logic_vector( outpipelength-1 DOWNTO 0 ) := (OTHERS=>'0');
  SIGNAL feedback, joined : std_logic := '0';

  ATTRIBUTE syn_preserve : boolean;
  ATTRIBUTE preserve_signal : boolean;
  ATTRIBUTE preserve_driver : boolean;
  ATTRIBUTE syn_preserve OF inpipeline : SIGNAL IS true;
  ATTRIBUTE preserve_signal OF inpipeline : SIGNAL IS true;
  ATTRIBUTE preserve_driver OF inpipeline : SIGNAL IS true;

BEGIN

  PROCESS (clk, aclr)
  BEGIN
    IF aclr='1' THEN
      inpipeline <= (OTHERS=>'0');
    ELSIF rising_edge(clk) THEN
      IF sclr='1' THEN
        inpipeline <= (OTHERS=>'0');
      ELSE
        FOR i IN 0 TO inpipelength-2 LOOP
          inpipeline(i+1) <= inpipeline(i);
        END LOOP;
        inpipeline(0) <= '1';
      END IF;
    END IF;
  END PROCESS;

  joined <= feedback or inpipeline(inpipelength-1);

  PROCESS (clk, aclr)
  BEGIN
    IF aclr='1' THEN
      feedback <= '0';
    ELSIF rising_edge(clk) THEN
      IF sclr='1' THEN
        feedback <= '0';
      ELSE
        feedback <= joined;
      END IF;
    END IF;
  END PROCESS;

  PROCESS (clk, aclr)
  BEGIN
    IF aclr='1' THEN
      outpipeline <= (OTHERS=>'0');
    ELSIF rising_edge(clk) THEN
      IF sclr='1' THEN
        outpipeline <= (OTHERS=>'0');
      ELSE
        FOR i IN 0 TO outpipelength-2 LOOP
          outpipeline(i+1) <= outpipeline(i);
        END LOOP;
        outpipeline(0) <= (not feedback) and joined;
      END IF;
    END IF;
  END PROCESS;

  start <= outpipeline(outpipelength-1);

END;

--- Clock divider component ----

LIBRARY IEEE;
USE IEEE.std_logic_1164.ALL;
ENTITY clockdiv IS
    -- high1+low+high2 must equal an even number...
    -- high2 can equal zero...
    GENERIC (high1 : integer := 1;
             low   : integer := 1;
             high2 : integer := 0);
    PORT (ckout : out std_logic;
          ckin : in std_logic;
          rst : in std_logic := '0');
END;

ARCHITECTURE behaviour OF clockdiv IS

  -- a common reset is required to ensure the two flip flop chain are synchronised...
  SIGNAL CommonReset_inv: std_logic := '0';
  SIGNAL CommonReset: std_logic;

  -- Used to store the reset values (will be optimised away hopefully)...
  SIGNAL RisingResetChain: std_logic_vector(((high1+low+high2)/2)-1 downto 0);
  SIGNAL FallingResetChain: std_logic_vector(((high1+low+high2)/2)-1 downto 0);

  -- These will become the flip flops...
  SIGNAL RisingChain: std_logic_vector(((high1+low+high2)/2)-1 DOWNTO 0);
  SIGNAL FallingChain: std_logic_vector(((high1+low+high2)/2)-1 DOWNTO 0);

  ATTRIBUTE preserve_driver : boolean;
  ATTRIBUTE preserve_driver OF CommonReset_inv : signal IS true;

BEGIN

  -- If the provided settings describe a divided clock build the required logic...
  DividedClock: IF ( not(high1=1 and low=1 and high2=0) ) GENERATE

    -- Set the clock to the generated signal
    -- The derived clock is generated by the or operations of the first
    --   registers in each shift chain...
    ckout <= RisingChain(0) or FallingChain(((high1+low+high2)/2)-1);

    -- Ensure the two divider chains are synchronised by building a common reset...
    SyncReset: PROCESS (rst, ckin) BEGIN
      IF (rst='1') THEN  -- if the reset signal is active
        CommonReset_inv <= '0';  -- the common reset is active
      ELSIF (rising_edge(ckin)) THEN  -- if the clock source is rising
        CommonReset_inv <= '1';   -- clear the reset
      END IF;
    END PROCESS SyncReset;

    CommonReset <= not(CommonReset_inv);

    -- Build the reset states for the shift registers...
    reset_states: for I in 0 to (high1+low+high2-1) GENERATE

      -- The reset states for the rising edge triggered flip flops,
      -- calculated on even numbers ((I/2)*2)=I will test for an even number...
      RisingEdgeReset: IF ( (I mod 2)=0 ) GENERATE
        HighGenerationRE: IF not( ((high1<=I)or(high1<=(I+1))) and ((high1+low)>I) ) GENERATE
           RisingResetChain(I/2) <= '1';
        END GENERATE HighGenerationRE;
        LowGenerationRE: IF ( ((high1<=I)or(high1<=(I+1))) and ((high1+low)>I) ) GENERATE
           RisingResetChain(I/2) <= '0';
        END GENERATE LowGenerationRE;
      END GENERATE RisingEdgeReset;

      -- the reset states for the falling edge chain,
      -- calculated on odd numbers (((I/2)*2)+1)=I will test for even numbers...
      FallingEdgeReset: IF ( (I mod 2)=1 ) GENERATE
        HighGenerationFE: IF not( ((high1<=I)or(high1<=(I+1))) and ((high1+low)>I) ) GENERATE
          FallingResetChain(I/2) <= '1';
        END GENERATE HighGenerationFE;
        LowGenerationFE: IF ( ((high1<=I)or(high1<=(I+1))) and ((high1+low)>I) ) GENERATE
          FallingResetChain(I/2) <= '0';
        END GENERATE LowGenerationFE;
      END GENERATE FallingEdgeReset;

    END GENERATE reset_states;

    -- Build the rising edge triggered flip flop chain...
    RisingEdgeChain: PROCESS(CommonReset, ckin, RisingResetChain) BEGIN
      IF (CommonReset='1') THEN
        RisingChain <= RisingResetChain;
      ELSIF (ckin'event and ckin='1') THEN
        RisingChain <= RisingChain(0) & RisingChain(RisingChain'LENGTH-1 DOWNTO 1);
      END IF;
    END PROCESS RisingEdgeChain;

    -- Build the falling edge triggered flip flop chain...
    FallingEdgeChain: process(CommonReset, ckin, FallingResetChain) begin
      IF (CommonReset='1') THEN
        FallingChain <= FallingResetChain;
      ELSIF (ckin'event and ckin='0') THEN
        FallingChain <= FallingChain(0) & FallingChain(FallingChain'LENGTH-1 DOWNTO 1);
      END IF;
    END PROCESS FallingEdgeChain;

  END GENERATE DividedClock;

  -- If the clock is not divided build no logic at all...
  UnDividedClock: IF ( high1=1 and low=1 and high2=0 ) GENERATE
    ckout <= ckin;
  END GENERATE UnDividedClock;

END behaviour;


---- Pulse sequence generator component ----

LIBRARY IEEE;
USE IEEE.std_logic_1164.ALL;
USE IEEE.numeric_std.ALL;
ENTITY pulsegen IS
  GENERIC (pulse : integer;
          length : integer);
  PORT (ckout : OUT std_logic;
        ckin   : IN std_logic;
        rst : IN std_logic);
END;

ARCHITECTURE only OF pulsegen IS

  CONSTANT revpulse : std_logic_vector(length-1 DOWNTO 0) := STD_LOGIC_VECTOR(TO_UNSIGNED(pulse, length));

  SIGNAL A : std_logic_vector(revpulse'HIGH/2 DOWNTO 0);
  SIGNAL B : std_logic_vector(revpulse'HIGH/2 DOWNTO 0);
  SIGNAL C : std_logic_vector(revpulse'HIGH/2 DOWNTO 0);
  SIGNAL D : std_logic_vector(revpulse'HIGH/2 DOWNTO 0);

  SIGNAL shiftA : std_logic_vector(A'RANGE);
  SIGNAL shiftB : std_logic_vector(B'RANGE);
  SIGNAL shiftC : std_logic_vector(C'RANGE);
  SIGNAL shiftD : std_logic_vector(D'RANGE);

  SIGNAL resetff, resetff_inv : std_logic;

  ATTRIBUTE preserve_driver : boolean;
  ATTRIBUTE preserve_driver OF resetff_inv : signal IS true;

BEGIN

  test: FOR I IN revpulse'HIGH/4 DOWNTO 0 GENERATE

    A(I*2) <= revpulse(I*4) or revpulse(I*4+1);
    B(I*2) <= revpulse(I*4);
    C(I*2) <= '0';

    test3 : IF I*4+2 <= revpulse'HIGH GENERATE
      D(I*2) <= revpulse(I*4+2);
    END GENERATE test3;

    test4 : IF I*4+2 > revpulse'HIGH GENERATE
      D(I*2) <= '0';
    END GENERATE test4;

    test2 : IF I*2+1 <= A'HIGH GENERATE
      A(I*2+1) <= '0';
      B(I*2+1) <= revpulse(I*4+1);
      C(I*2+1) <= revpulse(I*4+2) or revpulse(I*4+3);
      D(I*2+1) <= revpulse(I*4+3);
    END GENERATE test2;

  END GENERATE test;

  ckout <= (shiftA(shiftA'HIGH) and shiftB(shiftB'LOW)) or (shiftC(shiftC'HIGH) and shiftD(shiftD'HIGH));

  sr1: PROCESS(ckin, resetff)
  BEGIN
    if (resetff = '1') THEN
      shiftA <= A;
      shiftC <= C;
    ELSIF falling_edge(ckin) THEN
      shiftA <= shiftA(shiftA'HIGH-1 downto shiftA'LOW) & shiftA(shiftA'HIGH);
      shiftC <= shiftC(shiftC'HIGH-1 downto shiftC'LOW) & shiftC(shiftC'HIGH);
    END IF;
  END PROCESS;

  sr2: PROCESS(ckin, resetff)
  BEGIN
    IF (resetff = '1') THEN
      shiftB <= B;
      shiftD <= D;
    ELSIF rising_edge(ckin) THEN
      shiftB <= shiftB(shiftB'HIGH-1 downto shiftB'LOW) & shiftB(shiftB'HIGH);
      shiftD <= shiftD(shiftD'HIGH-1 downto shiftD'LOW) & shiftD(shiftD'HIGH);
    END IF;
  END PROCESS;

  start: PROCESS(ckin, rst)
  BEGIN
    IF (rst = '1') THEN
      resetff_inv <= '0';
    ELSIF (falling_edge(ckin)) THEN
      resetff_inv <= '1';
    END IF;
  END PROCESS;

  resetff <= not(resetff_inv);

END only;
