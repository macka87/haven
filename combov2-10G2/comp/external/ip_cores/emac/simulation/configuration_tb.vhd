------------------------------------------------------------------------
-- Title      : Demo testbench
-- Project    : Virtex-5 Ethernet MAC Wrappers
------------------------------------------------------------------------
-- File       : configuration_tb.vhd
------------------------------------------------------------------------
-- Copyright (c) 2004-2008 by Xilinx, Inc. All rights reserved.
-- This text/file contains proprietary, confidential
-- information of Xilinx, Inc., is distributed under license
-- from Xilinx, Inc., and may be used, copied and/or
-- disclosed only pursuant to the terms of a valid license
-- agreement with Xilinx, Inc. Xilinx hereby grants you
-- a license to use this text/file solely for design, simulation,
-- implementation and creation of design files limited
-- to Xilinx devices or technologies. Use with non-Xilinx
-- devices or technologies is expressly prohibited and
-- immediately terminates your license unless covered by
-- a separate agreement.
--
-- Xilinx is providing this design, code, or information
-- "as is" solely for use in developing programs and
-- solutions for Xilinx devices. By providing this design,
-- code, or information as one possible implementation of
-- this feature, application or standard, Xilinx is making no
-- representation that this implementation is free from any
-- claims of infringement. You are responsible for
-- obtaining any rights you may require for your implementation.
-- Xilinx expressly disclaims any warranty whatsoever with
-- respect to the adequacy of the implementation, including
-- but not limited to any warranties or representations that this
-- implementation is free from claims of infringement, implied
-- warranties of merchantability or fitness for a particular
-- purpose.
--
-- Xilinx products are not intended for use in life support
-- appliances, devices, or systems. Use in such applications are
-- expressly prohibited.
--
-- This copyright and support notice must be retained as part
-- of this text at all times. (c) Copyright 2004-2008 Xilinx, Inc.
-- All rights reserved.
------------------------------------------------------------------------
-- Description: Management
--
--              This testbench will exercise the ports of the generic
--              Host Interface to configure the EMAC pair.
------------------------------------------------------------------------


library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;


entity configuration_tb is
    port(
      reset                       : out std_logic;
      ------------------------------------------------------------------
      -- Host Interface
      ------------------------------------------------------------------
      host_clk                    : out std_logic;
      host_opcode                 : out std_logic_vector(1 downto 0);
      host_req                    : out std_logic;
      host_miim_sel               : out std_logic;
      host_addr                   : out std_logic_vector(9 downto 0);
      host_wr_data                : out std_logic_vector(31 downto 0);
      host_miim_rdy               : in  std_logic;
      host_rd_data                : in  std_logic_vector(31 downto 0);
      host_emac1_sel              : out std_logic;

      ------------------------------------------------------------------
      -- Test Bench Semaphores
      ------------------------------------------------------------------

      emac0_configuration_busy    : out boolean;
      emac0_monitor_finished_1g   : in  boolean;
      emac0_monitor_finished_100m : in  boolean;
      emac0_monitor_finished_10m  : in  boolean;

      emac1_configuration_busy    : out boolean;
      emac1_monitor_finished_1g   : in  boolean;
      emac1_monitor_finished_100m : in  boolean;
      emac1_monitor_finished_10m  : in  boolean

      );
end configuration_tb;


architecture behavioral of configuration_tb is


    -----------------------------------------------------------------------------
    -- Register Map Constants
    -----------------------------------------------------------------------------

    -- Management configuration register address (0x340)
    constant config_management_address   : std_logic_vector(8 downto 0) := "101000000";

    -- Flow control configuration register address (0x2C0)
    constant config_flow_control_address : std_logic_vector(8 downto 0) := "011000000";

    -- Receiver configuration register address (0x240)
    constant receiver_address            : std_logic_vector(8 downto 0) := "001000000";

    -- Transmitter configuration register address (0x280)
    constant transmitter_address         : std_logic_vector(8 downto 0) := "010000000";

    -- EMAC configuration register address (0x300)
    constant emac_config_add             : std_logic_vector(8 downto 0) := "100000000";


    ----------------------------------------------------------------------
    -- testbench signals
    ----------------------------------------------------------------------

    signal hostclk      : std_logic;
    signal hostopcode   : std_logic_vector(1 downto 0);
    signal hostreq      : std_logic := '0';
    signal hostmiimsel  : std_logic;
    signal hostaddr     : std_logic_vector(9 downto 0);
    signal hostwrdata   : std_logic_vector(31 downto 0);
    signal hostemac1sel : std_logic;


begin


    ------------------------------------------------------------------
    -- Drive outputs from internal signals
    ------------------------------------------------------------------
    host_clk       <= hostclk;
    host_opcode    <= hostopcode;               
    host_req       <= hostreq;                  
    host_miim_sel  <= hostmiimsel;              
    host_addr      <= hostaddr;                 
    host_wr_data   <= hostwrdata;              
    host_emac1_sel <= hostemac1sel;             


    ----------------------------------------------------------------------------
    -- HOSTCLK driver
    ----------------------------------------------------------------------------

    -- Drive HOSTCLK at one third the frequency of GTX_CLK
    p_hostclk : process
    begin
        hostclk <= '0';
        wait for 2 ns;
        loop
            wait for 12 ns;
            hostclk <= '1';
            wait for 12 ns;
            hostclk <= '0';
        end loop;
    end process P_hostclk;


    ----------------------------------------------------------------------------
    -- Configuration Through the Host Interface
    ----------------------------------------------------------------------------
    emac_configuration : process

        -------------------------------------
        -- EMAC Host Configuration Write Procedure
        -------------------------------------
        procedure config_write (
          address              : in std_logic_vector(8 downto 0);    
          data                 : in std_logic_vector(31 downto 0);    
          emacsel              : in std_logic) is    
        begin  
          hostemac1sel         <= emacsel;
          hostaddr(9)          <= '1';
          hostaddr(8 downto 0) <= address;
          hostmiimsel          <= '0';
          hostopcode           <= "01";
          hostwrdata           <= data;
          wait until hostclk'event and hostclk = '0';
        	
          hostaddr(9)          <= '1';
          hostmiimsel          <= '0';
          hostopcode           <= "11";
          hostwrdata           <= (others => '0');
          wait until hostclk'event and hostclk = '0';
        	
        end config_write;


        -------------------------------------
        -- EMAC Host Configuration Read Procedure
        -------------------------------------
        procedure config_read (
          address              : in std_logic_vector(8 downto 0);    
          emacsel              : in std_logic) is    
        begin  
          hostemac1sel         <= emacsel;
          hostaddr(9)          <= '1';
          hostaddr(8 downto 0) <= address;
          hostmiimsel          <= '0';
          hostopcode           <= "11";
          wait until hostclk'event and hostclk = '0';

        end config_read;

  
        variable data : std_logic_vector(31 downto 0) := (others => '0');


    begin -- emac_configuration

      emac0_configuration_busy <= false;
      emac1_configuration_busy <= false;

      -- Initialise the Host Bus
      hostemac1sel         <= '0';
      hostaddr(9)          <= '1';
      hostaddr(8 downto 0) <= "000000000";
      hostmiimsel          <= '0';
      hostopcode           <= "11";
      hostwrdata           <= (others => '0');
      data                 := (others => '0');

      -- Reset the core
      assert false
      report "Resetting the design..." & cr
      severity note;

      reset <= '1';
      wait for  4000 ns;
      reset <= '0';
      wait for 200 ns;

      assert false
      report "Timing checks are valid" & cr
      severity note;

      emac0_configuration_busy <= true;
      emac1_configuration_busy <= true;


      -- wait for EMAC Host I/F to initialise
      while (host_miim_rdy /= '1') loop
        wait until hostclk'event and hostclk = '0';
      end loop;


      ----------------------------------------------------------------------------
      -- Configuration: initialisation of EMAC0
      ----------------------------------------------------------------------------

        -- Disable Flow Control.  Set top 3 bits of the flow control
        -- configuration register (Address=2C0) to zero therefore disabling tx
        -- and rx flow control.
        --------------------------------------------------------------------------
        assert false
        report "Disabling tx and rx flow control of EMAC0..." & cr 
        severity note;

        -- Read the current config value from the register
        config_read  (config_flow_control_address,
                      '0');

        -- Now turn off the relevant bits and write back into the register
        data := "000" & host_rd_data(28 downto 0);

        config_write (config_flow_control_address,
                      data,
                      '0');


        -- Setting the tx configuration bit to enable the transmitter
        -- and set to full duplex mode.
        -- Write to Transmittter Configuration Register (Address = 0x280).
        --------------------------------------------------------------------------
        assert false
        report "Setting tx configuration of EMAC0..." & cr
        severity note;

        -- Read the current config value from the register
        config_read  (transmitter_address,
                      '0');

        -- Now set the relevant bits and write back into the register
        data := '0' & host_rd_data(30 downto 29) & '1' & host_rd_data(27) & '0' & host_rd_data(25 downto 0);

        config_write (transmitter_address,
                      data,
                      '0');

        -- Setting the rx configuration bit to enable the receiver
        -- and set to full duplex mode.
        -- Write to Receiver Configuration Register (Address = 0x240).
        -------------------------------------------------------------------------
        assert false
        report "Setting rx configuration of EMAC0..." & cr
        severity note;

        -- Read the current config value from the register
        config_read  (receiver_address,
                      '0');

        -- Now set the relevant bits and write back into the register
        data := '0' & host_rd_data(30 downto 29) & '1' & host_rd_data(27) & '0' & host_rd_data(25 downto 0);

        config_write (receiver_address,
                      data,
                      '0');


      ----------------------------------------------------------------------------
      -- Configuration: initialisation of EMAC1
      ----------------------------------------------------------------------------

        -- Disable Flow Control.  Set top 3 bits of the flow control
        -- configuration register (Address=2C0) to zero therefore disabling tx
        -- and rx flow control.
        --------------------------------------------------------------------------
        assert false
        report "Disabling tx and rx flow control of EMAC1..." & cr 
        severity note;

        -- Read the current config value from the register
        config_read  (config_flow_control_address,
                      '1');

        -- Now turn off the relevant bits and write back into the register
        data := "000" & host_rd_data(28 downto 0);

        config_write (config_flow_control_address,
                      data,
                      '1');


        -- Setting the tx configuration bit to enable the transmitter
        -- and set to full duplex mode.
        -- Write to Transmittter Configuration Register (Address = 0x280).
        --------------------------------------------------------------------------
        assert false
        report "Setting tx configuration of EMAC1..." & cr
        severity note;

        -- Read the current config value from the register
        config_read  (transmitter_address,
                      '1');

        -- Now set the relevant bits and write back into the register
        data := '0' & host_rd_data(30 downto 29) & '1' & host_rd_data(27) & '0' & host_rd_data(25 downto 0);

        config_write (transmitter_address,
                      data,
                      '1');

        -- Setting the rx configuration bit to enable the receiver
        -- and set to full duplex mode.
        -- Write to Receiver Configuration Register (Address = 0x240).
        -------------------------------------------------------------------------
        assert false
        report "Setting rx configuration of EMAC1..." & cr
        severity note;

        -- Read the current config value from the register
        config_read  (receiver_address,
                      '1');

        -- Now set the relevant bits and write back into the register
        data := '0' & host_rd_data(30 downto 29) & '1' & host_rd_data(27) & '0' & host_rd_data(25 downto 0);

        config_write (receiver_address,
                      data,
                      '1');


      ----------------------------------------------------------------------------
      -- Setting the speed of EMAC0 to 1Gb/s.
      ----------------------------------------------------------------------------
      -- Write to EMAC Configuration Register (Address = 0x300).
      assert false
      report "Setting speed of EMAC0 to 1Gb/s..." & cr
      severity note;

      -- Read the current config value from the register
      config_read  (emac_config_add,
                    '0');

      -- Now set the relevant bits and write back into the register
      data := "10" & host_rd_data(29 downto 0);

      config_write (emac_config_add,
                    data,
                    '0');

      emac0_configuration_busy <= false;


      ----------------------------------------------------------------------------
      -- Setting the speed of EMAC1 to 1Gb/s.
      ----------------------------------------------------------------------------
      -- Write to EMAC Configuration Register (Address = 0x300).
      assert false
      report "Setting speed of EMAC1 to 1Gb/s..." & cr
      severity note;

      -- Read the current config value from the register
      config_read  (emac_config_add,
                    '1');

      -- Now set the relevant bits and write back into the register
      data := "10" & host_rd_data(29 downto 0);

      config_write (emac_config_add,
                    data,
                    '1');

      emac1_configuration_busy <= false;


      -- wait for EMAC0 1Gb/s frames to complete
      while (not emac0_monitor_finished_1g) loop
         wait for 8 ns;
      end loop;		   


      -- wait for EMAC1 1Gb/s frames to complete
      while (not emac1_monitor_finished_1g) loop
         wait for 8 ns;
      end loop;		   


      emac0_configuration_busy <= true;

      ----------------------------------------------------------------------------
      -- Setting the speed of EMAC0 to 100Mb/s.
      ----------------------------------------------------------------------------
      -- Write to EMAC Configuration Register (Address = 0x300).
      assert false
      report "Setting speed of EMAC0 to 100Mb/s..." & cr
      severity note;

      -- Read the current config value from the register
      config_read  (emac_config_add,
                    '0');

      -- Now set the relevant bits and write back into the register
      data := "01" & host_rd_data(29 downto 0);

      config_write (emac_config_add,
                    data,
                    '0');

      emac0_configuration_busy <= false;


      emac1_configuration_busy <= true;

      ----------------------------------------------------------------------------
      -- Setting the speed of EMAC1 to 100Mb/s.
      ----------------------------------------------------------------------------
      -- Write to EMAC Configuration Register (Address = 0x300).
      assert false
      report "Setting speed of EMAC1 to 100Mb/s..." & cr
      severity note;

      -- Read the current config value from the register
      config_read  (emac_config_add,
                    '1');

      -- Now set the relevant bits and write back into the register
      data := "01" & host_rd_data(29 downto 0);

      config_write (emac_config_add,
                    data,
                    '1');

      emac1_configuration_busy <= false;


      -- wait for EMAC0 100Mb/s frames to complete
      while (not emac0_monitor_finished_100m) loop
         wait for 80 ns;
      end loop;		   


      -- wait for EMAC1 100Mb/s frames to complete
      while (not emac1_monitor_finished_100m) loop
         wait for 80 ns;
      end loop;		   


      emac0_configuration_busy <= true;
      ----------------------------------------------------------------------------
      -- Setting the speed of EMAC0 to 10Mb/s.
      ----------------------------------------------------------------------------
      -- Write to EMAC Configuration Register (Address = 0x300).
      assert false
      report "Setting speed of EMAC0 to 10Mb/s..." & cr
      severity note;

      -- Read the current config value from the register
      config_read  (emac_config_add,
                    '0');

      -- Now set the relevant bits and write back into the register
      data := "00" & host_rd_data(29 downto 0);

      config_write (emac_config_add,
                    data,
                    '0');

      emac0_configuration_busy <= false;


      emac1_configuration_busy <= true;
      ----------------------------------------------------------------------------
      -- Setting the speed of EMAC1 to 10Mb/s.
      ----------------------------------------------------------------------------
      -- Write to EMAC Configuration Register (Address = 0x300).
      assert false
      report "Setting speed of EMAC1 to 10Mb/s..." & cr
      severity note;

      -- Read the current config value from the register
      config_read  (emac_config_add,
                    '1');

      -- Now set the relevant bits and write back into the register
      data := "00" & host_rd_data(29 downto 0);

      config_write (emac_config_add,
                    data,
                    '1');
      emac1_configuration_busy <= false;



      -- wait for EMAC0 10Mb/s frames to complete
      while (not emac0_monitor_finished_10m) loop
         wait for 800 ns;
      end loop;		   


      -- wait for EMAC1 10Mb/s frames to complete
      while (not emac1_monitor_finished_10m) loop
         wait for 800 ns;
      end loop;		   


      wait for 100 ns;

      -- Our work here is done
        assert false
      report "Simulation stopped"
      severity failure;

    end process emac_configuration;



    -----------------------------------------------------------------------------
    -- If the simulation is still going after 2 ms 
    -- then something has gone wrong
    -----------------------------------------------------------------------------
    p_timebomb : process
    begin
      wait for 2 ms;
    	assert false
    	report "** ERROR - Simulation running forever!"
    	severity failure;
    end process p_timebomb;



end behavioral;

