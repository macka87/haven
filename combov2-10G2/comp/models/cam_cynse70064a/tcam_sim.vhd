--
-- tcam_sim.vhd: CYNSE70064A(CAM) simulation model
-- Copyright (C) 2004 CESNET
-- Author(s): Malek Tomas     <tomalek@liberouter.org>
--            Belohlavek Jiri <belohlavek@liberouter.org>
--            
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
-- $ID: $
--
-- TODO:
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity TCAM_SIM is

   generic (
      cam_mask    : string;
      cam_data    : string;
      cam_clk_per : time
   );

   port(
      -- Clocks and Reset
      CMCLK  : in std_logic; -- Master Clock
      CPHASE : in std_logic; -- Phase
      CRST   : in std_logic; -- Reset

      -- CMD and DQ bus
      COP  : in std_logic_vector(8 downto 0);     -- CMD Bus
      COPV : in std_logic;                        -- CMD Valid
      CD   : inout std_logic_vector(67 downto 0); -- Address/Data Bus

      CACK : inout std_logic; -- Read Acknowledge
      CEOT : inout std_logic; -- End of Transfer
      CMF  : inout std_logic; -- Search Successful Flag
      CMV  : inout std_logic; -- Search Successful Plag Valid

      -- SRAM Interface
      CAD  : inout std_logic_vector(21 downto 0); -- SRAM Address
      CCE  : inout std_logic; -- SRAM Chip Enable
      CWE  : inout std_logic; -- SRAM Write Enable
      COE  : inout std_logic; -- SRAM Output Enable
      CALE : inout std_logic; -- Address Latch Enable

      -- only for backward compability
      CSEN  : in  std_logic_vector(3 downto 0); -- CAM search enable
      CMM   : out std_logic; -- CAM multi match flag
      CFF   : out std_logic -- CAM full flag
   );
end entity TCAM_SIM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture CYNSE70064A_arch of TCAM_SIM is
   -- don't use, always "0000"
   signal mID : std_logic_vector(4 downto 0); -- Device Identification
   signal FULO : std_logic; -- ='1' cam is full, learn doesn't work
   -- aliases new_name is existing_name_of_same_type --------------------------
   -- names from new manual, used in code (aliases)

   -- Clocks and Reset
   alias CLK2X is CMCLK;  -- Master Clock
   alias PHS_L is CPHASE; -- Phase
   alias RST_L is CRST;   -- Reset

   -- CMD and DQ bus
   alias CMD  is COP;  -- CMD Bus
   alias CMDV is COPV; -- CMD Valid
   alias DQ   is CD;   -- Address/Data Bus

   alias ACK  is CACK; -- Read Acknowledge
--    alias cEOT is CEOT; -- End of Transfer
   alias SSF  is CMF;  -- Search Successful Flag
   alias SSV  is CMV;  -- Search Successful Plag Valid

   -- SRAM Interface
   alias SADR  is CAD;  -- SRAM Address
   alias CE_L  is CCE;  -- SRAM Chip Enable
   alias WE_L  is CWE;  -- SRAM Write Enable
   alias OE_L  is COE;  -- SRAM Output Enable
   alias ALE_L is CALE; -- Address Latch Enable

   -- costants ----------------------------------------------------------------
   constant NSE_clkper    : time   := cam_clk_per;
   constant NSE_DATA_FILE : string := cam_data;
   constant NSE_MASK_FILE : string := cam_mask;

   -- internal clock ----------------------------------------------------------
   -- NSE uses the PHS_L signal to divide CLK2X and generate an internal CLK.
   signal CLK : std_logic;

   -- All register in the CYNSE70064A are 68 bits wide.
   constant REGISTER_WIDE : natural := 68;
   subtype NSE_register is std_logic_vector(REGISTER_WIDE-1 downto 0);
   ----------------------------------------------------------------------------


   -- Comparand Registers: 16 pairs of comparand registers that store ---------
   --                      comparands form the DQ bus for learning later
   type type_Comparand_Registers is array (31 downto 0) of NSE_register;
   signal COMP0_31 : type_Comparand_Registers; -- address 0-31, mode read
   ----------------------------------------------------------------------------


   -- Mask Registers: 8 pairs of global mask register -------------------------
   type type_Global_Mask_Registers is array (15 downto 0) of NSE_register;
   signal MASKS : type_Global_Mask_Registers; -- address 32-47, mode read-write
   ----------------------------------------------------------------------------


   -- Search Successful Registers: 8 search successful index registers --------
   type structure_SSR is record
      INDEX : std_logic_vector(14 downto 0);  -- address of the 68-bit entry
      r_1   : std_logic_vector(30 downto 15); -- reserved
      VALID : std_logic;                      -- global winner sets '1'
      r_2   : std_logic_vector(67 downto 32); -- reserved
   end record;

   type type_Search_Successful_Registers is array (7 downto 0) of structure_SSR;
   signal SSR0_7 : type_Search_Successful_Registers; -- address 48-55, mode read
   -- Initial value of Index is 'X', others is '0'
   ----------------------------------------------------------------------------


   -- Command Register --------------------------------------------------------
  type structure_Command_Register is record
      SRST : std_logic;                      -- Software Reset
      DEVE : std_logic;                      -- Device Enable
      TLSZ : std_logic_vector(3 downto 2);   -- Table Size
      HLAT : std_logic_vector(6 downto 4);   -- Latency of Hit Signals
      LDEV : std_logic;                      -- Last Device in the Cascade
      LRAM : std_logic;                      -- Last Device on the SRAM Bus
      CFG  : std_logic_vector(16 downto 9);  -- Database Configuration
      r_1  : std_logic_vector(67 downto 17); -- reserved
   end record;

   signal COMMAND : structure_Command_Register; -- address 56, mode read-write
   -- Initial value of TLSZ is '01', others is '0'
   ----------------------------------------------------------------------------


   -- Information Register ----------------------------------------------------
   type structure_Information_Register is record
      Revision       : std_logic_vector(3 downto 0);   -- Revision Number
      Implementation : std_logic_vector(6 downto 4);   -- this is the CYNSE70064A
                                                       -- implementation number
      r_1            : std_logic;                      --
      Device_ID_1    : std_logic_vector(11 downto 8);  -- this is the device
                                                       -- identification number
      Device_ID_2    : std_logic;                      -- reserved
      Device_ID_3    : std_logic_vector(15 downto 13); -- these are the three MSBs
                                                       -- of the device mID
      MFID           : std_logic_vector(31 downto 16); -- Manufacturer mID
      r_2            : std_logic_vector(67 downto 32); -- reserved
   end record;

   signal INFO : structure_Information_Register; -- address 57, mode read
   ----------------------------------------------------------------------------


   -- Burst Registers Description ---------------------------------------------
   type structure_Burst_Register is record
      ADR  : std_logic_vector(14 downto 0); -- Address
      r_1  : std_logic_vector(18 downto 15); -- reserved
      BLEN : std_logic_vector(27 downto 19); -- Length of Burst Access
      r_2  : std_logic_vector(67 downto 28); -- reserved
   end record;

   -- Read Burst Register, address 58, mode read-write
   signal RBURREG  : structure_Burst_Register;

   -- Write Burst Register,  address 59, mode read-write
   signal WBURREG : structure_Burst_Register;
   ----------------------------------------------------------------------------


   -- NFA Register ------------------------------------------------------------
   type structure_NFA_Register is record
      -- address of 1. 68-bit location that contains a 0 in the entry s bit[0]
      INDEX : std_logic_vector(14 downto 0); -- address
      r_1   : std_logic_vector(67 downto 15); -- reserved
   end record;

   signal NFA : structure_NFA_Register; -- address 60, mode read
   ----------------------------------------------------------------------------


   -- register 61-63 reserved -------------------------------------------------
   type type_Reserved_Registers is array (2 downto 0) of NSE_register;
   signal Reserved_Registers : type_Reserved_Registers;
   ----------------------------------------------------------------------------


   -- 64 registers mapping ----------------------------------------------------
   --   type type_Registers is array (63 downto 0) of NSE_register;
   --   signal Registers : type_Registers;
   ----------------------------------------------------------------------------


   -- definition of memory types ----------------------------------------------
   constant NSE_MEM_SIZE  : natural := 20;--8*1024; -- depended of mode 272,136,68 !!!
   constant MODE : natural := 272;
   subtype type_cam_word is std_logic_vector(MODE - 1 downto 0);
   type type_cam_memory is array (NSE_MEM_SIZE - 1 downto 0) of type_cam_word;

   -- Variable memory
   shared variable data, mask : type_cam_memory;

   -- for record conversions
   signal mask_aux_signal, aux_signal : std_logic_vector(67 downto 0);

   -- for storage old address during write operation
   signal address_DQ : std_logic_vector(67 downto 0);
   ----------------------------------------------------------------------------

   -- variables for latency of ssf and ssv ------------------------------------
   signal ssv_aux, ssf_aux, ssv_out, ssf_out : std_logic;
   signal ssv_buffer, ssf_buffer : std_logic_vector(7 downto 0);
   
   ----------------------------------------------------------------------------

   -- latency of sram (similar to search ssv and ssf)
   type sram_buffer_t is array(7 downto 0) of std_logic_vector(21 downto 0);

   -- search
   signal sram_aux_s, sram_out_s : std_logic_vector(21 downto 0);
   signal sram_buffer_s : sram_buffer_t;

   signal alel_aux, alel_out : std_logic;
   signal alel_buffer : std_logic_vector(7 downto 0);
   
   -- learn
   signal sram_aux, sram_out : std_logic_vector(21 downto 0);
   signal sram_buffer : sram_buffer_t;

   signal oel_aux, oel_out : std_logic;
   signal oel_buffer : std_logic_vector(7 downto 0);
   
   signal wel_aux, wel_out : std_logic;
   signal wel_buffer : std_logic_vector(7 downto 0);
   
   signal cel_aux, cel_out : std_logic;
   signal cel_buffer : std_logic_vector(7 downto 0);
   -- end learn aux. variables and signals definition ----------------------


begin
 -- All signals are driven out of the device on the
 -- rising edge of CLK2X (when PHS_L is LOW).
 signals_drive: process --***************************************************

  procedure cam_reset is --**************************************************

   -- Initiation files
   file inp_data, inp_mask : text;

   -- Auxiliary variables
   variable i : natural;

   -- Fill data/masks from file -----------------------------------------------
   procedure FILL (file f: text; extern_name: in string;
                   variable cam_memory : inout type_cam_memory) is

      -- Auxiliary variables
      variable L : line;
      variable i : natural := 0;
      variable lwrd : type_cam_word;
      variable good : boolean;
      variable status : file_open_status;

      type type_read_status is (read, write, free_line, FMerror);
      variable read_status : type_read_status := read;

      variable flag_last_line : boolean := false;

   begin
      file_open(status, f, extern_name, READ_MODE);

      file_open_status: case status is

         when open_ok      => report "open file was succeful"
                              severity NOTE;

         when status_error => report "file previously open" &
                                     "and associated with a physical file"
                              severity ERROR;

         when name_error   => report "file does not exist"
                              severity ERROR;

         when mode_error   => report "file cannot be opened in the read mode"
                              severity ERROR;

         when others       => report "unknown error"
                              severity ERROR;

      end case file_open_status;

      read_from_file: while not (endfile(f)) loop

         case read_status is

            when read      => readline(f, L); -- assci to L

                              if (L'Length = 0) then
                                 read_status := free_line;
                              else

                                hread(L, lwrd, good); -- assci L to hexa wrd
                                assert good
                                report "Text I/O read error"
                                severity ERROR;

                                read_status := write;
                              end if;

            when write     => cam_memory(i) := lwrd;
                              i := (i+1);

                              exit when i = NSE_MEM_SIZE;

                              if (flag_last_line) then
                                 read_status := write;
                              else
                                 read_status := read;
                              end if;

            when free_line => flag_last_line := true;
                              read_status := read;

            when FMerror   => report "illegal file format"
                              severity WARNING;

            when others    => report "finite state machine error"
                              severity WARNING;

         end case;

      end loop read_from_file;

      file_close(f);

   end FILL;
   -- end FILL function -------------------------------------------------------

   begin
      mID <= "00000"; -- device identification
      FULO <= '0'; -- CAM is empty
      NFA.INDEX <= (others => '0'); -- next free address register
      -- initialization of registers ------------------------------------------
      SSRs_init: for i in 7 downto 0 loop
         SSR0_7(i).INDEX <= (others => 'X');
         SSR0_7(i).r_1   <= (others => '0');
         SSR0_7(i).VALID <= '0';
         SSR0_7(i).r_2   <= (others => '0');
      end loop SSRs_init;

      COMMAND.SRST <= '0';
      COMMAND.DEVE <= '0';
      COMMAND.TLSZ <= "00";--"01";
      COMMAND.HLAT <= "001";--"000";
      COMMAND.LDEV <= '1'; -- '0'
      COMMAND.LRAM <= '1';
      COMMAND.CFG  <= "10101010"; -- 272b, (others => '0')= mode 32K - 68b
      COMMAND.r_1  <= (others => '0');

      INFO.Revision       <= "0000";
      INFO.Implementation <= "000";    -- or "001"
      INFO.r_1            <= '0';
      INFO.Device_ID_1    <= "0001";   -- or '0010'
      INFO.Device_ID_2    <= '0';      -- or '1'
      INFO.Device_ID_3    <= "000";
      INFO.MFID           <= "1101110001111111";
      INFO.r_2            <= (others => '0');

      RBURREG.ADR  <= (others => '0');  WBURREG.ADR  <= (others => '0');
      RBURREG.r_1  <= (others => '0');  WBURREG.r_1  <= (others => '0');
      RBURREG.BLEN <= (others => '0');  WBURREG.BLEN <= (others => '0');
      RBURREG.r_2  <= (others => '0');  WBURREG.r_2  <= (others => '0');

      -- it is not in datasheet, but it is logical
--       MASKS_init: for i in 15 downto 0 loop
--          MASKS(i) <= (others => '1');
--       end loop MASKS_init;

      MASKS <= (others => (others => '1'));

      -- end initialization of registers --------------------------------------

      -- inicialization of interface
      DQ  <= (others => 'Z');
      ACK <= 'Z';
      cEOT <= 'Z';

      -- Device Enable. If 0, it keeps the SRAM bus (SADR, WE_L, CE_L, OE_L,
      -- and ALE_L), SSF, and SSV signals in three-state condition and forces
      -- the cascade interface output signals LHO[1:0] and BHO[2:0] to 0.
      -- It also keeps the DQ bus in input mode. The purpose of this bit
      -- is to make sure that there are no bus contentions when the
      -- devices power up in the system.

      -- SSF_aux <= 'Z';
      -- SSV_aux <= 'Z';
      --SRAM_aux  <= (others => 'Z');

      -- SRAM Interface
      SADR <= (others => 'Z'); -- SRAM Address
      CE_L <= 'Z'; -- SRAM Chip Enable
      WE_L <= 'Z'; -- SRAM Write Enable
      OE_L <= 'Z'; -- SRAM Output Enable
      ALE_L <= 'Z'; -- Address Latch Enable

      -- Fill NSE - implicit values
--      memory_init: for i in 0 to (NSE_MEM_SIZE - 1) loop
--         data(i) := (others => '0');
--         mask(i) := (others => '1');
--      end loop memory_init;
      
      data := (others => (others => '0'));
      mask := (others => (others => '1'));
      

      -- Fill data from file
      FILL(inp_data, NSE_DATA_FILE, data);
      FILL(inp_mask, NSE_MASK_FILE, mask);

      -- aux. signals of latency
      ssv_aux <= '0';
      ssf_aux <= '0';
--       ssv_out <= '0';
--       ssf_out <= '0';
--       ssv_buffer <= (others => '0');
--       ssf_buffer <= (others => '0');

      if (COMMAND.SRST = '1') then -- software reset

        -- Internally, it generates a reset pulse lasting for eight CLK cycles.
        SW_reset: for i in 0 to 7 loop
           wait until CLK='1';
        end loop SW_reset;

        -- This bit automatically resets to a 0 after the reset has completed.
        COMMAND.SRST <= '0';
      end if;

   end cam_reset;
   -- end procedure cam reset -------------------------------------------------

   -- mapping regisrers to virtual array(63 downto 0) of NSE_register ---------
   procedure registers_mapping (variable address : natural;
                                signal aux: inout NSE_register; read : boolean) is
   begin
      if (address >=  0) AND (address <= 31) AND read then -- R
         aux <= COMP0_31(address);

      elsif (address >= 32) AND (address <= 47) then -- RW
          if read then aux <= MASKS(address-32);
          else MASKS(address-32) <= aux;
          end if;

      elsif (address >= 48) AND (address <= 55) AND read then -- R
         aux <= SSR0_7(address-48).r_2 & SSR0_7(address-48).VALID &
                SSR0_7(address-48).r_1 & SSR0_7(address-48).INDEX;
      else
       mapping: case address is
         when 56 =>
            if read then -- RW
               aux <= COMMAND.r_1 & COMMAND.CFG & COMMAND.LRAM & COMMAND.LDEV &
                      COMMAND.HLAT &COMMAND.TLSZ & COMMAND.DEVE & COMMAND.SRST;
            else
               COMMAND <= (aux(0), aux(1), aux(3 downto 2), aux(6 downto 4),
                           aux(7), aux(8), aux(16 downto 9), aux(67 downto 17));
             end if;

         when 57 =>
            if read then -- R
               aux <= INFO.r_2 & INFO.MFID & INFO.Device_ID_3 &
                      INFO.Device_ID_2 & INFO.Device_ID_1 & INFO.r_1 &
                      INFO.Implementation & INFO.Revision;
           end if;

         when 58 =>
            if read then -- RW
               aux <= RBURREG.r_2  & RBURREG.BLEN & RBURREG.r_1 & RBURREG.ADR;
            else
               RBURREG <= (aux(14 downto 0), aux(18 downto 15),
                           aux(27 downto 19), aux(67 downto 28));
            end if;

         when 59 =>
            if read then -- RW
               aux <= WBURREG.r_2  & WBURREG.BLEN & WBURREG.r_1 & WBURREG.ADR;
            else
               WBURREG <= (aux(14 downto 0), aux(18 downto 15),
                           aux(27 downto 19), aux(67 downto 28));
            end if;

         when 60 =>
            if read then aux <= NFA.r_1 & NFA.INDEX; end if;

         when 61 | 62 | 63 =>
            report " illegal access to reserved registers"
            severity ERROR;
            aux <= Reserved_Registers(address-61);

         when others =>
            report "address out of range <0..63>"
            severity ERROR;
            aux <= (others => '0');

       end case mapping;
      end if;
   end registers_mapping;
   -- end function register_mappinng ------------------------------------------

   -- auxiliary procedure for assert ------------------------------------------
   procedure CMD10_CMDV (constant cycle:string;CMDV:in std_logic; -- CMD Valid
                         CMD : in std_logic_vector(8 downto 0)) is -- CMD Bus
   begin

      assert CMD(1 downto 0) = "10"
      report cycle & " The CMD[1:0] signal must be driven to logic '10'."
      severity WARNING;

      assert CMDV = '1'
      report cycle & " The CMDV signal must be driven to logic 1."
      severity WARNING;

   end CMD10_CMDV;

  -- auxiliary procedure for check the next free address in cam----------------
  -- it is looking for next free line in cam, if it reach the top, FULO <= '1'
   procedure check_NFA is
   begin
      if FULO = '0' then -- '1' cam is full
         while data(conv_integer(NFA.INDEX))(0) = '1' loop -- in 68b conf. Bit[0]=1 empty
            NFA.INDEX<=NFA.INDEX+'1';
            wait for 1 ps;
            if NFA.INDEX = (NSE_MEM_SIZE-1) then -- all data banks were used
              FULO <= '1'; -- cam is full
              report "Cam is full, Learn is not correct operation"
              severity ERROR;
              exit; -- end of while cycle
            end if;
         end loop;
      end if;
   end check_NFA;
   -- end procedure CMD10_CMDV ------------------------------------------------

      variable aux_a : std_logic_vector(67 downto 0); -- for configuration 272b
      --alias address_alias : std_logic_vector(67 downto 0) is aux_a(67 downto 0);

      variable row : natural; -- row in array of cam words (data/mask)

      variable number : integer range 0 to 63; -- number of register [63:0]

      -- variables for masking during searching
      variable wrd, mask_wrd, gmask_wrd, cam_wrd : std_logic_vector(271 downto 0);

      variable i : natural; -- iterator
      variable search : natural; -- iterator

      -- variables for indexing during searching
      variable GMR_pair_A, GMR_pair_C, store_address : integer range 0 to 7;

      -- Command bits 8, and 7 {CMD[8:7]} are passed from the command
      -- to the SRAM address bus. (search)
      variable CMD87 : std_logic_vector(8 downto 7);
      
      variable data_flag : boolean;

      -- variable for learn instruction ---------------------------------------
      variable cmd5_2_a : std_logic_vector(5 downto 2);
      variable cmd5_2_b : std_logic_vector(5 downto 2);     
      variable sadr21_20 : std_logic_vector(8 downto 7);
      
      
   begin
      -- Control database configuration => CFG
      -- Database Configuration. The device is divided internally into four
      -- partitions of 8K × 68, each of which can be configured as 8K × 68,
      -- 4K × 136, or 2K × 272, as follows.
      --    00: 8K × 68
      --    01: 4K × 136
      --    10: 2K × 272
      --    11: Reserved
-- Bits [10:9] apply to configuring the first partition in the address space.
-- Bits [12:11] apply to configuring the second partition in the address space.
-- Bits [14:13] apply to configuring the third partition in the address space.
-- Bits [16:15] apply to configuring the fourth partition in the address space.

      control_CFG: case COMMAND.CFG is
         when "00000000"   =>
            report "Configuration 4x00: 4x8K × 68 not supported"
            severity WARNING;

         when "01010101"   =>
            report "Configuration 4x01: 4x4K × 136 not supported"
            severity WARNING;

         --when "10101010"   =>
         --   report "Configuration 4x10: 4x2K × 272 supported"
         --   severity NOTE;

         when "11111111"   =>
            report "Bad configuration, this bits position are reserved!"
            severity ERROR;

         when others =>
         --   report "You should reset TCAM." &
         --          "Multiwidth Database Configurations not supported!"
         --   severity WARNING;

      end case control_CFG;

      wait until ((CLK2X'event AND CLK2X = '1') AND (PHS_L = '1')) OR (RST_L = '0');
    --  wait until (CLK = '1' OR RST_L = '0');

     -- wait until (CLK2X'event AND CLK2X = '1' AND PHS_L = '0');
      -- inicialization of interface
      DQ  <= (others => 'Z');
      ACK <= 'Z';
      --cEOT <= 'Z';

      assert COMMAND.TLSZ /= "01" or COMMAND.TLSZ /= "10"
      report "TLSZ should by '00' for Max Table Size 8K x 272 bits" &
             "Latency in this case are 4 CLK cycles => single device"
      severity WARNING;

      if COMMAND.DEVE = '0' then -- SRAM device enable
        -- SRAM Interface
        SADR <= (others => 'Z'); -- SRAM Address
        CE_L <= 'Z'; -- SRAM Chip Enable
        WE_L <= 'Z'; -- SRAM Write Enable
        OE_L <= 'Z'; -- SRAM Output Enable
        ALE_L <= 'Z'; -- Address Latch Enable

        SSF_aux <= 'Z'; -- Search Succesful Flag
        SSV_aux <= 'Z'; -- Search Sucesful Flag Valid     
      else
        -- SRAM Interface
        SADR <= (others => 'Z'); -- SRAM Address
        CE_L <= '1'; -- SRAM Chip Enable
        WE_L <= '1'; -- SRAM Write Enable
        OE_L <= '0'; -- SRAM Output Enable
--        ALE_L <= '1'; -- Address Latch Enable
      end if;

        SRAM_aux <= (others => 'Z');
        SSF_aux <= '0'; -- Search Succesful Flag
        SSV_aux <= '0'; -- Search Sucesful Flag Valid

        CEL_aux <= '1'; -- SRAM Chip Enable
        ALEL_aux <= '0'; -- Address Latch Enable
        
        WEL_aux <= '1'; -- SRAM Write Enable
        OEL_aux <= '0'; -- SRAM Output Enable

      -- HW Reset. Driving RST_L LOW (asynchronous)
      -- SW Reset. Driving COMMAND.SRST HIGHT (synchronous)
      -- =>  initializes the device to a known state

      if (COMMAND.SRST = '1') OR (RST_L = '0') then
        cam_reset; -- procedure calling
      else
        if (CMDV='1') then  -- This signal qualifies the CMD bus: 0/1=no/command
         operation: case CMD(2 downto 0) is -- only for 272b configuration

            when "000"  => -- single read -------------------------------------

               -- ASIC selects the NSE for which mID matches the DQ lines.
               --assert(DQ(25 downto 21) = mID)
               --report "bad device indentification"
               --severity WARNING;

               --assert(CMD(5 downto 3) = "000")
               --report "bad command parameters"
               --severity WARNING;

               -- If DQ[29] is 0, this field carries the address
               -- of the data array location.
               if (DQ(29) = '0') then --direct

                  row := conv_integer(DQ(14 downto 0));

                  -- If DQ[29] is 1, the SSRI specified on DQ[28:26] is used
                  -- to generate the address of the data array location:
                  -- {SSR[14:2], SSR[1] | DQ[1], SSR[0] | DQ[0]}.

               else -- indirect
                  number := conv_integer(DQ(28 downto 26)); -- SSRI applicable
                  row := conv_integer(SSR0_7(number).INDEX(14 downto 0) or DQ(1 downto 0));
               end if;

               -- Cycle 1: indexing of NSE memory
               source_read: case DQ(20 downto 19) is

                  when "00"   => -- data array
                     aux_a := data(row)(67 downto 0);

                  when "01"   => -- mask array
                     aux_a := mask(row)(67 downto 0);

                  when "10"   => -- external SRAM
                     report "read from external SRAM do not support"
                     severity NOTE;

                  when "11"   => -- internal registers
                     number := conv_integer(DQ(5 downto 0));
                     registers_mapping(number, aux_signal, true); -- true=read
                     wait for 1 ps;
                     aux_a := aux_signal;
                  when others =>
                     report "error: DQ[20:19]=XX"
                     severity WARNING;

               end case source_read;

--TO DO cycles A B + assert for B => CMD[876]=000
               wait until CLK='1';

               -- Cycle 2: The host ASIC floats DQ to three-state-condition.
               wait until CLK='1';

               -- Cycle 3: The host ASIC keeps DQ[67:0] in 3-state condition.
               -- wait until CLK='1';
               wait until CLK='1';
               wait until CLK2X'event AND CLK2X='0'AND PHS_L='1';
               
               -- Cycle 4: The selected device starts to drive the DQ[67:0]
               -- bus, and drives the ACK signal from Z to LOW.
               ACK <= '0';
               DQ  <= (others => '1');
               --wait until CLK='1';
               wait until CLK2X'event AND CLK2X='0'AND PHS_L='1';

               -- Cycle 5: The selected device drives the Read data from the
               -- addr. location on the DQ bus, and drives the ACK signal HIGH.
               ACK <= '1';
               DQ  <= aux_a;
               --wait until CLK='1';
               wait until CLK2X'event AND CLK2X='0'AND PHS_L='1';

               -- Cycle 6: The selected device floats the DQ[67:0] to 3-state
               -- condition and drives the ACK signal LOW.
               ACK <= '0';
               DQ  <= (others => 'Z');
               wait until CLK='1';

               -- At the termination of cycle 6, the selected device releases
               -- the ACK line to three-state condition. The Read instruction
               -- is complete, and a new operation can begin.
               ACK <= 'Z';

            -- end single read ------------------------------------------------


            when "100"  => -- burst read --------------------------------------

               --assert(CMD(5 downto 3) = "000")
               --report "bad command parameters"
               --severity WARNING;

               -- If DQ[29] is 0, this field carries the address
               -- of the data array location.
               if (DQ(29) = '0') then --direct

                  row := conv_integer(RBURREG.ADR);

                  -- If DQ[29] is 1, the SSRI specified on DQ[28:26] is used
                  -- to generate the address of the data array location:
                  -- {SSR[14:2], SSR[1] | DQ[1], SSR[0] | DQ[0]}.

               else -- indirect
                  number := conv_integer(DQ(28 downto 26)); -- SSRI applicable
                  row := conv_integer(SSR0_7(number).INDEX(14 downto 0) or DQ(1 downto 0));
               end if;

              -- Cycle 1: indexing of NSE memory
               source_read1: case DQ(20 downto 19) is

                  when "00"   => -- data array
                     aux_a := data(row)(67 downto 0);
                     data_flag := true;

                  when "01"   => -- mask array
                     aux_a := mask(row)(67 downto 0);
                     data_flag := false;

                  when "10"   => -- external SRAM
                     report "read from external SRAM do not support"
                     severity NOTE;
 
                  when others =>
                     report "error: DQ[20:19]=XX"
                     severity WARNING;

               end case source_read1;

--TO DO cycles A B + assert for B => CMD[876]=000
               wait until CLK='1';

               -- Cycle 2: The host ASIC floats DQ to three-state-condition.
               wait until CLK='1';

               -- Cycle 3: The host ASIC keeps DQ[67:0] in 3-state condition.
               wait until CLK='1';
               wait for cam_clk_per/4; 

               -- Cycles 4 and 5 repeat for each additional access until all
               -- the accesses specified in the burst length (BLEN) field of
               -- RBURREG are complete. On the last transfer, the CYNSE70064A
               -- drives the EOT signal HIGH.
               
               for i in 0 to conv_integer(RBURREG.BLEN)-1 loop
                  -- Cycle 4: The selected device starts to drive the DQ[67:0]
                  -- bus, and drives the ACK and EOT from Z to LOW.
                  ACK <= '0';                  
                  cEOT <= '0';
                  DQ  <= (others => '1');
                  wait until CLK='1';                 
                  wait for cam_clk_per/4;
                  wait for 2 ns;

                  if i<conv_integer(RBURREG.BLEN)-1 then cEOT <= '0';
                  else cEOT <= '1'; -- On the last transfer, EOT signal is HIGH.
                  end if;
   
                  -- Cycle 5: The selected device drives the Read data from the
                  -- addr. location on the DQ bus, and drives the ACK signal HIGH.
                  ACK <= '1';
                  if data_flag then aux_signal<=data(conv_integer(RBURREG.ADR))(67 downto 0);
                  else aux_signal<=mask(conv_integer(RBURREG.ADR))(67 downto 0);
                  end if;

                  wait for 1 ps; -- change the value of aux_signal
                  -- ?? maskovani pri cteni?

                  DQ  <= aux_signal;
                  wait until CLK='1';
                  wait for cam_clk_per/4;
                  wait for 2 ns;

                  RBURREG.ADR <= RBURREG.ADR + '1'; -- autoincrementing
                  --RBURREG.BLEN <= RBURREG.BLEN - '1'; -- autodecrementing

               end loop;


               -- Cycle 6: The selected device floats the DQ[67:0] to 3-state
               -- condition and drives the ACK signal LOW.
               ACK <= '0';
               cEOT <= '0';
               DQ  <= (others => 'Z');
               wait until CLK='1';

               -- At the termination of cycle 6, the selected device releases
               -- the ACK line to three-state condition. The Read instruction
               -- is complete, and a new operation can begin.
               ACK <= 'Z';
               cEOT <= 'Z';
            -- end burst read -------------------------------------------------


            when "001"  => -- single write ------------------------------------

               -- Cycle 1A:
               -- The host ASIC applies the Write instruction to the CMD[1:0]
               -- (CMD[2]=0),using CMDV=1 and the address supplied on the DQ bus.

               -- The host ASIC also supplies the GMR Index to mask the Write
               -- to the data or mask array location on CMD[5:3].

--TO DO =>     -- For SRAM Writes, the host ASIC must supply the
               -- SADR[21:20] on CMD[8:7].

               -- wait for cam_clk_per/2;

               -- Cycle 1B: ---
               -- The host ASIC continues to apply the Write instruction to the
               -- CMD[1:0] (CMD[2] = 0), using CMDV = 1 and the address
               -- supplied on the DQ bus.
 --              assert CMD(2 downto 0) = "001"
 --              report "Sorry: I can't burst yet."
 --              severity WARNING;

               assert not CMDV = '1'
               report "CMDV = '1' is neccessary"
               severity WARNING;

               -- The host ASIC continues to supply the GMR Index to mask the
               -- Write to the data or mask array locations in CMD[5:3].
               -- 32 is offset to all(0:63) registers
               -- true is predicate for return value of register to aux_signal
               number := conv_integer(CMD(5 downto 3))+32;
               registers_mapping(number, mask_aux_signal, true); -- read GMR

--TO DO =>     -- The host ASIC selects the device where ID[4:0] matches the
               -- DQ[25:21] lines, or it selects all the devices
               -- when DQ[25:21] = 11111.
               --assert((DQ(25 downto 21) = mID) or (DQ(25 downto 21) = "11111"))
               --report "bad device indentification"
               --severity WARNING;


               -- If DQ[29] is 0, this field carries the address
               -- of the data array location.
               if (DQ(29) = '0') then --direct
                  row := conv_integer(DQ(14 downto 0));

               -- If DQ[29] is 1, the SSRI specified on DQ[28:26] is used to
               -- generate the address of the data array location:
               -- {SSR[14:2], SSR[1] | DQ[1], SSR[0] | DQ[0]}.

               else -- indirect
                  number := conv_integer(DQ(28 downto 26));
      row := conv_integer(SSR0_7(number).INDEX(14 downto 0) or DQ(1 downto 0));
               end if;

               -- cycle 1 : A - increase edge CLK2X and PHL_S high
               address_DQ <= DQ; -- storage old DQ

--TO DO cycles A B + assert for B => CMD[876]=000
               -- cycle 1 : B - increase edge CLK2X
               wait until CLK2X'event AND CLK2X='1'AND PHS_L='0'; -- wait for B
               wait until CLK2X'event AND CLK2X='1'AND PHS_L='0'; -- wait for data

               -- cycle 2 - increase edge CLK2X and PHL_S high
               -- The host ASIC drives the DQ[67:0] with
               -- the data to be written to the data array, mask
               -- array,or register location of the selected device
               -- wait until CLK='1'; -- wait for data
               aux_signal <= DQ and mask_aux_signal; -- masking by GMR
               -- evaluation aux_signal(masking)!

               wait until CLK2X'event AND CLK2X='0' AND PHS_L='1'; -- wait for X

               source_write: case address_DQ(20 downto 19) is

                  when "00"   => -- data array
                      data(row) := (271 downto 68 => '0') & aux_signal;

                  when "01"   => -- mask array
                     mask(row) := (271 downto 68 => '0') & aux_signal;

                  when "10"   => -- external SRAM
                     report "read from external" &
                         "SRAM do not support"
                     severity NOTE;

                  when "11"   => -- internal registers
                     number := conv_integer(address_DQ(5 downto 0));
                     -- false = write
                     registers_mapping(number, aux_signal, false);

                  when others =>
                     report "error: DQ[20:19]=XX"
                     severity WARNING;

               end case source_write;

               -- cycle 3 - increase edge CLK2X and PHL_S high
               -- Idle cycle. At the termination of cycle 3,
               -- another operation can begin.
               -- wait for 10 ns; -- time correction
               -- DQ <= (others => 'X');

               -- cycle 4 - increase edge CLK2X and PHL_S high
               wait until CLK2X'event AND CLK2X='1'AND PHS_L='0';
               wait until CLK2X'event AND CLK2X='0' AND PHS_L='1'; -- wait for Z
            -- end single write -----------------------------------------------


            when "101"  => -- burst write -------------------------------------
               -- Cycle 1A:
               -- The host ASIC applies the Write instruction to the CMD[1:0]
               -- (CMD[2]=0),using CMDV=1 and the address supplied on the DQ bus.

               -- The host ASIC also supplies the GMR Index to mask the Write
               -- to the data or mask array location on CMD[5:3].

               -- wait for cam_clk_per/2;

               -- Cycle 1B: ---
               -- The host ASIC continues to apply the Write instruction to the
               -- CMD[1:0] (CMD[2] = 0), using CMDV = 1 and the address
               -- supplied on the DQ bus.
               assert CMD(2 downto 0) = "001"
               report "Sorry: I can't burst yet."
               severity WARNING;

               assert not CMDV = '1'
               report "CMDV = '1' is neccessary"
               severity WARNING;

               -- The host ASIC continues to supply the GMR Index to mask the
               -- Write to the data or mask array locations in CMD[5:3].
               -- 32 is offset to all(0:63) registers
               -- true is predicate for return value of register to aux_signal
               number := conv_integer(CMD(5 downto 3))+32;
               registers_mapping(number, aux_signal, true); -- read GMR

--TO DO =>     -- The host ASIC selects the device where ID[4:0] matches the
               -- DQ[25:21] lines, or it selects all the devices
               -- when DQ[25:21] = 11111.
               --assert((DQ(25 downto 21) = mID) or (DQ(25 downto 21) = "11111"))
               --report "bad device indentification"
               --severity WARNING;


               -- If DQ[29] is 0, this field carries the address
               -- of the data array location.
--                if (DQ(29) = '0') then --direct
--                   row := conv_integer(DQ(14 downto 0));

               -- If DQ[29] is 1, the SSRI specified on DQ[28:26] is used to
               -- generate the address of the data array location:
               -- {SSR[14:2], SSR[1] | DQ[1], SSR[0] | DQ[0]}.

--                else -- indirect
--                   number := conv_integer(DQ(28 downto 26));
--       row := conv_integer(SSR0_7(number).INDEX(14 downto 0) or DQ(1 downto 0));
--                end if;

               -- cycle 1 : A - increase edge CLK2X and PHL_S high
               address_DQ <= DQ; -- storage old DQ

--TO DO cycles A B + assert for B => CMD[876]=000
               -- cycle 1 : B - increase edge CLK2X
               wait until CLK2X='1'; -- wait for B
               wait until CLK2X='1'; -- wait for data

               -- cycle 2 - increase edge CLK2X and PHL_S high
               -- The host ASIC drives the DQ[67:0] with
               -- the data to be written to the data array, mask
               -- array,or register location of the selected device
               -- wait until CLK='1'; -- wait for data
               mask_aux_signal <= aux_signal;
               wait for 1 ps;
               for i in 0 to conv_integer(WBURREG.BLEN)-1 loop
               
                 aux_signal <= DQ and mask_aux_signal; -- masking by GMR
                 -- evaluation aux_signal(masking)!
               
                 wait until CLK2X'event AND CLK2X='0'AND PHS_L='1';
                 if i = WBURREG.BLEN-2 then cEOT <= '1'; else CEOT <= '0'; end if;                 
                 --cEOT <= '0'; --
                 wait until CLK='1'; -- wait for DataX


                  source_write1: case address_DQ(20 downto 19) is
   
                     when "00"   => -- data array
                         data(conv_integer(WBURREG.ADR)) := (271 downto 68 => '0') & aux_signal;
   
                     when "01"   => -- mask array
                        mask(conv_integer(WBURREG.ADR)) := (271 downto 68 => '0') & aux_signal;
   
   --                   when "10"   => -- external SRAM
   --                      report "read from external" &
   --                          "SRAM do not support"
   --                      severity NOTE;
   -- 
   --                   when "11"   => -- internal registers
   --                      number := conv_integer(address_DQ(5 downto 0));
   --                      -- false = write
   --                      registers_mapping(number, aux_signal, false);
   
                     when others =>
                        report "error: DQ[20:19]=XX"
                        severity WARNING;
   
                  end case source_write1;
   
                  WBURREG.ADR <= WBURREG.ADR + '1'; -- autoincrementing
--                  WBURREG.BLEN <= WBURREG.BLEN - '1'; -- autodecrementing
               wait until PHS_L='1' and PHS_L'event;

               end loop;
               
--               wait until CLK='1'; -- wait for X


               -- cycle 3 - increase edge CLK2X and PHL_S high
               -- Idle cycle. At the termination of cycle 3,
               -- another operation can begin.
               DQ <= (others => 'X');
               cEOT <= 'Z';

            -- end burst write ------------------------------------------------


            when "010" | "110"  => -- search ----------------------------------
               -- The CMD[2] signal must be driven to logic 1.
               -- Note. CMD[2] = 1 signals that the Search is a ×272-bit Search.
               -- CMD[8:3] in this cycle is ignored.

               -- CMD[5:3] signals must be driven with the index to the GMR pair
               -- used fo bits [271:136] of the data being searched
               GMR_pair_A := conv_integer(cmd(5 downto 3));

               -- Cycle A:
               --The host ASIC drives the CMDV HIGH and applies Search command
               --code (10) on CMD[1:0] signals

               -- DQ[67:0] must be driven with the 68-bit data ([271:204]) to be
               -- compared to all locations 0 in the four 68-bits-word page.
               wrd(271 downto 204) := DQ;

               wait for cam_clk_per/4;

               -- Cycle B:
               -- The host ASIC continues to drive the CMDV HIGH and continues to
               -- apply the command code of Search command (10) on CMD[1:0].
               -- CMD10_CMDV("Search cycle B:", CMDV, CMD); -- asserts

               -- The DQ[67:0] is driven with the 68-bit data ([204:136]) to be
               -- compared to all locations 1 in the four 68-bits-word page.
               wrd(203 downto 136) := DQ;
               wait for cam_clk_per/4;

               -- Cycle C:
               -- The host ASIC drives the CMDV HIGH and applies Search command
               -- code (10) on CMD[1:0] signals.
               -- CMD10_CMDV("Search cycle C:", CMDV, CMD); -- asserts

               -- CMD[5:3] signals must be driven with the index to the GMR pair
               -- used for bits [135:0] of the data being searched.
               GMR_pair_C := conv_integer(cmd(5 downto 3));

               -- CMD[8:7] signals must be driven with the bits that will be
               -- driven on SADR[21:20] by this device if it has a hit.
               -- Command bits 8, and 7 {CMD[8:7]} are passed from the command
               -- to the SRAM address bus.
               CMD87 := cmd(8 downto 7);

               -- The CMD[2] signal must be driven to logic 0.
               --assert CMD(2) = '0'
               --report "Search cycle C: " &
               --       "The CMD[2] signal must be driven to logic 0."
               --severity WARNING;

               -- DQ[67:0] must be driven with the 68-bit data ([135:68]) to be
               -- compared to all locations 2 in the four 68-bits-word page.
               wrd(135 downto  68) := DQ;
               wait for cam_clk_per/4;

               -- Cycle D:
               -- The host ASIC continues to drive the CMDV HIGH and applies
               -- Search command code (10) on CMD[1:0].
               -- CMD10_CMDV("Search cycle D:", CMDV, CMD); -- asserts

               -- CMD[8:6] signals must be driven with the index of the
               -- SSR that will be used for storing the address of the
               -- matching entry and the hit flag.
               store_address := conv_integer(CMD(8 downto 6));

               -- The DQ[67:0] is driven with the 68-bit data ([67:0]) to be
               -- compared to all locations 3 in the four 68-bits-word page.
               wrd(67 downto 0) := DQ;

               -- CMD[5:2] is ignored because the Learn instruction is not
               -- supported for x272 tables.


               -- Searching in CAM

               -- 32 is offset to all(0:63) registers
               -- *2 is mapping function for choose pair
               -- + 0 choose first of pair, +1 choose second of pair
               -- true is predicate for return value of register to aux_signal

               number:=GMR_pair_A*2+32+0;
               registers_mapping(number, aux_signal, true);
               wait for 1 ps; -- evaluation aux signal !!! predelat
               gmask_wrd(271 downto 204) := aux_signal;

               number:=GMR_pair_A*2+32+1;
               registers_mapping(number, aux_signal, true);
               wait for 1 ps; -- evaluation aux signal !!! predelat
               gmask_wrd(203 downto 136) := aux_signal;

               number:=GMR_pair_C*2+32+0;
               registers_mapping(number, aux_signal, true);
               wait for 1 ps; -- evaluation aux signal !!! predelat
               gmask_wrd(135 downto 68) := aux_signal;

               number:=GMR_pair_C*2+32+1;
               registers_mapping(number, aux_signal, true);
               wait for 1 ps; -- evaluation aux signal !!! predelat
               gmask_wrd(67 downto 0) := aux_signal;

               i := 0;
               --wrd := wrd and gmask_wrd; -- global masking
               mask_wrd := mask(i) and wrd and gmask_wrd;
               cam_wrd  := mask(i) and data(i) and gmask_wrd;
                while not (mask_wrd=cam_wrd or i=NSE_MEM_SIZE) loop
                  mask_wrd := mask(i) and wrd and gmask_wrd;
                  cam_wrd  := mask(i) and data(i) and gmask_wrd;
                  i:=i+1;
		 
               end loop;

               if not (i = NSE_MEM_SIZE) then
--                  i:=i*4;
                  SSR0_7(store_address).Index<=conv_std_logic_vector(i, 15);
--                  SRAM_aux_s <= CMD87&mID&conv_std_logic_vector(i, 15);
                  
                  CEL_aux <= '0';
                  ALEL_aux <= '0';
               end if;
               
               wait for cam_clk_per/2000;

               SRAM_aux_s <= (others => 'Z');
               ALEL_aux <= '0';               

               if not (i = NSE_MEM_SIZE) then
                  ssf_aux <= '1';
                  SRAM_aux_s <= CMD87&mID&conv_std_logic_vector((i-1)*4, 15);
                  ALEL_aux <= '1';               
               end if;
               ssv_aux <= '1';               
               CEL_aux <= '1';

             -- end search ------------------------------------------------------


            -- The 272-bit-configured devices or 272-bit-configured quadrants
            -- within devices do not support the Learn instruction.
            when "011" | "111" =>               
               -- Cycle 1A:
               -- The host ASIC applies the Learn instruction on CMD[1:0] using CMDV = 1.
               cd <= (others => 'X');
               wait until CLK2X'event AND CLK2X='1'AND PHS_L='1';
               -- The CMD[5:2] field specifies the index of the comparand register pair
               -- that will be written in the data array in the 136-bit-configured table.
               
               -- For a Learn in a 68-bit-configured table, the even-numbered comparand
               -- specified by this index will be written.
               cmd5_2_a:=CMD(5 downto 2);
               
               -- CMD[8:7] carries the bits
               -- that will be driven on SADR[21:20] in the SRAM Write cycle.
               sadr21_20:=CMD(8 downto 7);
              
               -- Cycle 1B: The host ASIC continues to drive the CMDV to 1, the CMD[1:0] to 11,
               wait until CLK2X'event AND CLK2X='1'AND PHS_L='0';
               -- and the CMD[5:2] with the comparand pair index.
               cmd5_2_b:=CMD(5 downto 2);

               -- Cycle 2: The host ASIC drives the CMDV to 0. At the end of cycle 2,
               -- a new instruction can begin. The latency of the SRAM Write is the
               -- same as the Search to the SRAM Read cycle. It is measured from the
               -- second cycle of the Learn instruction.
               
               check_NFA; -- check next free position in cam
               
               number:=conv_integer(cmd5_2_a)*2+0; -- even-numbered comparand
               registers_mapping(number, aux_signal, true); -- read comparand
               data(conv_integer(NFA.INDEX))(67 downto 0):= aux_signal;


               --CMD[6] must be set to 0 if the Learn is being performed on a 68-bit-configured
               -- table, and to 1 if the Learn is being performed on a 136-bit-configured table.
               if CMD(6) = '1' then -- 136b configuration
                 number:=conv_integer(cmd5_2_a)*2+1; -- odd-numbered comparand
                 registers_mapping(number, aux_signal, true); -- read comparand
                 data(conv_integer(NFA.INDEX))(135 downto 68):= aux_signal;
               end if;
              
               cd <= (others => 'Z');
               sram_aux <= sadr21_20&mID&NFA.INDEX; -- ???
               oel_aux <= '1';
               wel_aux <= '0';
               cel_aux <= '0';

               report "do not support the Learn instruction"
               severity WARNING;

            -- end learn -------------------------------------------------------

            when others =>          -- Other states
               -- CAM test
               ssf_aux <= '0';
               ssv_aux <= '0';
               wait for 2*cam_clk_per;

         end case operation;
       end if; -- cmdv
     end if; --reset
    end process signals_drive;

    --*************************************************************************

   internal_clock: process --**************************************************

   begin
      -- NSE uses the PHS_L signal to divide CLK2X and generate an
      -- internal CLK. (CLK2X a CLK are used for internal operations)

      wait until (CLK2X'event AND CLK2X = '1' AND PHS_L = '0');
      CLK <= '1';

      wait until (CLK2X'event AND CLK2X = '1' AND PHS_L = '1');
      CLK <= '0';
   end process internal_clock;

   --**************************************************************************
   latency_of_sram_for_learn : process (PHS_L, sram_aux, RST_L)
   begin
      if (PHS_L'event AND PHS_L = '1') then
         if (RST_L='0' or sram_aux= (21 downto 0 => 'U') or sram_aux=(21 downto 0 => 'Z') or COMMAND.TLSZ="UU") then
            sram_buffer(6 downto 0) <= sram_buffer(7 downto 1);
            sram_buffer(7) <= (21 downto 0 => 'Z');
            sram_buffer(conv_integer(COMMAND.HLAT)+3) <=  (21 downto 0 => 'Z');
         else            
            sram_buffer(6 downto 0) <= sram_buffer(7 downto 1);
            sram_buffer(7) <= (21 downto 0 => '0');
            
            sram_buffer(conv_integer(COMMAND.HLAT)+3) <= sram_aux;
         end if;
      end if;
      sram_out <= sram_buffer(0);
   end process latency_of_sram_for_learn;

   latency_of_oel: process (PHS_L, oel_aux, RST_L)
   begin
      if (PHS_L'event AND PHS_L = '1') then
         if (RST_L='0' or oel_aux='U' or oel_aux='Z' or COMMAND.HLAT="UU") then
            oel_buffer <= (others => '0');
         else
            oel_buffer <= '0' & oel_buffer(7 downto 1); -- Shift Right Logical
            oel_buffer(conv_integer(COMMAND.HLAT)+3) <= oel_aux;
            if oel_aux = '1' then  -- hold oel for two cycles
               oel_buffer(conv_integer(COMMAND.HLAT)+3 downto conv_integer(COMMAND.HLAT)+2) <= "11";
            end if;            
         end if;
      end if;
      oel_out <= oel_buffer(0);       
   end process latency_of_oel;

   latency_of_cel: process (PHS_L, cel_aux, RST_L)
   begin
      if (PHS_L'event AND PHS_L = '1') then
         if (RST_L='0' or cel_aux='U' or cel_aux='Z' or COMMAND.HLAT="UU") then
            cel_buffer <= (others => '0');
         else
            cel_buffer <= '0' & cel_buffer(7 downto 1); -- Shift Right Logical
            cel_buffer(conv_integer(COMMAND.HLAT)+3) <= cel_aux;
         end if;
      end if;
      cel_out <= cel_buffer(0);
   end process latency_of_cel;

   latency_of_alel: process (PHS_L, alel_aux, RST_L)
   begin
      if (PHS_L'event AND PHS_L = '1') then
         if (RST_L='0' or alel_aux='U' or alel_aux='Z' or COMMAND.HLAT="UU") then
            alel_buffer <= (others => '0');
         else
            alel_buffer <= '0' & alel_buffer(7 downto 1);
            alel_buffer(conv_integer(COMMAND.HLAT)+2) <= alel_aux;
         end if;
      end if;
      alel_out <= alel_buffer(0);
   end process latency_of_alel;

   latency_of_wel: process (PHS_L, wel_aux, RST_L)
   begin
      if (PHS_L'event AND PHS_L = '1') then
         if (RST_L='0' or wel_aux='U' or wel_aux='Z' or COMMAND.HLAT="UU") then
            wel_buffer <= (others => '0');
         else
            wel_buffer <= '0' & wel_buffer(7 downto 1); -- Shift Right Logical
            wel_buffer(conv_integer(COMMAND.HLAT)+3) <= wel_aux;
         end if;
      end if;
      wel_out <= wel_buffer(0);
   end process latency_of_wel;

   --**************************************************************************
   latency_of_sram_for_search : process (PHS_L, sram_aux_s, RST_L)
   begin
      if (PHS_L'event AND PHS_L = '1') then
         if (RST_L='0' or sram_aux_s= (21 downto 0 => 'U') or sram_aux_s=(21 downto 0 => 'Z') or COMMAND.HLAT="UU") then
            sram_buffer_s(6 downto 0) <= sram_buffer_s(7 downto 1);
            sram_buffer_s(7) <= (21 downto 0 => 'Z');
            sram_buffer_s(conv_integer(COMMAND.HLAT)+3) <=  (21 downto 0 => 'Z');
            --sram_buffer_s <= (others => (others => 'Z'));
         else            
            sram_buffer_s(6 downto 0) <= sram_buffer_s(7 downto 1);
            sram_buffer_s(7) <= (21 downto 0 => '0');
            
            sram_buffer_s(conv_integer(COMMAND.HLAT)+2) <= sram_aux_s;
         end if;
      end if;
      sram_out_s <= sram_buffer_s(0);
   end process latency_of_sram_for_search;

   latency_of_ssv: process (PHS_L, ssv_aux, RST_L)
   begin
      if (PHS_L'event AND PHS_L = '1') then
         if (RST_L='0' or ssv_aux='U' or ssv_aux='Z' or COMMAND.HLAT="UU") then
            ssv_buffer <= (others => '0');
         else
            ssv_buffer <= '0' & ssv_buffer(7 downto 1); -- Shift Right Logical
            ssv_buffer(conv_integer(COMMAND.HLAT)+3) <= ssv_aux;
         end if;
      end if;
      ssv_out <= ssv_buffer(0);
   end process latency_of_ssv;

   latency_of_ssf: process (PHS_L, ssf_aux, RST_L)
   begin
      if (PHS_L'event AND PHS_L = '1') then
         if (RST_L='0' or ssf_aux='U' or ssf_aux='Z' or COMMAND.HLAT="UU") then
            ssf_buffer <= (others => '0');
         else
            -- ssf_buffer <= ssf_buffer SRL 1; -- Shift Right Logical
            ssf_buffer <= '0' & ssf_buffer(7 downto 1);
            ssf_buffer(conv_integer(COMMAND.HLAT)+3) <= ssf_aux;
         end if;
      end if;
      ssf_out <= ssf_buffer(0);
   end process latency_of_ssf;
   
-- learn
cad   <= sram_out;
ce_l  <= ale_l;
we_l  <= wel_out;
oe_l  <= oel_out;

-- search
ssf   <= ssf_out;
ssv   <= ssv_out;
cad   <= sram_out_s;
ale_l <= not alel_out;

end architecture CYNSE70064A_arch;




