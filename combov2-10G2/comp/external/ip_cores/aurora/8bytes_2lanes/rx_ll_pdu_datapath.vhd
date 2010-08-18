    -------------------------------------------------------------------------------
--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: rx_ll_pdu_datapath.vhd,v $
--          Rev:  $Revision$
--
--      Company:  Xilinx
-- Contributors:  R. K. Awalt, B. L. Woodard, N. Gulstone
--
--   Disclaimer:  XILINX IS PROVIDING THIS DESIGN, CODE, OR
--                INFORMATION "AS IS" SOLELY FOR USE IN DEVELOPING
--                PROGRAMS AND SOLUTIONS FOR XILINX DEVICES.  BY
--                PROVIDING THIS DESIGN, CODE, OR INFORMATION AS
--                ONE POSSIBLE IMPLEMENTATION OF THIS FEATURE,
--                APPLICATION OR STANDARD, XILINX IS MAKING NO
--                REPRESENTATION THAT THIS IMPLEMENTATION IS FREE
--                FROM ANY CLAIMS OF INFRINGEMENT, AND YOU ARE
--                RESPONSIBLE FOR OBTAINING ANY RIGHTS YOU MAY
--                REQUIRE FOR YOUR IMPLEMENTATION.  XILINX
--                EXPRESSLY DISCLAIMS ANY WARRANTY WHATSOEVER WITH
--                RESPECT TO THE ADEQUACY OF THE IMPLEMENTATION,
--                INCLUDING BUT NOT LIMITED TO ANY WARRANTIES OR
--                REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE
--                FROM CLAIMS OF INFRINGEMENT, IMPLIED WARRANTIES
--                OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
--                PURPOSE.
--
--                (c) Copyright 2004 Xilinx, Inc.
--                All rights reserved.
--
-------------------------------------------------------------------------------
--
--  RX_LL_PDU_DATAPATH
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  Description: the RX_LL_PDU_DATAPATH module takes regular PDU data in Aurora format
--               and transforms it to LocalLink formatted data
--
--               This module supports 4 4-byte lane designs
--              
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;
use WORK.AURORA.all;
library aurora_8byte;

entity RX_LL_PDU_DATAPATH is

    port (

    -- Traffic Separator Interface

            PDU_DATA     : in std_logic_vector(0 to 63);
            PDU_DATA_V   : in std_logic_vector(0 to 3);
            PDU_PAD      : in std_logic_vector(0 to 3);
            PDU_SCP      : in std_logic_vector(0 to 3);
            PDU_ECP      : in std_logic_vector(0 to 3);

    -- LocalLink PDU Interface

            RX_D         : out std_logic_vector(0 to 63);
            RX_REM       : out std_logic_vector(0 to 2);
            RX_SRC_RDY_N : out std_logic;
            RX_SOF_N     : out std_logic;
            RX_EOF_N     : out std_logic;

    -- Error Interface

            FRAME_ERROR  : out std_logic;

    -- System Interface

            USER_CLK     : in std_logic;
            RESET        : in std_logic

         );

end RX_LL_PDU_DATAPATH;


architecture RTL of RX_LL_PDU_DATAPATH is

--****************************Parameter Declarations**************************

    constant DLY : time := 1 ns;

    
--****************************External Register Declarations**************************

    signal RX_D_Buffer                      : std_logic_vector(0 to 63);
    signal RX_REM_Buffer                    : std_logic_vector(0 to 2);
    signal RX_SRC_RDY_N_Buffer              : std_logic;
    signal RX_SOF_N_Buffer                  : std_logic;
    signal RX_EOF_N_Buffer                  : std_logic;
    signal FRAME_ERROR_Buffer               : std_logic;


--****************************Internal Register Declarations**************************
    --Stage 1
    signal stage_1_data_r                   : std_logic_vector(0 to 63); 
    signal stage_1_pad_r                    : std_logic;  
    signal stage_1_ecp_r                    : std_logic_vector(0 to 3);
    signal stage_1_scp_r                    : std_logic_vector(0 to 3);
    signal stage_1_start_detected_r         : std_logic;


    --Stage 2
    signal stage_2_data_r                   : std_logic_vector(0 to 63);
    signal stage_2_pad_r                    : std_logic;  
    signal stage_2_start_with_data_r        : std_logic; 
    signal stage_2_end_before_start_r       : std_logic;
    signal stage_2_end_after_start_r        : std_logic;    
    signal stage_2_start_detected_r         : std_logic; 
    signal stage_2_frame_error_r            : std_logic;
        

    




--*********************************Wire Declarations**********************************
    --Stage 1
    signal stage_1_data_v_r                 : std_logic_vector(0 to 3);
    signal stage_1_after_scp_r              : std_logic_vector(0 to 3);
    signal stage_1_in_frame_r               : std_logic_vector(0 to 3);
    
    --Stage 2
    signal stage_2_left_align_select_r      : std_logic_vector(0 to 11);
    signal stage_2_data_v_r                 : std_logic_vector(0 to 3);
    
    signal stage_2_data_v_count_r           : std_logic_vector(0 to 2);
    signal stage_2_frame_error_c            : std_logic;
             
 
    --Stage 3
    signal stage_3_data_r                   : std_logic_vector(0 to 63);
    
 
    
    signal stage_3_storage_count_r          : std_logic_vector(0 to 2);
    signal stage_3_storage_ce_r             : std_logic_vector(0 to 3);
    signal stage_3_end_storage_r            : std_logic;
    signal stage_3_storage_select_r         : std_logic_vector(0 to 19);
    signal stage_3_output_select_r          : std_logic_vector(0 to 19);
    signal stage_3_src_rdy_n_r              : std_logic;
    signal stage_3_sof_n_r                  : std_logic;
    signal stage_3_eof_n_r                  : std_logic;
    signal stage_3_rem_r                    : std_logic_vector(0 to 2);
    signal stage_3_frame_error_r            : std_logic;
    
  
  
    --Stage 4
    signal storage_data_r                   : std_logic_vector(0 to 63);
  
    

-- ********************************** Component Declarations ************************************--

    component RX_LL_DEFRAMER
    port (
        PDU_DATA_V      : in std_logic_vector(0 to 3);
        PDU_SCP         : in std_logic_vector(0 to 3);
        PDU_ECP         : in std_logic_vector(0 to 3);
        USER_CLK        : in std_logic;
        RESET           : in std_logic;
        
        DEFRAMED_DATA_V : out std_logic_vector(0 to 3);
        IN_FRAME        : out std_logic_vector(0 to 3);
        AFTER_SCP       : out std_logic_vector(0 to 3)
    );
    end component;


    component LEFT_ALIGN_CONTROL
    port (
        PREVIOUS_STAGE_VALID : in std_logic_vector(0 to 3);

        MUX_SELECT           : out std_logic_vector(0 to 11);
        VALID                : out std_logic_vector(0 to 3);

        USER_CLK             : in std_logic;
        RESET                : in std_logic

    );
    end component;


    component VALID_DATA_COUNTER
    port (
        PREVIOUS_STAGE_VALID : in std_logic_vector(0 to 3);
        
        USER_CLK             : in std_logic;
        RESET                : in std_logic;
        
        COUNT                : out std_logic_vector(0 to 2)
     );
     end component;


    component LEFT_ALIGN_MUX
    port (
        RAW_DATA   : in std_logic_vector(0 to 63);
        MUX_SELECT : in std_logic_vector(0 to 11);
        
        USER_CLK   : in std_logic;
        
        MUXED_DATA : out std_logic_vector(0 to 63)

     );
    end component;


    component STORAGE_COUNT_CONTROL
    port (

        LEFT_ALIGNED_COUNT : in std_logic_vector(0 to 2);
        END_STORAGE        : in std_logic;
        START_WITH_DATA    : in std_logic;
        FRAME_ERROR        : in std_logic;
        
        STORAGE_COUNT      : out std_logic_vector(0 to 2);
        
        USER_CLK           : in std_logic;
        RESET              : in std_logic
    );
    end component;


    component STORAGE_CE_CONTROL
    port (
        LEFT_ALIGNED_COUNT : in std_logic_vector(0 to 2);
        STORAGE_COUNT      : in std_logic_vector(0 to 2);
        END_STORAGE        : in std_logic;
        START_WITH_DATA    : in std_logic;
        
        STORAGE_CE         : out std_logic_vector(0 to 3);
        
        USER_CLK           : in std_logic;
        RESET              : in std_logic
    );
    end component;


    component STORAGE_SWITCH_CONTROL
    port (
        LEFT_ALIGNED_COUNT : in std_logic_vector(0 to 2);
        STORAGE_COUNT      : in std_logic_vector(0 to 2);
        END_STORAGE        : in std_logic;
        START_WITH_DATA    : in std_logic;
        
        STORAGE_SELECT     : out std_logic_vector(0 to 19);
        
        USER_CLK           : in std_logic
    );
    end component;


    component OUTPUT_SWITCH_CONTROL
    port (
        LEFT_ALIGNED_COUNT : in std_logic_vector(0 to 2);
        STORAGE_COUNT      : in std_logic_vector(0 to 2);
        END_STORAGE        : in std_logic;
        START_WITH_DATA    : in std_logic;
        
        OUTPUT_SELECT      : out std_logic_vector(0 to 19);
        
        USER_CLK           : in std_logic
    );
    end component;


    component SIDEBAND_OUTPUT
    port (
        LEFT_ALIGNED_COUNT : in std_logic_vector(0 to 2);
        STORAGE_COUNT      : in std_logic_vector(0 to 2);
        END_BEFORE_START   : in std_logic;
        END_AFTER_START    : in std_logic;
        START_DETECTED     : in std_logic;
        START_WITH_DATA    : in std_logic;
        PAD                : in std_logic;
        FRAME_ERROR        : in std_logic;
        USER_CLK           : in std_logic;
        RESET              : in std_logic;
        END_STORAGE        : out std_logic;
        SRC_RDY_N          : out std_logic;
        SOF_N              : out std_logic;
        EOF_N              : out std_logic;
        RX_REM             : out std_logic_vector(0 to 2);
        FRAME_ERROR_RESULT : out std_logic
    );
    end component;


    component STORAGE_MUX
    port (

        RAW_DATA     : in std_logic_vector(0 to 63);
        MUX_SELECT   : in std_logic_vector(0 to 19);
        STORAGE_CE   : in std_logic_vector(0 to 3);
        USER_CLK     : in std_logic;
        
        STORAGE_DATA : out std_logic_vector(0 to 63)
    );
    end component;


    component OUTPUT_MUX
    port (
        STORAGE_DATA      : in std_logic_vector(0 to 63);
        LEFT_ALIGNED_DATA : in std_logic_vector(0 to 63);
        MUX_SELECT        : in std_logic_vector(0 to 19);
        USER_CLK          : in std_logic;
        
        OUTPUT_DATA       : out std_logic_vector(0 to 63)
    );
    end component;


begin    
   
--*********************************Main Body of Code**********************************
    
    -- VHDL Helper Logic
    RX_D         <= RX_D_Buffer;
    RX_REM       <= RX_REM_Buffer;
    RX_SRC_RDY_N <= RX_SRC_RDY_N_Buffer;
    RX_SOF_N     <= RX_SOF_N_Buffer;
    RX_EOF_N     <= RX_EOF_N_Buffer;
    FRAME_ERROR  <= FRAME_ERROR_Buffer;
    
    


    --_____Stage 1: Decode Frame Encapsulation and remove unframed data ________
    
    
    stage_1_rx_ll_deframer_i : RX_LL_DEFRAMER 
    port map
    (        
        PDU_DATA_V          =>   PDU_DATA_V,
        PDU_SCP             =>   PDU_SCP,
        PDU_ECP             =>   PDU_ECP,
        USER_CLK            =>   USER_CLK,
        RESET               =>   RESET,

        DEFRAMED_DATA_V     =>   stage_1_data_v_r,
        IN_FRAME            =>   stage_1_in_frame_r,
        AFTER_SCP           =>   stage_1_after_scp_r
   
    );
    
   
    --Determine whether there were any SCPs detected, regardless of data
    process(USER_CLK)
    begin
        if(USER_CLK 'event and USER_CLK = '1') then
            if(RESET = '1') then
                stage_1_start_detected_r    <= '0' after DLY;  
            else         
                stage_1_start_detected_r    <=  std_bool(PDU_SCP /= "0000") after DLY; 
            end if;
        end if;
    end process;    
   
   
    --Pipeline the data signal, and register a signal to indicate whether the data in
    -- the current cycle contained a Pad character.
    process(USER_CLK)
    begin
        if(USER_CLK 'event and USER_CLK = '1') then
            stage_1_data_r             <=  PDU_DATA after DLY;
            stage_1_pad_r              <=  std_bool(PDU_PAD /= "0000") after DLY;
            stage_1_ecp_r              <=  PDU_ECP after DLY;
            stage_1_scp_r              <=  PDU_SCP after DLY;
        end if;    
    end process;    
    
    
    
    --_______________________Stage 2: First Control Stage ___________________________
    
    
    --We instantiate a LEFT_ALIGN_CONTROL module to drive the select signals for the
    --left align mux in the next stage, and to compute the next stage valid signals
    
    stage_2_left_align_control_i : LEFT_ALIGN_CONTROL 
    port map(
        PREVIOUS_STAGE_VALID    =>   stage_1_data_v_r,

        MUX_SELECT              =>   stage_2_left_align_select_r,
        VALID                   =>   stage_2_data_v_r,
        
        USER_CLK                =>   USER_CLK,
        RESET                   =>   RESET

    );
        

    
    --Count the number of valid data lanes: this count is used to select which data 
    -- is stored and which data is sent to output in later stages    
    stage_2_valid_data_counter_i : VALID_DATA_COUNTER 
    port map(
        PREVIOUS_STAGE_VALID    =>   stage_1_data_v_r,
        USER_CLK                =>   USER_CLK,
        RESET                   =>   RESET,
        
        COUNT                   =>   stage_2_data_v_count_r
    );
     
     
          
    --Pipeline the data and pad bits
    process(USER_CLK)
    begin
        if(USER_CLK 'event and USER_CLK = '1') then
            stage_2_data_r          <=  stage_1_data_r after DLY;        
            stage_2_pad_r           <=  stage_1_pad_r after DLY;
        end if;    
    end process;   
        
        
    
    
    --Determine whether there was any valid data after any SCP characters
    process(USER_CLK)
    begin
        if(USER_CLK 'event and USER_CLK = '1') then
            if(RESET = '1') then
                stage_2_start_with_data_r    <=  '0' after DLY;
            else
                stage_2_start_with_data_r    <=  std_bool((stage_1_data_v_r and stage_1_after_scp_r) /= "0000") after DLY;
            end if;
        end if;
    end process;    
        
        
        
    --Determine whether there were any ECPs detected before any SPC characters
    -- arrived
    process(USER_CLK)
    begin
        if(USER_CLK 'event and USER_CLK = '1') then
            if(RESET = '1') then
                stage_2_end_before_start_r      <=  '0' after DLY;   
            else
                stage_2_end_before_start_r      <=  std_bool((stage_1_ecp_r and not stage_1_after_scp_r) /= "0000") after DLY;
            end if;
        end if;
    end process;    
    
    
    --Determine whether there were any ECPs detected at all
    process(USER_CLK)
    begin
        if(USER_CLK 'event and USER_CLK = '1') then
            if(RESET = '1') then
                stage_2_end_after_start_r       <=  '0' after DLY;   
            else        
                stage_2_end_after_start_r       <=  std_bool((stage_1_ecp_r and stage_1_after_scp_r) /= "0000") after DLY;
            end if;
        end if;
    end process;    
        
    
    --Pipeline the SCP detected signal
    process(USER_CLK)
    begin
        if(USER_CLK 'event and USER_CLK = '1') then
            if(RESET = '1') then
                stage_2_start_detected_r    <=  '0' after DLY;  
            else        
                stage_2_start_detected_r    <=   stage_1_start_detected_r after DLY;
            end if;
        end if;
    end process;    
        
    
    
    --Detect frame errors. Note that the frame error signal is held until the start of 
    -- a frame following the data beat that caused the frame error
    stage_2_frame_error_c   <=   std_bool( (stage_1_ecp_r and not stage_1_in_frame_r) /= "0000" ) or
                                 std_bool( (stage_1_scp_r and stage_1_in_frame_r) /= "0000" );
    
    
    process(USER_CLK)
    begin
        if(USER_CLK 'event and USER_CLK = '1') then
            if(RESET = '1') then
                stage_2_frame_error_r               <=  '0' after DLY;
            elsif(stage_2_frame_error_c = '1') then
                stage_2_frame_error_r               <=  '1' after DLY;
            elsif(stage_1_start_detected_r = '1') then   
                stage_2_frame_error_r               <=  '0' after DLY;
            end if;
        end if;
    end process;    
       
    
        
 



    --_______________________________ Stage 3 Left Alignment _________________________
    
    
    --We instantiate a left align mux to shift all lanes with valid data in the channel leftward
    --The data is seperated into groups of 8 lanes, and all valid data within each group is left
    --aligned.
    stage_3_left_align_datapath_mux_i : LEFT_ALIGN_MUX 
    port map(
        RAW_DATA    =>   stage_2_data_r,
        MUX_SELECT  =>   stage_2_left_align_select_r,
        USER_CLK    =>   USER_CLK,
 
        MUXED_DATA  =>   stage_3_data_r
    );
        






    --Determine the number of valid data lanes that will be in storage on the next cycle
    stage_3_storage_count_control_i : STORAGE_COUNT_CONTROL 
    port map(
        LEFT_ALIGNED_COUNT  =>   stage_2_data_v_count_r,
        END_STORAGE         =>   stage_3_end_storage_r,
        START_WITH_DATA     =>   stage_2_start_with_data_r,
        FRAME_ERROR         =>   stage_2_frame_error_r,
        
        STORAGE_COUNT       =>   stage_3_storage_count_r,
        
        USER_CLK            =>   USER_CLK,
        RESET               =>   RESET
          
    );
        
     
     
    --Determine the CE settings for the storage module for the next cycle
    stage_3_storage_ce_control_i : STORAGE_CE_CONTROL 
    port map(
        LEFT_ALIGNED_COUNT  =>   stage_2_data_v_count_r,
        STORAGE_COUNT       =>   stage_3_storage_count_r,
        END_STORAGE         =>   stage_3_end_storage_r,
        START_WITH_DATA     =>   stage_2_start_with_data_r,

        STORAGE_CE          =>   stage_3_storage_ce_r,
        
        USER_CLK            =>   USER_CLK,
        RESET               =>   RESET
    
    );
    
             
        
    --Determine the appropriate switch settings for the storage module for the next cycle
    stage_3_storage_switch_control_i : STORAGE_SWITCH_CONTROL 
    port map(
        LEFT_ALIGNED_COUNT  =>   stage_2_data_v_count_r,
        STORAGE_COUNT       =>   stage_3_storage_count_r,
        END_STORAGE         =>   stage_3_end_storage_r,
        START_WITH_DATA     =>   stage_2_start_with_data_r,

        STORAGE_SELECT      =>   stage_3_storage_select_r,
        
        USER_CLK            =>   USER_CLK
        
    );
    
        
        
    --Determine the appropriate switch settings for the output module for the next cycle
    stage_3_output_switch_control_i : OUTPUT_SWITCH_CONTROL 
    port map(
        LEFT_ALIGNED_COUNT  =>   stage_2_data_v_count_r,
        STORAGE_COUNT       =>   stage_3_storage_count_r,
        END_STORAGE         =>   stage_3_end_storage_r,
        START_WITH_DATA     =>   stage_2_start_with_data_r,

        OUTPUT_SELECT       =>   stage_3_output_select_r,
        
        USER_CLK            =>   USER_CLK
    
    );
        
    
    --Instantiate a sideband output controller
    sideband_output_i : SIDEBAND_OUTPUT 
    port map(
        LEFT_ALIGNED_COUNT  =>   stage_2_data_v_count_r,
        STORAGE_COUNT       =>   stage_3_storage_count_r,
        END_BEFORE_START    =>   stage_2_end_before_start_r,
        END_AFTER_START     =>   stage_2_end_after_start_r,
        START_DETECTED      =>   stage_2_start_detected_r,
        START_WITH_DATA     =>   stage_2_start_with_data_r,
        PAD                 =>   stage_2_pad_r,
        FRAME_ERROR         =>   stage_2_frame_error_r,
        USER_CLK            =>   USER_CLK,
        RESET               =>   RESET,
    
        END_STORAGE         =>   stage_3_end_storage_r,
        SRC_RDY_N           =>   stage_3_src_rdy_n_r,
        SOF_N               =>   stage_3_sof_n_r,
        EOF_N               =>   stage_3_eof_n_r,
        RX_REM              =>   stage_3_rem_r,
        FRAME_ERROR_RESULT  =>   stage_3_frame_error_r
    );
    
      
    
    
    
    --________________________________ Stage 4: Storage and Output_______________________
 
    
    --Storage: Data is moved to storage when it cannot be sent directly to the output.
    
    stage_4_storage_mux_i : STORAGE_MUX 
    port map(
        RAW_DATA        =>   stage_3_data_r,
        MUX_SELECT      =>   stage_3_storage_select_r,
        STORAGE_CE      =>   stage_3_storage_ce_r,
        USER_CLK        =>   USER_CLK,

        STORAGE_DATA    =>   storage_data_r
        
    );
    
    
    
    --Output: Data is moved to the locallink output when a full word of valid data is ready,
    -- or the end of a frame is reached
    
    output_mux_i : OUTPUT_MUX 
    port map(
        STORAGE_DATA        =>   storage_data_r,    
        LEFT_ALIGNED_DATA   =>   stage_3_data_r,
        MUX_SELECT          =>   stage_3_output_select_r,
        USER_CLK            =>   USER_CLK,
        
        OUTPUT_DATA         =>   RX_D_Buffer
        
    );
    
    
    --Pipeline LocalLink sideband signals
    process(USER_CLK)
    begin
        if(USER_CLK 'event and USER_CLK = '1') then
            RX_SOF_N_Buffer        <=  stage_3_sof_n_r after DLY;
            RX_EOF_N_Buffer        <=  stage_3_eof_n_r after DLY;
            RX_REM_Buffer          <=  stage_3_rem_r after DLY;
        end if;    
    end process;
         

    --Pipeline the LocalLink source Ready signal
    process(USER_CLK)
    begin
        if(USER_CLK 'event and USER_CLK = '1') then
            if(RESET = '1') then
                RX_SRC_RDY_N_Buffer    <=  '1' after DLY;
            else
                RX_SRC_RDY_N_Buffer    <=  stage_3_src_rdy_n_r after DLY;
            end if;
        end if;
    end process;    
        
        
    
    --Pipeline the Frame error signal
    process(USER_CLK)
    begin
        if(USER_CLK 'event and USER_CLK = '1') then
            if(RESET = '1') then
                FRAME_ERROR_Buffer     <=  '0' after DLY;
            else        
                FRAME_ERROR_Buffer     <=  stage_3_frame_error_r after DLY;
            end if;
        end if;
    end process;    
    
 
 
 end RTL;


