/************************************************************************/
/* Cypress Semiconductor Company Confidential                           */
/* Copyright 1999, Cypress Semiconductor. All Rights reserved           */
/* Cypress Semiconductor proprietary source code                        */
/* Permission to use, modify or copy this code is prohibited            */
/* without the express written consent of                               */
/* Cypress Semiconductor                                                */
/* Filename: README_ref									*/
/* Release: 1.6 									*/
/* Last Updated: @(#)README_ref	1.6 03/22/04, see TNT-100								*/
/* Stored at WPP central, clearcase									*/
/************************************************************************/

`timescale 10ps/10ps
`define CAM_2MEG 1 //Simulating CYNSE70064: 2Mb device
 `define MODELSIM 1
 
`ifdef CAM_4MEG
   `ifdef MHZ_100
      `define 		T_CLK2X           500
      `define 		T_HIZ_DQ          650
      `define 		T_HIZ_SRAM        550

      `ifdef DYN_WC
         `define 		TOUT_SRAMBUS           700
         `define 		TOUT_DQBUS             700
         `define 		TOUT_CASC              650

         `define 		TSETUP                 150
         `define 		TCASC_SETUP            300
         `define 		THOLD                  50

         `define 		TSTROBE                710
      `else
         `ifdef DYN_BC
            `define 		TOUT_SRAMBUS           100
            `define 		TOUT_DQBUS             100
            `define 		TOUT_CASC              100
   
            `define 		TSETUP                 150
            `define 		TCASC_SETUP            300
            `define 		THOLD                  50
            `define 		TSTROBE                710
         `else
            `ifdef DYN_TC
               `define 	TOUT_SRAMBUS           300
               `define 	TOUT_DQBUS             300
               `define 	TOUT_CASC              300

               `define 	TSETUP                 150
               `define 	TCASC_SETUP            300
               `define 	THOLD                  50
               `define 	TSTROBE                710
            `else
               `define 	TOUT_SRAMBUS           300 
               `define 	TOUT_DQBUS             300
               `define 	TOUT_CASC              300

               `define 	TSETUP                 150
               `define 	TCASC_SETUP            300
               `define 	THOLD                  50
               `define 	TSTROBE                710
            `endif  // end of !DYN_TC
         `endif  // end of !DYN_BC
      `endif  // end of !DYN_WC
   `else
      `ifdef MHZ_83
         `define 		T_CLK2X           600
   	 `define 		T_HIZ_DQ          700
   	 `define 		T_HIZ_SRAM        600

         `ifdef DYN_WC
            `define 		TOUT_SRAMBUS      750
            `define 		TOUT_DQBUS        750
            `define 		TOUT_CASC         700

            `define 		TSETUP            180
            `define 		TCASC_SETUP       350
            `define 		THOLD             60

            `define 		TSTROBE           760
         `else
            `ifdef DYN_BC
               `define 		TOUT_SRAMBUS      100
               `define 		TOUT_DQBUS        100
               `define 		TOUT_CASC         100
   
               `define 		TSETUP            180
               `define 		TCASC_SETUP       350
               `define 		THOLD             60
               `define 		TSTROBE           760
            `else
               `ifdef DYN_TC
                  `define 	TOUT_SRAMBUS      300
                  `define 	TOUT_DQBUS        300
                  `define 	TOUT_CASC         300

                  `define 	TSETUP            180
                  `define 	TCASC_SETUP       350
                  `define 	THOLD             60
                  `define 	TSTROBE           760
               `else
                  `define 	TOUT_SRAMBUS      300
                  `define 	TOUT_DQBUS        300
                  `define 	TOUT_CASC         300

                  `define 	TSETUP            180
                  `define 	TCASC_SETUP       350
                  `define 	THOLD             60
                  `define 	TSTROBE           760
               `endif // end of !DYN_TC
            `endif // end of !DYN_BC
         `endif // end of !DYN_WC
     
      `else				// 66 MHZ operation
   	  `define 		T_CLK2X           750
   	  `define 		T_HIZ_DQ          850
   	  `define 		T_HIZ_SRAM        650

            `ifdef DYN_WC
               `define 		TOUT_SRAMBUS      900
               `define 		TOUT_DQBUS        900
               `define 		TOUT_CASC         850

               `define 		TSETUP            250 
               `define 		TCASC_SETUP       420
               `define 		THOLD             60

               `define 		TSTROBE           910
            `else
               `ifdef DYN_BC
                  `define       TOUT_SRAMBUS      100
                  `define       TOUT_DQBUS        100
                  `define       TOUT_CASC         100
   
                  `define       TSETUP            150
                  `define       TCASC_SETUP       300
                  `define       THOLD             50
                  `define       TSTROBE           910
               `else
                  `ifdef DYN_TC
                     `define 	TOUT_SRAMBUS      300
                     `define 	TOUT_DQBUS        300
                     `define 	TOUT_CASC         300

                     `define 	TSETUP            150
                     `define 	TCASC_SETUP       300
                     `define 	THOLD             50
                     `define 	TSTROBE           910
                  `else
                     `define 	TOUT_SRAMBUS      300
                     `define 	TOUT_DQBUS        300 
                     `define 	TOUT_CASC         300

                     `define 	TSETUP            150
                     `define 	TCASC_SETUP       300
                     `define 	THOLD             50
                     `define 	TSTROBE           910
                  `endif // end of !DYN_TC
               `endif // end of !DYN_BC
            `endif // end of !DYN_WC

        `endif // end of !MHZ_83

   `endif   // end of !MHZ_100

`else       // numbers of other CAMS
   `ifdef CAM_2MEG           // numbers for CAM_2MEG
     
      `ifdef MHZ_66  // 66MHz 2Meg
         `define 		T_CLK2X           750
         `define 		T_HIZ_DQ          850
         `define 		T_HIZ_SRAM        650

         `ifdef DYN_WC
            `define 		TOUT_SRAMBUS      900
            `define 		TOUT_DQBUS        900
            `define 		TOUT_CASC         850
 
            `define 		TSETUP            250
            `define 		TCASC_SETUP       420
            `define 		THOLD             60

            `define 		TSTROBE           910
         `else
            `ifdef DYN_BC
               `define 		TOUT_SRAMBUS      100
               `define 		TOUT_DQBUS        100
               `define 		TOUT_CASC         100
   
               `define 		TSETUP            150
               `define 		TCASC_SETUP       300
               `define 		THOLD             50
               `define 		TSTROBE           710
            `else
                `ifdef DYN_TC
                   `define 	TOUT_SRAMBUS      300
                   `define 	TOUT_DQBUS        300
                   `define 	TOUT_CASC         300

                   `define 	TSETUP            150
                   `define 	TCASC_SETUP       300
                   `define 	THOLD             50
                   `define 	TSTROBE           710
                `else
                   `define 	TOUT_SRAMBUS      300
                   `define 	TOUT_DQBUS        300
                   `define 	TOUT_CASC         300

                   `define 	TSETUP            150
                   `define 	TCASC_SETUP       300
                   `define 	THOLD             50
                   `define 	TSTROBE           710
                `endif // end of !DYN_TC
             `endif // end of !DYN_BC
          `endif // end of !DYN_WC

      `else				// 50MHz CAM_2MEG

         `define 		T_CLK2X           1000
         `define 		T_HIZ_DQ          950
         `define 		T_HIZ_SRAM        700

         `ifdef DYN_WC
            `define 		TOUT_SRAMBUS      1000
            `define 		TOUT_DQBUS        1000
            `define 		TOUT_CASC         950

            `define 		TSETUP            250
            `define 		TCASC_SETUP       420
            `define 		THOLD             60

            `define 		TSTROBE           1010
         `else
            `ifdef DYN_BC
               `define 		TOUT_SRAMBUS      100
               `define 		TOUT_DQBUS        100
               `define 		TOUT_CASC         100
   
               `define 		TSETUP            150
               `define 		TCASC_SETUP       300
               `define 		THOLD             50
               `define 		TSTROBE           910
            `else
               `ifdef DYN_TC
                  `define 	TOUT_SRAMBUS      300
                  `define 	TOUT_DQBUS        300
                  `define 	TOUT_CASC         300

                  `define 	TSETUP            150
                  `define 	TCASC_SETUP       300
                  `define 	THOLD             50
                  `define 	TSTROBE           910
               `else
                  `define 	TOUT_SRAMBUS      300
                  `define 	TOUT_DQBUS        300
                  `define 	TOUT_CASC         300

                  `define 	TSETUP            150
                  `define 	TCASC_SETUP       300
                  `define 	THOLD             50
                  `define 	TSTROBE           910
               `endif //end of !DYN_TC
            `endif // end of !DYN_BC
         `endif // end of !DYN_WC

      `endif // end of !MHZ_66 for CAM_2MEG      
   
   `else  // Numbers of CAM_1MEG

     
      `ifdef MHZ_83  // 83MHz  CAM_1MEG
         `define 		T_CLK2X           600
         `define 		T_HIZ_DQ          700
         `define 		T_HIZ_SRAM        600

         `ifdef DYN_WC
            `define 		TOUT_SRAMBUS      750
            `define 		TOUT_DQBUS        750
            `define 		TOUT_CASC         700

            `define 		TSETUP            180
            `define 		TCASC_SETUP       350
            `define 		THOLD             60
            `define 		TSTROBE           760
         `else
            `ifdef DYN_BC
               `define 		TOUT_SRAMBUS      400
               `define 		TOUT_DQBUS        400
               `define 		TOUT_CASC         350
   
               `define 		TSETUP            150
               `define 		TCASC_SETUP       300
               `define 		THOLD             50
               `define 		TSTROBE           760
            `else
                `ifdef DYN_TC
                   `define 	TOUT_SRAMBUS      550
                   `define 	TOUT_DQBUS        550
                   `define 	TOUT_CASC         500

                   `define 	TSETUP            150
                   `define 	TCASC_SETUP       300
                   `define 	THOLD             50
                   `define 	TSTROBE           760
                `else
                   `define 	TOUT_SRAMBUS      400
                   `define 	TOUT_DQBUS        400
                   `define 	TOUT_CASC         350

                   `define 	TSETUP            150
                   `define 	TCASC_SETUP       300
                   `define 	THOLD             50
                   `define 	TSTROBE           760
                `endif // end of !DYN_TC
             `endif // end of !DYN_BC
          `endif // end of !DYN_WC

      `else				// 66MHz CAM_1MEG

         `define 		T_CLK2X           750
         `define 		T_HIZ_DQ          850
         `define 		T_HIZ_SRAM        650

         `ifdef DYN_WC
            `define 		TOUT_SRAMBUS      900
            `define 		TOUT_DQBUS        900
            `define 		TOUT_CASC         850

            `define 		TSETUP            250
            `define 		TCASC_SETUP       420
            `define 		THOLD             60

            `define 		TSTROBE           910
         `else
            `ifdef DYN_BC
               `define 		TOUT_SRAMBUS      600
               `define 		TOUT_DQBUS        600
               `define 		TOUT_CASC         550
   
               `define 		TSETUP            150
               `define 		TCASC_SETUP       300
               `define 		THOLD             50
               `define 		TSTROBE           910
            `else
               `ifdef DYN_TC
                  `define 	TOUT_SRAMBUS      700
                  `define 	TOUT_DQBUS        700
                  `define 	TOUT_CASC         650

                  `define 	TSETUP            150
                  `define 	TCASC_SETUP       300
                  `define 	THOLD             50
                  `define 	TSTROBE           910
               `else
                  `define 	TOUT_SRAMBUS      600
                  `define 	TOUT_DQBUS        600
                  `define 	TOUT_CASC         550

                  `define 	TSETUP            150
                  `define 	TCASC_SETUP       300
                  `define 	THOLD             50
                  `define 	TSTROBE           910
               `endif //end of !DYN_TC
            `endif // end of !DYN_BC
         `endif // end of !DYN_WC

      `endif // end of !MHZ_83 for CAM_1MEG      

   `endif  // end of !CAM_2MEG

`endif // end of !CAM_4MEG


/****************************************************/
// This are hard coded parameters for the model
/****************************************************/

`ifdef CAM_4MEG
  `define  REG_WIDTH         72
  `define  REG_ADDR_WIDTH    7
  `define  CMD_WIDTH         11 
  `define  SADR_WIDTH        24
  `define  INDEX_WIDTH       16
  `define  LOG_ARRAY_SIZE    16  // This value can be changed to make CAM Array small 

`else
   `ifdef CAM_2MEG
       `define  REG_WIDTH         68
       `define  REG_ADDR_WIDTH    6
       `define  CMD_WIDTH         9
       `define  SADR_WIDTH        22
       `define  INDEX_WIDTH       15
       `ifdef MODELSIM
       		`define  LOG_ARRAY_SIZE    10 // This value can be changed to make CAM Array small //changed by HUJ
   	`else 
   		`define  LOG_ARRAY_SIZE    15 // This value can be changed to make CAM Array small 
   	`endif
   
   `else  // CAM_1MEG
       `define  REG_WIDTH         68
       `define  REG_ADDR_WIDTH    6
       `define  CMD_WIDTH         9
       `define  SADR_WIDTH        22
       `define  INDEX_WIDTH       14
       `define  LOG_ARRAY_SIZE    14 // This value can be changed to make CAM Array small

   `endif // end of !CAM_2MEG

`endif // end of !CAM_4MEG

`define   ARRAY_SIZE        (1 << `LOG_ARRAY_SIZE)
`define  FOUR_TIMES_REG_WIDTH  4*`REG_WIDTH
`define  LAST_PARTITION_0_ADDR     ((`ARRAY_SIZE/4) -1)
`define  LAST_PARTITION_1_ADDR				 ((`ARRAY_SIZE/2) -1)
`define  LAST_PARTITION_2_ADDR     ((`ARRAY_SIZE*3/4) -1)
`define  LAST_PARTITION_3_ADDR				  (`ARRAY_SIZE -1)
/*****************************************************/
