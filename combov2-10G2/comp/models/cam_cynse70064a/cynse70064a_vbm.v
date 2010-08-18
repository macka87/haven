/************************************************************************/
/* Cypress Semiconductor Company Confidential                           */
/* Copyright 1999, Cypress Semiconductor. All Rights reserved           */
/* Cypress Semiconductor proprietary source code                        */
/* Permission to use, modify or copy this code is prohibited            */
/* without the express written consent of                               */
/* Cypress Semiconductor                                                */
/* Filename: cynse70064A_VBM.v									*/
/* Release: 1.6 									*/
/* Last Updated: 24th September 2004 HUJ                      							   */
/************************************************************************/
//`include "../cynse70032_064_128.vh"
`define CAM_2MEG 1 //Simulating CYNSE70064: 2Mb device

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

//********************** module added by HUJ *********************************
module cynse70064A		(	CLK2X,
		    	PHS_L,
		    	RST_L,
		    	DQ,
		    	CMDV,
		    	CMD,
		    	LHI,
		    	BHI,
		    	FULI,
		    	ID,
		    	ACK,
		    	EOT,
		    	SSV,
		    	SSF,
		    	CE_L,
		    	WE_L,
		    	OE_L,
		    	ALE_L,
		    	SADR,
		    	FULL,
		    	FULO,
		    	LHO,
		    	BHO
		    	);
//inputs
input 				CLK2X;
input 				PHS_L;
input 				RST_L;
inout [`REG_WIDTH - 1:0] 				DQ;		//data bus
input 		    		CMDV;           // cmd valid
input [`CMD_WIDTH-1:0]   				CMD;            // cmd
input [6:0] 		    		LHI;            // local hit in
input [2:0] 		    		BHI;            // block hit in
input [6:0] 		    		FULI;           // local full in
input [4:0] 		    		ID;             // device id
//outputs
output 		    		ACK;
output 		    		EOT;
output 		    		SSV;
output 		    		SSF;
output 		    		CE_L;
output 		    		WE_L;
output 		    		OE_L;
output 		    		ALE_L;
output [`SADR_WIDTH-1:0] 				SADR;
output 		    		FULL;
output [1:0]		    		FULO;
output [1:0]		    		LHO;
output [2:0]		    		BHO;





brecken_ref_leaf model ( .clk1x_2x(CLK2X),
			 .phs_l(PHS_L),
                         .rst_l(RST_L),
                         .dq(DQ),
                         .cmdv(CMDV),
                         .cmd(CMD),
			 .id(ID),
			 .lhi(LHI),
			 .bhi(BHI),
			 .fuli(FULI),
			 .ref_ack_out(ACK),
                	 		 .ref_eot_out(EOT),
                	 		 .ref_ssv_out(SSV),
                	 		 .ref_ssf_out(SSF),
                	 		 .ref_ce_l_out(CE_L),
                	 		 .ref_we_l_out(WE_L),
                	 		 .ref_oe_l_out(OE_L),
                	 		 .ref_ale_l_out(ALE_L),
                	 		 .ref_sadr_out(SADR),
                	 		 .ref_full_out(FULL),
                			 .ref_fulo_out(FULO),
                			 .ref_lho_out(LHO),
                			 .ref_bho_out(BHO)
			);  //instantiation for the signal names to match data sheet

endmodule
//*********************************************************************************




module brecken_ref_leaf         (
                        // clk_mode,   //by HUJ
			// pll_bypass, //by HUJ
			// cfg_l,      //by HUJ
			 clk1x_2x,
			 phs_l,
                         rst_l,
                         dq,
                         cmdv,
                         cmd,
			 id,
			 lhi,
			 bhi,
			 fuli,
			// test,      //by HUJ
			// high_speed,//by HUJ
			// find_miss,   //by HUJ
			// ref_multihit_out,  //by HUJ
                	 ref_ack_out,
                	 ref_eot_out,
                	 ref_ssv_out,
                	 ref_ssf_out,
                	 ref_ce_l_out,
                	 ref_we_l_out,
                	 ref_oe_l_out,
                	 ref_ale_l_out,
                	 ref_sadr_out,
                	 ref_full_out,
                	 ref_fulo_out,
                	 ref_lho_out,
                	 ref_bho_out

			 );

   parameter D = 1;
   

 //  input           clk_mode;   //by HUJ
 //  input 	   pll_bypass;			 //by HUJ
 //  input 	   cfg_l;			//by HUJ
 //*************** added by HUJ for 2M only****************
     wire      clk_mode;
     wire      pll_bypass;
     wire      cfg_l;
     assign    clk_mode = 0;
     assign    pll_bypass = 0;
     assign    cfg_l = 0;
 //********************************************************  
   
   
   input 	   clk1x_2x;
   input 	   phs_l;
   input 	   rst_l;
   
   inout [`REG_WIDTH - 1:0] dq;             // data bus
   input 		    cmdv;           // cmd valid
   input [`CMD_WIDTH-1:0]   cmd;            // cmd
   input [6:0] 		    lhi;            // local hit in
   input [2:0] 		    bhi;            // block hit in
   input [6:0] 		    fuli;           // local full in
   input [4:0] 		    id;             // device id
  // input 		    test;			//by HUJ
  // input 		    high_speed;			//by HUJ
  // input 		    find_miss;			//by HUJ
  //*************** added by HUJ for 2M only****************
     wire           test;
     wire	          high_speed;
     wire           find_miss;
     assign         test = 0;
     assign         high_speed = 0;
     assign         find_miss = 0;
  //********************************************************
   // These signals are to be verified by REF -- generated by RTL
   // Need to Add the output enable to verify the arbitration

 //  output 		    ref_multihit_out;  //by HUJ 
   output 		    ref_ack_out;
   output 		    ref_eot_out;
   output 		    ref_ssv_out;
   output 		    ref_ssf_out;
   output 		    ref_ce_l_out;
   output 		    ref_we_l_out;
   output 		    ref_oe_l_out;
   output 		    ref_ale_l_out;
   output [`SADR_WIDTH-1:0] ref_sadr_out;
   output 		    ref_full_out;
   output [1:0]		    ref_fulo_out;   //HUJ
   output [1:0]		    ref_lho_out;    //HUJ
   output [2:0]		    ref_bho_out;    //HUJ



   /******************* Reg / Wire Declarations ******************/

   wire 		    reset_l;
   reg 			    srst_pipe0, srst_pipe1, srst_pipe2, srst_pipe3, srst_pipe4,
			    srst_pipe5, srst_pipe6, srst_pipe7;
   reg 			    srst; 
   wire 		    deve, lcam, lram;
   wire [1:0] 		    tlsz, cfg0, cfg1, cfg2, cfg3,cfg4,cfg5,cfg6,cfg7;
   wire [2:0] 		    hlat;
   wire [`LOG_ARRAY_SIZE-1:0] rd_burst_addr, wr_burst_addr;   // ??? Why not 14 bits
   wire [8:0] 		      rd_burst_len, wr_burst_len;
   reg [8:0] 		      running_burst_len;
   reg [`LOG_ARRAY_SIZE-1:0]  running_burst_addr;

   reg [`REG_WIDTH - 1:0]     dq_cycle_dataA, dq_cycle_dataB, dq_cycle_dataC, dq_cycle_dataD;
   `ifdef CAM_1MEG 
   //wire [13:0] dq_address;
   wire [`LOG_ARRAY_SIZE-1:0] dq_address;
   `else 
   wire [`LOG_ARRAY_SIZE-1:0] dq_address;
   `endif
   wire [1:0] 		      dq_pio_target;
   wire [4:0] 		      dq_id;
   wire 		      dq_indirect;
   wire [2:0] 		      dq_ssr_index;
   wire [71:0] 		      dq_int;
 		      
   wire [`REG_ADDR_WIDTH:0]   register_addr;
   wire [`LOG_ARRAY_SIZE-1:0] cam_data_mask_addr;
   reg [`LOG_ARRAY_SIZE-1:0]  cam_data_mask_addr_pipe1;
   

   reg [`LOG_ARRAY_SIZE-1:0]  next_free_addr;
   
   reg [`CMD_WIDTH-1:0]       cmd_cycleA, cmd_cycleB, cmd_cycleC, cmd_cycleD;
   wire [1:0] 		      cmd_op;
   wire 		      parallel ;
   reg [6:0] 		      addr_par_write;
   reg [1:0] 		      cmd_op_pipe1, cmd_op_pipe2;
   reg 			      cmdv_pipe1, cmdv_pipe2;
   wire 		      cmd_burst;
`ifdef CAM_4MEG
   wire [3:0] 		      cmd_global_mask_indexA, cmd_global_mask_indexC;
`else
   wire [2:0] 		      cmd_global_mask_indexA, cmd_global_mask_indexC;
`endif
   
   
   wire [2:0] 		      cmd_sadr;
   wire [2:0] 		      cmd_ssr_index; 
   wire [3:0] 		      cmd_comp_indexA, cmd_comp_indexB;
   wire 		      cmd_search_x72;
   wire 		      cmd_search_x144;
   wire 		      cmd_search_x288;
   reg 			      cmd_search_x288_pipe1, cmd_search_x288_pipe2;
   reg 			      cmd_search_x72_pipe1, cmd_search_x72_pipe2;
   reg 			      cmd_search_x144_pipe1, cmd_search_x144_pipe2;
   wire 		      cmd_learn_x144;

   reg 			      read_op, write_op, search_op1, search_op2, learn_op;
   reg 			      learn_op_pipe1, learn_op_pipe2;
   wire 		      search_op;
   reg 			      search_op_pipe1;
   wire 		      sample_search_x288;
   reg 			      sample_search_x288_pipe1;
   wire 		      sample_search_x144;
   reg 			      sample_search_x144_pipe1;

      wire 		      sample_search_x72;
   reg 			      sample_search_x72_pipe1;
   
   wire 		      indirect_mode;
   wire [`LOG_ARRAY_SIZE-1:0] pio_ssr_index;
   wire 		      pio_ssr_index_valid;
   wire [`REG_WIDTH - 1:0]    global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1;
   wire [`FOUR_TIMES_REG_WIDTH-1:0] global_mask_x288;

   wire 			    cam_data_rd, cam_mask_rd, sram_rd, reg_rd;
   wire 			    cam_data_wr, cam_mask_wr, sram_wr, reg_wr;
   wire 			    learn_data_wr0,  learn_data_wr1;
   wire [`REG_WIDTH - 1:0] 	    learn_comp_0, learn_comp_1;

   wire 			    wr_comp_reg0,  wr_comp_reg1,  wr_comp_reg2,  wr_comp_reg3,
				    wr_comp_reg4,  wr_comp_reg5,  wr_comp_reg6,  wr_comp_reg7,
				    wr_comp_reg8,  wr_comp_reg9,  wr_comp_reg10, wr_comp_reg11,
				    wr_comp_reg12, wr_comp_reg13, wr_comp_reg14, wr_comp_reg15,
            			    wr_comp_reg16, wr_comp_reg17, wr_comp_reg18, wr_comp_reg19,
				    wr_comp_reg20, wr_comp_reg21, wr_comp_reg22, wr_comp_reg23,
				    wr_comp_reg24, wr_comp_reg25, wr_comp_reg26, wr_comp_reg27,
				    wr_comp_reg28, wr_comp_reg29, wr_comp_reg30, wr_comp_reg31;

   wire 			    wr_mask_reg0,  wr_mask_reg1,  wr_mask_reg2,  wr_mask_reg3,
				    wr_mask_reg4,  wr_mask_reg5,  wr_mask_reg6,  wr_mask_reg7,
				    wr_mask_reg8,  wr_mask_reg9,  wr_mask_reg10, wr_mask_reg11,
				    wr_mask_reg12, wr_mask_reg13, wr_mask_reg14, wr_mask_reg15
`ifdef CAM_4MEG
				    ,
				    wr_mask_reg16, wr_mask_reg17, wr_mask_reg18, wr_mask_reg19,
				    wr_mask_reg20, wr_mask_reg21, wr_mask_reg22, wr_mask_reg23,
				    wr_mask_reg24, wr_mask_reg25, wr_mask_reg26, wr_mask_reg27,
				    wr_mask_reg28, wr_mask_reg29, wr_mask_reg30, wr_mask_reg31
`endif
				    ;
   
   

   wire 			    wr_ssr_reg0,   wr_ssr_reg1,   wr_ssr_reg2,   wr_ssr_reg3,
				    wr_ssr_reg4,   wr_ssr_reg5,   wr_ssr_reg6,   wr_ssr_reg7;

   wire 			    wr_cmd_reg,    wr_rd_bst_reg, wr_wr_bst_reg, wr_nfa_reg; 

   wire [`REG_WIDTH - 1:0] 	    wr_comp_value;
   wire [`REG_WIDTH - 1:0] 	    wr_ssr_value;

   reg [2:0] 			    cmd_state, n_cmd_state;
   reg 				    read_now,  write_now, write_now_sram;

   reg [`INDEX_WIDTH-1:0] 	    pre_search_success_index;

   
   reg [`LOG_ARRAY_SIZE-1:0] 	    pre_search_success_index_0, pre_search_success_index_1;
   reg [`LOG_ARRAY_SIZE-1:0] 	    pre_search_success_index_64;
   wire [`LOG_ARRAY_SIZE-1:0] 	    search_success_index;
   wire [`LOG_ARRAY_SIZE-1:0] 	    ssr_reg_value;
   reg 				    second_cycle;
   reg 				    inc_burst_addr;
   reg 				    update_rd_bst_reg, update_wr_bst_reg;

   wire 				    ref_multihit;
   reg 				    multihit;
   
   
   reg 				    ref_ack,  ref_eot;
   wire 			    ref_ssv,  ref_ssf;
   wire	[1:0]			    ref_lho;
   reg 	[2:0]			    ref_bho;		//bit changed by HUJ
   reg 	[1:0]			    ref_fulo;		//bit changed by HUJ
   reg				     ref_full;  
   wire 			    ref_ce_l, ref_we_l, ref_oe_l, ref_ale_l;
   reg [`REG_WIDTH - 1:0] 	    ref_dq;
   wire [`SADR_WIDTH-1:0] 	    ref_sadr;

   reg 				    ref_oe_dq,   ref_oe_ack,  ref_oe_eot;
   wire 			    ref_oe_ssv,  ref_oe_ssf;
   wire 			    ref_oe_ce_l, ref_oe_we_l, ref_oe_oe_l, ref_oe_ale_l, ref_oe_sadr;

   reg 				    verify_read;
   wire 			    verify_sadr;

   reg [3:0] 			    sram_cmd_pipe1, sram_cmd_pipe2, sram_cmd_pipe3,
				    sram_cmd_pipe4, sram_cmd_pipe5, sram_cmd_pipe6;

   reg 				    sram_oe_pipe1, sram_oe_pipe2, sram_oe_pipe3,
				    sram_oe_pipe4, sram_oe_pipe5, sram_oe_pipe6;


   wire [3:0] 			    sram_op; 

   reg 				    sram_cmd_pending_pipe1, sram_cmd_pending_pipe2, sram_cmd_pending_pipe3,
				    sram_cmd_pending_pipe4, sram_cmd_pending_pipe5, sram_cmd_pending_pipe6;

   wire 			    sram_op_pending;

   reg [`SADR_WIDTH-1:0] 	    ext_sram_addr,       ext_sram_addr_pipe2, ext_sram_addr_pipe3,
				    ext_sram_addr_pipe4, ext_sram_addr_pipe5, ext_sram_addr_pipe6;

   reg 				    pre_lho;
   reg 				    pre_lho_0, pre_lho_1;
   reg				    partition272_pre_lho_0, partition272_pre_lho_1;  //added by HUJ
`ifdef CAM_4MEG
   
   wire [21:0] 			    search_result;
   reg [21:0] 			    search_result_pipe2, search_result_pipe3, search_result_pipe4, 
				    search_result_pipe5, search_result_pipe6;
`else
   wire [20:0] 			    search_result;
   reg [20:0] 			    search_result_pipe2, search_result_pipe3, search_result_pipe4, 
				    search_result_pipe5, search_result_pipe6;
`endif
   reg 				    multihit_pipe2, multihit_pipe3, multihit_pipe4;
 				    
   wire [2:0] 			    ssv_ssf_pipe0;
   reg [2:0] 			    ssv_ssf_pipe1, ssv_ssf_pipe2, ssv_ssf_pipe3, ssv_ssf_pipe4,
				    ssv_ssf_pipe5, ssv_ssf_pipe6, ssv_ssf_pipe7;

   wire 			    global_miss;

   reg [2:0] 			    read_transaction;
   reg [`REG_WIDTH - 1:0] 	    dq_latched;

   reg [3:0] 			    sram_cycle_latency;
   reg 				    inc_sram_cycle_count;

   reg [`REG_WIDTH - 1:0] 	    cam_rd_data0, cam_rd_data1, cam_rd_data2, cam_rd_data3;
   reg 				    cbit0,        cbit1, 	    cbit2,	  cbit3;
   reg 				    cbit;
   reg 				    cam_data_wr_pipe1, cam_data_wr_pipe2;

   wire [`REG_WIDTH - 1:0] 	    last_entry, 	         last_entry_minus_1,      
				    last_entry_minus_2,      last_entry_minus_3;

   wire 			    last_entry_cbit,         last_entry_cbit_minus_1, 
 				    last_entry_cbit_minus_2, last_entry_cbit_minus_3;

   wire 			    last_cfg_mode_144, 	 last_cfg_mode_288;
   wire			    partition_0_reserved, partition_1_reserved, partition_2_reserved, partition_3_reserved;  //internal signal added by HUJ

   reg 				    calc_nfa_done;

   /******************* Registers Definitions ********************/

   reg [`REG_WIDTH - 1:0] 	    comp_reg0,  comp_reg1,  comp_reg2,  comp_reg3,
				    comp_reg4,  comp_reg5,  comp_reg6,  comp_reg7,
				    comp_reg8,  comp_reg9,  comp_reg10, comp_reg11,
				    comp_reg12, comp_reg13, comp_reg14, comp_reg15,
				    comp_reg16, comp_reg17, comp_reg18, comp_reg19,
				    comp_reg20, comp_reg21, comp_reg22, comp_reg23,
				    comp_reg24, comp_reg25, comp_reg26, comp_reg27,
				    comp_reg28, comp_reg29, comp_reg30, comp_reg31;

   reg [`REG_WIDTH - 1:0] 	    mask_reg0,  mask_reg1,  mask_reg2,  mask_reg3,
				    mask_reg4,  mask_reg5,  mask_reg6,  mask_reg7,
				    mask_reg8,  mask_reg9,  mask_reg10, mask_reg11,
				    mask_reg12, mask_reg13, mask_reg14, mask_reg15
`ifdef CAM_4MEG
				    ,
				    mask_reg16, mask_reg17, mask_reg18, mask_reg19,
				    mask_reg20, mask_reg21, mask_reg22, mask_reg23,
				    mask_reg24, mask_reg25, mask_reg26, mask_reg27,
				    mask_reg28, mask_reg29, mask_reg30, mask_reg31
`endif
				    ;
   

   

   reg [`REG_WIDTH - 1:0] 	    ssr_reg0,   ssr_reg1,   ssr_reg2,   ssr_reg3,
				    ssr_reg4,   ssr_reg5,   ssr_reg6,   ssr_reg7;

   reg [`REG_WIDTH - 1:0] 	    cmd_reg, cmd_reg_pipe1, cmd_reg_pipe2;

   reg [`REG_WIDTH - 1:0] 	    rd_bst_reg;

   reg [`REG_WIDTH - 1:0] 	    wr_bst_reg;

   // NOTE:  update after each WR or LRN command
   reg [`REG_WIDTH - 1:0] 	    nfa_reg;

   /********************* MEMORY DECLARATION **********************/

   reg [`REG_WIDTH - 1:0] 	    cam_data_array[0:`ARRAY_SIZE-1];
   reg [`REG_WIDTH - 1:0] 	    cam_mask_array[0:`ARRAY_SIZE-1];

   wire [`REG_WIDTH - 1:0] 	    cam_rd_mod_wr_data;
   reg [`REG_WIDTH - 1:0] 	    cam_rd_mod_wr_data_pipe1;

   reg [`LOG_ARRAY_SIZE:0] 	    cam_data_mask_index;	// Make it 1 bit wider
   reg [8:0] 			    cambit;
   reg [`REG_WIDTH - 1:0] 	    cam_data_xREG_WIDTH_0,  cam_mask_xREG_WIDTH_0,  combined_mask_xREG_WIDTH_0 ;
   reg [`REG_WIDTH - 1:0] 	    cam_data_xREG_WIDTH_1,  cam_mask_xREG_WIDTH_1,  combined_mask_xREG_WIDTH_1 ;
   reg [`FOUR_TIMES_REG_WIDTH-1:0]  cam_data_x288,   cam_mask_x288,   combined_mask_x288;

   reg 	[1:0]			    ref_lho_pipe1, ref_lho_pipe2;
   reg 				    ref_multihit_pipe1, ref_multihit_pipe2;
   
   wire 			    local_hit;
   reg [1:0] 			    cfg_info[0:7];

   

   /************************* CODE BEGINS *************************/

   /******************* Tristate outputs *************************/

   //wire 			    ref_ack_out_pre;
   reg 			    ref_ack_out_pre;
   wire 			    ref_ack_out_pre_internal;
   //reg 			    ref_ack_out_pre_internal;
   //wire 			    ref_ack_out;
   reg  			    ref_ack_out;
   //wire 			    ref_ack_out_internal;
   reg  			    ref_ack_out_internal;
   //wire 			    ref_eot_out;
   reg  			    ref_eot_out;
   //wire 			    ref_ssv_out;
   reg 			    ref_ssv_out;
   //wire 			    ref_ssf_out;
   reg 			    ref_ssf_out;
   //wire 			    ref_ce_l_out;
   reg 			    ref_ce_l_out;
   //wire 			    ref_we_l_out;
   reg 			    ref_we_l_out;
   //wire 			    ref_oe_l_out;
   reg 			    ref_oe_l_out;
   //wire 			    ref_ale_l_out;
   reg 			    ref_ale_l_out;
   //wire [`SADR_WIDTH-1:0] 	    ref_sadr_out;
   reg [`SADR_WIDTH-1:0] 	    ref_sadr_out;
   wire 			    ref_full_out;
   wire [1:0]			    ref_fulo_out;  //bit changed by HUJ
   wire [1:0]			    ref_lho_out;   //bit changed by HUJ
   wire [2:0]			    ref_bho_out;   //bit changed by HUJ
   wire 			    ref_multihit_out;
  
//-------------------------------------------------------
   //wire [`SADR_WIDTH-1:0]           dummy_ref_sadr_out;
   reg [`SADR_WIDTH-1:0]           dummy_ref_sadr_out;
   wire [`REG_WIDTH - 1:0]          dummy_ref_dq;
 reg                            clk_ref; 

/*****************************
   assign # `TOUT_SRAMBUS 	    ref_ssv_out	=  ref_oe_ssv  ? ref_ssv : 1'bz;
   assign # `TOUT_SRAMBUS 	    ref_ssf_out	=  ref_oe_ssf  ? ref_ssf : 1'bz;
   assign # `TOUT_SRAMBUS 	    ref_ce_l_out	=  ref_oe_ce_l  ? ref_ce_l : 1'bz;
   assign # `TOUT_SRAMBUS 	    ref_we_l_out	=  ref_oe_we_l  ? ref_we_l : 1'bz;
   assign # `TOUT_SRAMBUS 	    ref_oe_l_out	=  ref_oe_oe_l  ? ref_oe_l : 1'bz;
   assign # `TOUT_SRAMBUS 	    ref_ale_l_out	=  ref_oe_ale_l  ? ref_ale_l : 1'bz;
   assign # `TOUT_SRAMBUS 	    ref_sadr_out	=  ref_oe_sadr  ? ref_sadr : `SADR_WIDTH'bz;

   assign 			    ref_ack_out_pre	=  ref_oe_ack ? ref_ack : 1'bz;
   reg internal_high_z;
   assign                 internal_high_z     = reg_oe_ack ? #T_HIZ_DQ 1'bz : 1'bz;

   assign  			    ref_ack_out_pre	=  ref_oe_ack ? ref_ack : internal_high_z;

   assign # `TOUT_DQBUS 	    ref_ack_out = ref_ack_out_pre;
   assign # `TOUT_DQBUS 	    ref_eot_out	=  ref_oe_eot ? ref_eot : 1'bz;
   assign # `TOUT_DQBUS 	    dq  = (ref_oe_dq) ? ref_dq : `REG_WIDTH'bz;

   assign # `TOUT_CASC 		    ref_full_out = ~rst_l? 0 : ref_full;
   assign # `TOUT_CASC 		    ref_fulo_out = ~rst_l? 0 : ref_fulo;
   assign # `TOUT_CASC 		    ref_lho_out =  ~rst_l? 0 : ref_lho;
   assign # `TOUT_CASC 		    ref_bho_out =  ~rst_l? 0 : ref_bho;
   assign # `TOUT_CASC 		    ref_multihit_out =  ~rst_l? 0 : ref_multihit;
   
   assign 			    dq_int = cfg_l?dq:{4'b000,dq[67:0]};
****************************/

   always @(posedge ref_oe_ack or negedge ref_oe_ack or ref_ack)
      begin
      if ( ref_oe_ack == 0)
         begin
           #(`T_HIZ_DQ - (D*2) ) ;
           ref_ack_out  = 1'bz ; 
         end
      else
          begin
          # (`TOUT_DQBUS - (D*2) );
          ref_ack_out = ref_ack ;
          end 
      end

      always @(posedge ref_oe_ack or negedge ref_oe_ack )
      begin
      if ( ref_oe_ack == 0)
         begin
           #(`T_HIZ_DQ - (D*2) ) ;
           ref_ack_out_internal  = 1'b0 ;
         end
      else
          begin
          #( `TOUT_DQBUS - (D*2) );
          ref_ack_out_internal = ref_ack ;
          end
      end


   assign 			    ref_ack_out_pre_internal	=  ref_oe_ack ? ref_ack : 1'b0;
 
   //assign # `TOUT_DQBUS             ref_ack_out = ref_ack_out_pre;
   //assign # `TOUT_DQBUS 	    ref_ack_out_internal = ref_ack_out_pre_internal;
 
   assign                           dq_int = cfg_l?dq:{4'b000,dq[67:0]};
 
   //wire                 dummy_ref_ssv_out =  ref_oe_ssv  ? ref_ssv : 1'bz;

   always @( ref_oe_ssv or  ref_ssv ) 
      begin
      #D;
      if ( ref_oe_ssv == 0)
         begin
           #(`T_HIZ_SRAM - (D*3));
           ref_ssv_out  = 1'bz ;
         end
      else
          begin
          #( `TOUT_SRAMBUS- (D*3));
          ref_ssv_out = ref_ssv;
          end
      end

   //wire                 dummy_ref_ssf_out =  ref_oe_ssf  ? ref_ssf : 1'bz;

   //always @(posedge ref_oe_ssf or negedge ref_oe_ssf ) 
   always @( ref_oe_ssf or ref_ssf ) 
      begin
      #D;
      if ( ref_oe_ssf == 0)
         begin
           #(`T_HIZ_SRAM - (D*3));
           ref_ssf_out  = 1'bz ;
         end
      else
          begin
          # (`TOUT_SRAMBUS -(D*3));
          ref_ssf_out = ref_ssf;
          end
      end

   //wire                 dummy_ref_ce_l_out        =  ref_oe_ce_l  ? ref_ce_l : 1'bz;
   //always @(posedge ref_oe_ce_l or negedge ref_oe_ce_l )
   always @( ref_oe_ce_l or ref_ce_l )
      begin
      #D;
      if ( ref_oe_ce_l == 0)
         begin
           #(`T_HIZ_SRAM - (D*3));
           ref_ce_l_out  = 1'bz ;
         end
      else
          begin
          # (`TOUT_SRAMBUS- (D*3));
          ref_ce_l_out = ref_ce_l;
          end
      end

   //wire                 dummy_ref_we_l_out        =  ref_oe_we_l  ? ref_we_l : 1'bz;
   //always @(posedge ref_oe_we_l or negedge ref_oe_we_l )
   always @(ref_oe_we_l or  ref_we_l )
      begin
      #D;
      if ( ref_oe_we_l == 0)
         begin
           #(`T_HIZ_SRAM -(D*3));
           ref_we_l_out  = 1'bz ;
         end
      else
          begin
          # (`TOUT_SRAMBUS- (D*3));
          ref_we_l_out = ref_we_l;
          end
      end

   //wire                 dummy_ref_oe_l_out        =  ref_oe_oe_l  ? ref_oe_l : 1'bz;
   //always @(posedge ref_oe_oe_l or negedge ref_oe_oe_l )
   always @(ref_oe_oe_l or ref_oe_l )
      begin
      #D;
      if ( ref_oe_oe_l == 0)
         begin
           #(`T_HIZ_SRAM - (D*3));
           ref_oe_l_out  = 1'bz ;
         end
      else
          begin
          # (`TOUT_SRAMBUS- (D*3));
          ref_oe_l_out = ref_oe_l;
          end
      end

   //wire                 dummy_ref_ale_l_out       =  ref_oe_ale_l  ? ref_ale_l : 1'bz;

   //always @(posedge ref_oe_ale_l or negedge ref_oe_ale_l )
   always @(ref_oe_ale_l or ref_ale_l )
      begin
      #D;
      if ( ref_oe_ale_l == 0)
         begin
           #(`T_HIZ_SRAM - (D*3));
           ref_ale_l_out  = 1'bz ;
         end
      else
          begin
          # (`TOUT_SRAMBUS- (D*3));
          ref_ale_l_out = ref_ale_l;
          end
      end


  // assign               dummy_ref_sadr_out        =  ref_oe_sadr  ? ref_sadr : `SADR_WIDTH'bz;

   //always @(posedge ref_oe_sadr or negedge ref_oe_sadr )
   always @(ref_oe_sadr or ref_sadr )
      begin
      #D;
      if ( ref_oe_sadr == 0)
         begin
           #(`T_HIZ_SRAM - (D*3));
           ref_sadr_out  <= `SADR_WIDTH'bz;
         end
      else
         begin
          # (`TOUT_SRAMBUS - (D*3));
          ref_sadr_out <= ref_sadr;
         end
      end
 
 
   //wire                 dummy_ref_eot_out =  ref_oe_eot ? ref_eot : 1'bz;
    //always @(posedge ref_oe_eot or negedge ref_oe_eot )
    always @(ref_oe_eot or ref_eot )
      begin
      if ( ref_oe_eot == 0)
         begin
           #(`T_HIZ_DQ - (D*2));
          ref_eot_out  = 1'bz ;
         end
      else
          begin
          #(`TOUT_DQBUS - (D*2));             
         ref_eot_out = ref_eot ;
          end
      end

   assign               dummy_ref_dq  = (ref_oe_dq) ? ref_dq : `REG_WIDTH'bz;
 
   wire                 dummy_ref_full_out = ~rst_l? 0 : ref_full;
   wire [1:0]           dummy_ref_fulo_out = ~rst_l? 0 : ref_fulo;   //bit changed by HUJ
   wire [1:0]           dummy_ref_lho_out =  ~rst_l? 0 : ref_lho;    //bit changed by HUJ
   wire [2:0]           dummy_ref_bho_out =  ~rst_l? 0 : ref_bho;    //bit changed by HUJ
   wire                 dummy_ref_multihit_out =  ~rst_l? 0 : ref_multihit;
 
  // assign # `TOUT_SRAMBUS           ref_ssv_out         =  dummy_ref_ssv_out;
  // assign # `TOUT_SRAMBUS           ref_ssf_out         =  dummy_ref_ssf_out;
  // assign # `TOUT_SRAMBUS           ref_ce_l_out        =  dummy_ref_ce_l_out;
  // assign # `TOUT_SRAMBUS           ref_we_l_out        =  dummy_ref_we_l_out;
  // assign # `TOUT_SRAMBUS           ref_oe_l_out        =  dummy_ref_oe_l_out;
  // assign # `TOUT_SRAMBUS           ref_ale_l_out       =  dummy_ref_ale_l_out;
  // assign # `TOUT_SRAMBUS           ref_sadr_out        =  dummy_ref_sadr_out;
 
  // assign # `TOUT_DQBUS             ref_eot_out         =  dummy_ref_eot_out;
   assign # `TOUT_DQBUS             dq                  =  dummy_ref_dq;
 
   assign # (`TOUT_CASC - (D*2))           ref_full_out        = dummy_ref_full_out;
   assign # (`TOUT_CASC - (D*2))           ref_fulo_out        = dummy_ref_fulo_out;
   assign # (`TOUT_CASC - (D*2))           ref_lho_out         = dummy_ref_lho_out;
   assign # (`TOUT_CASC - (D*2))           ref_bho_out         = dummy_ref_bho_out;
   assign # (`TOUT_CASC - (D*2))           ref_multihit_out    = dummy_ref_multihit_out;
 
//-------------------------------------------------------------------------------------


   // CLK == ???

   wire 			    clk2x;
   wire 			    phs_l;
   reg 				    clk;
 //  reg 			    clk_ref;
   

   always @(posedge clk1x_2x or negedge clk1x_2x)
     begin
	if (clk_mode ==1)
	  begin
	     clk_ref = clk1x_2x;
       	     #D clk = clk1x_2x;
	  end
	else
	  begin
	     if (clk1x_2x == 1)
	       begin
		  clk_ref = ~phs_l;
		  #D clk = ~phs_l;
	       end
	  end // else: !if(clk_mode ==1)
	

     end
   
   

   // ???


   wire #(2*D) 			    clk_dly  = clk;
   wire [6:0] 			    #(2*D) lhi_dly  = lhi;
   wire [2:0] 			    #(2*D) bhi_dly  = bhi;
   wire [6:0] 			    #(2*D) fuli_dly = fuli;

   wire    setupchecker=  ~ ref_ack_out_pre_internal;
   wire    holdchecker =  ~ ref_ack_out_internal;
   //wire 			    setupchecker = phs_l & ~ref_ack_out_pre;
   //wire 			    holdchecker = ~phs_l & ~ref_ack_out;
  reg setup_check_edge, hold_chek_edge,cascade_check_edge; 
  
  // This logic is to skip 3 clocks for checking timings
  reg clk_over_1;
  reg first_clk_over ;
  reg phs_over;
  reg [1:0] counter;
  reg first_neg_edge;
  always @(clk1x_2x )
    begin
         if ( clk1x_2x == 1'b0 && ~first_neg_edge )  
            begin
            counter <= 0;
            first_neg_edge <= #D 1'b1;
            end
         else
            begin
            if (first_neg_edge !== 1'b1)
               first_neg_edge <= 1'b0; 
            if(first_neg_edge == 1) 
               counter <= #D counter +1;
            end
    end
  always @(posedge clk1x_2x)
   begin
     if ((counter == 2'b10 && first_clk_over == 1'b0 ) | (first_clk_over == 1'b1))
       first_clk_over = 1'b1;
     else
       first_clk_over = 1'b0;
   end
  always @(posedge clk1x_2x )
   begin
     if (((counter == 2'b10) && (phs_over == 1'b0) && (phs_l == 1'b1)) | phs_over == 1'b1 )
       phs_over = 1'b1;
     else
       phs_over = 1'b0;
   end

   always @(clk1x_2x )
   begin
      if(clk1x_2x == 1'b0 && first_clk_over == 1'b1)
        begin
          setup_check_edge = 1'b0;
          hold_chek_edge = 1'b0;
          cascade_check_edge = 1'b0; 
      end
      else
        begin
        if ( clk_mode == 1'b1 && first_clk_over == 1'b1)
          begin
          setup_check_edge = 1'b1;
          hold_chek_edge = 1'b1;
          cascade_check_edge = 1'b1;
          end
        else
          begin
           if(phs_l == 1'b0 && first_clk_over == 1'b1)
              begin
               setup_check_edge = 1'b1;
               hold_chek_edge = 1'b1;
               cascade_check_edge = 1'b1;
             end
          end
        end
   end
wire setup_check1 = setup_check_edge; 
wire hold_check1 = setup_check_edge; 
wire cascade_check1 = cascade_check_edge;

wire first_phs_over =  phs_over;         
`ifdef BEH_SIM
   // find out if ifndef exists
`else 
    	specify
	   $setup (dq, posedge setup_check1  &&& setupchecker, `TSETUP);
	   $hold (posedge hold_check1  &&& holdchecker, dq, `THOLD);
	   $setup (cmd , posedge setup_check1 , `TSETUP);
	   $hold ( posedge hold_check1, cmd, `THOLD);
	   $setup (cmdv,posedge  setup_check1,`TSETUP);
	   $hold (posedge hold_check1, cmdv, `THOLD);
	   $setup (posedge clk1x_2x &&& first_phs_over, phs_l,`TSETUP);
	   $hold (phs_l,posedge clk1x_2x &&& first_phs_over, `THOLD);
	   $setup (posedge setup_check1 , rst_l,`TSETUP);
	   $hold (posedge hold_check1,rst_l,`THOLD);
	   $setup (lhi , posedge cascade_check1, `TCASC_SETUP);
	   $hold (posedge cascade_check1, lhi, `THOLD);
	   $setup (bhi , posedge cascade_check1, `TCASC_SETUP);
	   $hold (posedge cascade_check1, bhi, `THOLD);
	   $setup (fuli ,posedge  cascade_check1, `TCASC_SETUP);
	   $hold (posedge cascade_check1,  fuli, `THOLD);
   	endspecify
         
`endif   

   // Register Decode

   // Need to cycle pipe to match with RTL 
   always @(posedge clk) cmd_reg_pipe1 <= #D cmd_reg;
   always @(posedge clk) 
     begin
	cmd_reg_pipe2 <= #D cmd_reg_pipe1;
	cfg_info[0] <= #D cmd_reg_pipe1[10:9];
	cfg_info[1] <= #D cmd_reg_pipe1[12:11];
	cfg_info[2] <= #D cmd_reg_pipe1[14:13];
	cfg_info[3] <= #D cmd_reg_pipe1[16:15];
	cfg_info[4] <= #D cmd_reg_pipe1[18:17];
	cfg_info[5] <= #D cmd_reg_pipe1[20:19];
	cfg_info[6] <= #D cmd_reg_pipe1[22:21];
	cfg_info[7] <= #D cmd_reg_pipe1[24:23];
	
     end
   

   always @(posedge clk) srst_pipe0 <= #D (wr_cmd_reg & dq_int[0]);
   always @(posedge clk) srst_pipe1 <= #D srst_pipe0;
   always @(posedge clk) srst_pipe2 <= #D srst_pipe1;
   always @(posedge clk) srst_pipe3 <= #D srst_pipe2;
   always @(posedge clk) srst_pipe4 <= #D srst_pipe3;
   always @(posedge clk) srst_pipe5 <= #D srst_pipe4;
   always @(posedge clk) srst_pipe6 <= #D srst_pipe5;
   always @(posedge clk) srst_pipe7 <= #D srst_pipe6;

   always @(posedge clk)
     if (~rst_l | (srst_pipe0 | srst_pipe1 | srst_pipe2 | srst_pipe3 |srst_pipe4 |
		   srst_pipe5 | srst_pipe6 | srst_pipe7)) 
       srst <= #D 1'b1;
     else
       srst <= #D 1'b0;

   assign 			    reset_l = (rst_l & ~srst);

   //assign  srst = cmd_reg_pipe2[0];          // Software Reset           ???

   assign 			    deve = cmd_reg_pipe2[1];          // Device Enable            ???
   assign 			    tlsz = cmd_reg_pipe2[3:2];        // Table Size
   assign 			    hlat = cmd_reg_pipe2[6:4];        // Latency of SFG and SVD
   assign 			    lcam = cmd_reg_pipe2[7];          // Last Cam in table
   assign 			    lram = cmd_reg_pipe2[8];          // Last Cam on SRAM Bus
   assign 			    cfg0 = cmd_reg_pipe2[10:9];       // Table Configuration -- Octant 0
   assign 			    cfg1 = cmd_reg_pipe2[12:11];      // Table Configuration -- Octant 1
   assign 			    cfg2 = cmd_reg_pipe2[14:13];      // Table Configuration -- Octant 2
   assign 			    cfg3 = cmd_reg_pipe2[16:15];      // Table Configuration -- Octant 3
`ifdef CAM_4MEG
   assign 			    cfg4 = cmd_reg_pipe2[18:17];      // Table Configuration -- Octant 4
   assign 			    cfg5 = cmd_reg_pipe2[20:19];      // Table Configuration -- Octant 5
   assign 			    cfg6 = cmd_reg_pipe2[22:21];      // Table Configuration -- Octant 6
   assign 			    cfg7 = cmd_reg_pipe2[24:23];      // Table Configuration -- Octant 7
`endif
   


   
   //    

   assign 			    rd_burst_len  = rd_bst_reg[27:19];
   assign 			    rd_burst_addr = rd_bst_reg[`LOG_ARRAY_SIZE-1:0] ;
   assign 			    wr_burst_len  = wr_bst_reg[27:19];
   assign 			    wr_burst_addr = wr_bst_reg[`LOG_ARRAY_SIZE-1:0] ;

   // DQ bus Decode for RD and WR operations

   always @(posedge clk_ref or negedge clk_ref)
     if (~reset_l | second_cycle)
       begin
	  second_cycle =  1'b0;
       end
     else if(cmdv & ~second_cycle & clk_ref)
       begin
	  second_cycle =  1'b1;
       end
     else
       begin
	  second_cycle =  1'b0;
       end

   always @(posedge clk_ref or negedge clk_ref)
       begin
       #D;
       if (clk_ref == 1)
       cmd_search_x288_pipe1 <=  (cmd_search_x288 & search_op1);
       else 
       cmd_search_x288_pipe1 <= 0;
       end
   always @(posedge clk_ref or negedge clk_ref) cmd_search_x288_pipe2 <= #D cmd_search_x288_pipe1;
   assign sample_search_x288 = (cmd_search_x288_pipe1 | cmd_search_x288_pipe2);
   always @(posedge clk) sample_search_x288_pipe1 <= #D sample_search_x288;
`ifdef CAM_4MEG
   always @(posedge clk_ref or negedge clk_ref) 
    begin
    #D;
    cmd_search_x144_pipe1 <=  (cmd_search_x144 & search_op1);
    end
   always @(posedge clk_ref or negedge clk_ref) cmd_search_x144_pipe2 <= #D cmd_search_x144_pipe1;
   assign sample_search_x144 = (cmd_search_x144_pipe1 | cmd_search_x144_pipe2);


   always @(posedge clk_ref or negedge clk_ref)
      begin
      #D;
      cmd_search_x72_pipe1 <=  (cmd_search_x72 & search_op1);
      end
   always @(posedge clk_ref or negedge clk_ref) cmd_search_x72_pipe2 <= #D cmd_search_x72_pipe1;
   assign sample_search_x72 = (cmd_search_x72_pipe1 | cmd_search_x72_pipe2);
`endif   
   always @(posedge clk_ref or negedge clk_ref   or second_cycle )//or dq_int)

     if (~reset_l)
       begin
	  dq_cycle_dataA <= #D `REG_WIDTH'h0;
	  dq_cycle_dataB <= #D `REG_WIDTH'h0;
	  dq_cycle_dataC <= #D `REG_WIDTH'h0;       // Only for SRCH x288 mode
	  dq_cycle_dataD <= #D `REG_WIDTH'h0;       // Only for SRCH x288 mode
	  cmd_cycleA     <= #D  9'h0;
	  cmd_cycleB     <= #D  9'h0;
	  cmd_cycleC     <= #D  9'h0;	// Only for SRCH x288 mode
	  cmd_cycleD     <= #D  9'h0;	// Only for SRCH x288 mode
       end
     else if (cmdv)
       begin
	  if (sample_search_x288)
            begin
               if (~second_cycle)
 		 begin
		    dq_cycle_dataC <= #D dq_int;
		    cmd_cycleC     <= #D cmd;
		 end
               else
		 begin
		    dq_cycle_dataD <= #D dq_int;
		    cmd_cycleD     <= #D cmd;
		 end
            end
	  else
            begin
               if (~second_cycle)
		 begin
		    dq_cycle_dataA <= #D dq_int;
		    cmd_cycleA     <= #D cmd;
		 end
               else 
                  if ( second_cycle == 1'b1 )
     		   begin
		    dq_cycle_dataB <= #D dq_int;
		    cmd_cycleB     <= #D cmd;
		   end
            end
       end
     else
       begin
	  dq_cycle_dataA <= #D dq_cycle_dataA;
	  dq_cycle_dataB <= #D dq_cycle_dataB;
	  dq_cycle_dataC <= #D dq_cycle_dataC;
	  dq_cycle_dataD <= #D dq_cycle_dataD;
	  cmd_cycleA     <= #D cmd_cycleA;
	  cmd_cycleB     <= #D cmd_cycleB;
	  cmd_cycleC     <= #D cmd_cycleC;
	  cmd_cycleD     <= #D cmd_cycleD;
       end

   // Latch at cycle A or B ???
   `ifdef CAM_1MEG
      //assign  dq_address     = dq_cycle_dataB[13:0];        // Use 18:14 only for SRAM
      assign  dq_address     = dq_cycle_dataB[`LOG_ARRAY_SIZE-1:0];        // Use 18:14 only for SRAM
   `else
      assign   dq_address     =  dq_cycle_dataB[`LOG_ARRAY_SIZE-1:0];        // Use 18:14 only for SRAM
   `endif 
   assign  dq_pio_target  =  dq_cycle_dataB[20:19];       // Tells us what to access
   assign  dq_id          =  dq_cycle_dataB[25:21];
   assign  dq_ssr_index   =  dq_cycle_dataB[28:26];
   assign  dq_indirect    =  dq_cycle_dataB[29];

   // CMD bus Decode for SRCH and LRN opereations

   assign  cmd_op                 = cmd_cycleA[1:0];
   assign  cmd_burst              = cmd_cycleA[2];         // For RD, WR
   `ifdef CAM_4MEG 
assign parallel = cmd_cycleA[9]; 
`else 
assign parallel = 1'b0; 
`endif 


`ifdef CAM_4MEG
   
   assign  cmd_global_mask_indexA = {cmd_cycleA[10],cmd_cycleA[5:3]};       // For WR, SRCH
   assign  cmd_global_mask_indexC = {cmd_cycleC[10],cmd_cycleC[5:3]};       // For SRCH x288
  assign  cmd_search_x144             = cmd_cycleA[9] & ~cmd_cycleA[2];
   assign  cmd_search_x72               = ~cmd_cycleA[9] & ~cmd_cycleA[2];
`else
   assign  cmd_global_mask_indexA = cmd_cycleA[5:3];       // For WR, SRCH
   assign  cmd_global_mask_indexC = cmd_cycleC[5:3];       // For SRCH x288
   assign  cmd_search_x144             =  ~cmd_cycleA[2];
   assign  cmd_search_x72              =  ~cmd_cycleA[2];
`endif
   
   assign  cmd_sadr               = cmd_cycleA[8:6];       // For WR, SRCH, LRN
   assign  cmd_ssr_index          = cmd_cycleB[8:6];       // For SRCH
   assign  cmd_comp_indexA        = cmd_cycleA[5:2];       // For LRN
   assign  cmd_comp_indexB        = cmd_cycleB[5:2];       // For SRCH, LRN
   assign  cmd_search_x288	       = cmd_cycleA[2];		// For SRCH x288 original code
  // assign  cmd_search_x288	       = cmd_cycleA[2] & ~cmd_cycleB[2];		// For SRCH x288
   
   assign  cmd_learn_x144	       = cmd_cycleB[6];		// For LRN  x144

   /*
    assign  search_op     = (((cfg !== 2'b10) & search_op1) |
    ((cfg === 2'b10) & search_op2));
    */

   assign  search_op     = ((search_op1 & ~cmd_search_x288) | 
			    (search_op2 &  cmd_search_x288));

   assign  indirect_mode = (dq_indirect & ((cmd_op == 2'h0) | (cmd_op == 2'h1)));	// Only for Rd/Wr 

   assign  cam_data_rd = (read_now  & (dq_pio_target == 2'b00));
   assign  cam_mask_rd = (read_now  & (dq_pio_target == 2'b01));
   assign  sram_rd     = (read_now  & (dq_pio_target == 2'b10));
   assign  reg_rd      = (read_now  & (dq_pio_target == 2'b11));

   assign  cam_data_wr = (write_now & (dq_pio_target == 2'b00) & (~indirect_mode | (indirect_mode & pio_ssr_index_valid)));
   assign  cam_mask_wr = (write_now & (dq_pio_target == 2'b01) & (~indirect_mode | (indirect_mode & pio_ssr_index_valid)));
   assign  sram_wr     = (write_now & (dq_pio_target == 2'b10) & (~indirect_mode | (indirect_mode & pio_ssr_index_valid)));
   assign  reg_wr      = (write_now & (dq_pio_target == 2'b11));

   // ???
   assign  learn_data_wr0 = ~(ref_fulo==2'b11) & (&fuli_dly) & learn_op_pipe1;            ///changed by HUJ
   assign  learn_data_wr1 = ~(ref_fulo==2'b11) & (&fuli_dly) & learn_op_pipe1 & cmd_learn_x144 ;    // Only in x144 mode  ///

   // ??? Do I need to qualify with valid bit (31) ??? --> Yes :) !!!
   assign  {pio_ssr_index_valid,pio_ssr_index} = (dq_ssr_index == 3'h0) ? {ssr_reg0[31],ssr_reg0[`LOG_ARRAY_SIZE-1:0]} :
           (dq_ssr_index == 3'h1) ? {ssr_reg1[31],ssr_reg1[`LOG_ARRAY_SIZE-1:0]} :
           (dq_ssr_index == 3'h2) ? {ssr_reg2[31],ssr_reg2[`LOG_ARRAY_SIZE-1:0]} :
           (dq_ssr_index == 3'h3) ? {ssr_reg3[31],ssr_reg3[`LOG_ARRAY_SIZE-1:0]} :
           (dq_ssr_index == 3'h4) ? {ssr_reg4[31],ssr_reg4[`LOG_ARRAY_SIZE-1:0]} :
           (dq_ssr_index == 3'h5) ? {ssr_reg5[31],ssr_reg5[`LOG_ARRAY_SIZE-1:0]} :
           (dq_ssr_index == 3'h6) ? {ssr_reg6[31],ssr_reg6[`LOG_ARRAY_SIZE-1:0]} :
           (dq_ssr_index == 3'h7) ? {ssr_reg7[31],ssr_reg7[`LOG_ARRAY_SIZE-1:0]} :
`ifdef CAM_4MEG
	   17'h0          		    ;
`else
   16'h0          		    ;
`endif
   

   // ??? Use Even Masks for Wrs and also in xREG_WIDTH mode;
   assign  global_mask_xREG_WIDTH_0 = (cmd_global_mask_indexA == 4'h0) ? mask_reg0  :
	   (cmd_global_mask_indexA == 4'h1) ? mask_reg2  :
	   (cmd_global_mask_indexA == 4'h2) ? mask_reg4  :
	   (cmd_global_mask_indexA == 4'h3) ? mask_reg6  :
	   (cmd_global_mask_indexA == 4'h4) ? mask_reg8  :
	   (cmd_global_mask_indexA == 4'h5) ? mask_reg10 :
	   (cmd_global_mask_indexA == 4'h6) ? mask_reg12 :
`ifdef CAM_4MEG
	   (cmd_global_mask_indexA == 4'h7) ? mask_reg14 :
	   (cmd_global_mask_indexA == 4'h8) ? mask_reg16 :
	   (cmd_global_mask_indexA == 4'h9) ? mask_reg18 :
	   (cmd_global_mask_indexA == 4'ha) ? mask_reg20 :
       	   (cmd_global_mask_indexA == 4'hb) ? mask_reg22 :
       	   (cmd_global_mask_indexA == 4'hc) ? mask_reg24 :
       	   (cmd_global_mask_indexA == 4'hd) ? mask_reg26 :
      	   (cmd_global_mask_indexA == 4'he) ? mask_reg28 :
           mask_reg30;
`else // !ifdef CAM_4MEG
   mask_reg14;

`endif // !ifdef CAM_4MEG
   
   

   assign  global_mask_xREG_WIDTH_1 = (cmd_global_mask_indexA == 3'h0) ? mask_reg1  :
	   (cmd_global_mask_indexA == 4'h1) ? mask_reg3  :
	   (cmd_global_mask_indexA == 4'h2) ? mask_reg5  :
	   (cmd_global_mask_indexA == 4'h3) ? mask_reg7  :
	   (cmd_global_mask_indexA == 4'h4) ? mask_reg9  :
	   (cmd_global_mask_indexA == 4'h5) ? mask_reg11 :
	   (cmd_global_mask_indexA == 4'h6) ? mask_reg13 :
`ifdef CAM_4MEG
       	   (cmd_global_mask_indexA == 4'h7) ? mask_reg15 :
	   (cmd_global_mask_indexA == 4'h8) ? mask_reg17 :
	   (cmd_global_mask_indexA == 4'h9) ? mask_reg19 :
	   (cmd_global_mask_indexA == 4'ha) ? mask_reg21 :
       	   (cmd_global_mask_indexA == 4'hb) ? mask_reg23 :
       	   (cmd_global_mask_indexA == 4'hc) ? mask_reg25 :
       	   (cmd_global_mask_indexA == 4'hd) ? mask_reg27 :
      	   (cmd_global_mask_indexA == 4'he) ? mask_reg29 :
	   mask_reg31 ;
`else // !ifdef CAM_4MEG
   mask_reg15;
`endif // !ifdef CAM_4MEG
   

   assign  global_mask_x288 = (cmd_global_mask_indexC == 3'h0) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg0, mask_reg1}  :
	   (cmd_global_mask_indexC == 3'h1) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg2, mask_reg3}  :
	   (cmd_global_mask_indexC == 3'h2) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg4, mask_reg5}  :
	   (cmd_global_mask_indexC == 3'h3) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg6, mask_reg7}  :
	   (cmd_global_mask_indexC == 3'h4) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg8, mask_reg9}  :
	   (cmd_global_mask_indexC == 3'h5) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg10,mask_reg11} :
	   (cmd_global_mask_indexC == 3'h6) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg12,mask_reg13} :
`ifdef CAM_4MEG
	   (cmd_global_mask_indexC == 4'h7) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg14,mask_reg15} :
	   (cmd_global_mask_indexC == 4'h8) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg16,mask_reg17} :
	   (cmd_global_mask_indexC == 4'h9) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg18,mask_reg19} :
	   (cmd_global_mask_indexC == 4'ha) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg20,mask_reg21} :
	   (cmd_global_mask_indexC == 4'hb) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg22,mask_reg23} :
	   (cmd_global_mask_indexC == 4'hc) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg24,mask_reg25} :
	   (cmd_global_mask_indexC == 4'hd) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg26,mask_reg27} :
	   (cmd_global_mask_indexC == 4'he) ? {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg28,mask_reg29} :
	   {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg30,mask_reg31} ;
`else // !ifdef CAM_4MEG
   
   {global_mask_xREG_WIDTH_0, global_mask_xREG_WIDTH_1, mask_reg14,mask_reg15};

`endif // !ifdef CAM_4MEG
   
   assign  register_addr      = dq_address[6:0];

   // ??? Precedence of burst/indirect_mode
   // Change -- OR 2 LSB of INDEX with DQ in Indirect Mode instead of qualifying with CFG. 
   assign  cam_data_mask_addr = (cmd_burst)     ? running_burst_addr 	     	     			    :
           (indirect_mode) ? {pio_ssr_index[`LOG_ARRAY_SIZE-1:2],(pio_ssr_index[1:0] | dq_address[1:0])} :
           dq_address               	     			    ;

   // DONE TO FIX FULL -- NFA PIPE
   always @(posedge clk) cam_data_mask_addr_pipe1 <= #D cam_data_mask_addr;


   // *** NOTE: Currently only supporting 1M mode ***
   // ??? Can Indirect Mode and Burst happen at the same time ???
   // Change -- OR 2 LSB of INDEX with DQ in Indirect Mode instead of qualifying with CFG. 
   // Burst PIO RD/WR not supported for SRAM
   // Remove Search from ext_sram_adrr pipeline since we don't know search_success_index

   always @(posedge clk) learn_op_pipe1 <= #D learn_op;
   always @(posedge clk) learn_op_pipe2 <= #D learn_op_pipe1;

   // Change -- OR 2 LSB of INDEX with DQ in Indirect Mode instead of qualifying with CFG. 
   // Burst PIO RD/WR not supported for SRAM
`ifdef CAM_4MEG
   always @(posedge clk)
      begin
       #D;
        if ( `INDEX_WIDTH - `LOG_ARRAY_SIZE == 0)
           ext_sram_addr <=  (indirect_mode)  ? {cmd_sadr,id,pio_ssr_index[`LOG_ARRAY_SIZE-1:2],(pio_ssr_index[1:0] | dq_address[1:0])} :
                      (learn_op_pipe1) ? {cmd_sadr,id,nfa_reg[`LOG_ARRAY_SIZE-1:0]}            			          :
                      {cmd_sadr,id,dq_address}               			          ;
        else
            ext_sram_addr <=  (indirect_mode)  ? {cmd_sadr,id,{`INDEX_WIDTH-`LOG_ARRAY_SIZE{1'b0}},pio_ssr_index[`LOG_ARRAY_SIZE-1:2],(pio_ssr_index[1:0] | dq_address[1:0])} :
                      (learn_op_pipe1) ? {cmd_sadr,id,{`INDEX_WIDTH-`LOG_ARRAY_SIZE{1'b0}},nfa_reg[`LOG_ARRAY_SIZE-1:0]}            			          :
                      {cmd_sadr,id,{`INDEX_WIDTH-`LOG_ARRAY_SIZE{1'b0}},dq_address}               			          ;
      end // always @ (posedge clk)

`else // 
     `ifdef CAM_2MEG
      always @(posedge clk)
      begin
        #D;
        if ( `INDEX_WIDTH - `LOG_ARRAY_SIZE == 0)
           ext_sram_addr <=  (indirect_mode)  ? {cmd_sadr[2:1],id,pio_ssr_index[`LOG_ARRAY_SIZE-1:2],(pio_ssr_index[1:0] | dq_address[1:0])} :
                      (learn_op_pipe1) ? {cmd_sadr[2:1],id,nfa_reg[`LOG_ARRAY_SIZE-1:0]}            			          :
                      {cmd_sadr,id,dq_address}               			          ;
        else
            ext_sram_addr <=  (indirect_mode)  ? {cmd_sadr[2:1],id,{`INDEX_WIDTH-`LOG_ARRAY_SIZE{1'b0}},pio_ssr_index[`LOG_ARRAY_SIZE-1:2],(pio_ssr_index[1:0] | dq_address[1:0])} :
                      (learn_op_pipe1) ? {cmd_sadr[2:1],id,{`INDEX_WIDTH-`LOG_ARRAY_SIZE{1'b0}},nfa_reg[`LOG_ARRAY_SIZE-1:0]}            			          :
                      {cmd_sadr[2:1],id,{`INDEX_WIDTH-`LOG_ARRAY_SIZE{1'b0}},dq_address}               			          ;
      end // always @ (posedge clk)
    `else

always @(posedge clk)
  begin
   #D;
    //ext_sram_addr <=  (indirect_mode)  ? {cmd_sadr,id,pio_ssr_index[13:2],(pio_ssr_index[1:0] | dq_address[1:0])} :
    //                  (learn_op_pipe1) ? {cmd_sadr,id,nfa_reg[13:0]}                                              :
    //
    //                                     {cmd_sadr,id,dq_address}                                                 ;
     if ( `INDEX_WIDTH - `LOG_ARRAY_SIZE == 0)
    ext_sram_addr <= (indirect_mode) ? {cmd_sadr,id,pio_ssr_index[`LOG_ARRAY_SIZE-1:2],(pio_ssr_index[1:0]|dq_address[1:0])} : 
      (learn_op_pipe1) ? {cmd_sadr,id,nfa_reg[`LOG_ARRAY_SIZE-1:0]}
  :
        {cmd_sadr,id,dq_address};
    else
         ext_sram_addr <=  (indirect_mode)  ? {cmd_sadr,id,{`INDEX_WIDTH-`LOG_ARRAY_SIZE{1'b0}},pio_ssr_index[`LOG_ARRAY_SIZE-1:2],(pio_ssr_index[1:0] | dq_address[1:0])} :
    (learn_op_pipe1) ? {cmd_sadr,id,{`INDEX_WIDTH-`LOG_ARRAY_SIZE{1'b0}},nfa_reg[`LOG_ARRAY_SIZE-1:0 ]}                                        :
 {cmd_sadr,id,{`INDEX_WIDTH-`LOG_ARRAY_SIZE{1'b0}},dq_address} ;

   end
   `endif // !ifdef CAM_2MEG 

`endif // !ifdef CAM_4MEG
   
   

   assign  wr_mask_reg0   = (reg_wr & (register_addr == 7'd32));
   assign  wr_mask_reg1   = (reg_wr & (register_addr == 7'd33));
   assign  wr_mask_reg2   = (reg_wr & (register_addr == 7'd34));
   assign  wr_mask_reg3   = (reg_wr & (register_addr == 7'd35));
   assign  wr_mask_reg4   = (reg_wr & (register_addr == 7'd36));
   assign  wr_mask_reg5   = (reg_wr & (register_addr == 7'd37));
   assign  wr_mask_reg6   = (reg_wr & (register_addr == 7'd38));
   assign  wr_mask_reg7   = (reg_wr & (register_addr == 7'd39));
   assign  wr_mask_reg8   = (reg_wr & (register_addr == 7'd40));
   assign  wr_mask_reg9   = (reg_wr & (register_addr == 7'd41));
   assign  wr_mask_reg10  = (reg_wr & (register_addr == 7'd42));
   assign  wr_mask_reg11  = (reg_wr & (register_addr == 7'd43));
   assign  wr_mask_reg12  = (reg_wr & (register_addr == 7'd44));
   assign  wr_mask_reg13  = (reg_wr & (register_addr == 7'd45));
   assign  wr_mask_reg14  = (reg_wr & (register_addr == 7'd46));
   assign  wr_mask_reg15  = (reg_wr & (register_addr == 7'd47));
   assign  wr_cmd_reg     = (reg_wr & (register_addr == 7'd56));
   assign  wr_rd_bst_reg  = (reg_wr & (register_addr == 7'd58));
   assign  wr_wr_bst_reg  = (reg_wr & (register_addr == 7'd59));
`ifdef CAM_4MEG
   assign  wr_mask_reg16  = (reg_wr & (register_addr == 7'd96));
   assign  wr_mask_reg17  = (reg_wr & (register_addr == 7'd97));
   assign  wr_mask_reg18  = (reg_wr & (register_addr == 7'd98));
   assign  wr_mask_reg19  = (reg_wr & (register_addr == 7'd99));
   assign  wr_mask_reg20  = (reg_wr & (register_addr == 7'd100));
   assign  wr_mask_reg21  = (reg_wr & (register_addr == 7'd101));
   assign  wr_mask_reg22  = (reg_wr & (register_addr == 7'd102));
   assign  wr_mask_reg23  = (reg_wr & (register_addr == 7'd103));
   assign  wr_mask_reg24  = (reg_wr & (register_addr == 7'd104));
   assign  wr_mask_reg25  = (reg_wr & (register_addr == 7'd105));
   assign  wr_mask_reg26  = (reg_wr & (register_addr == 7'd106));
   assign  wr_mask_reg27  = (reg_wr & (register_addr == 7'd107));
   assign  wr_mask_reg28  = (reg_wr & (register_addr == 7'd108));
   assign  wr_mask_reg29  = (reg_wr & (register_addr == 7'd109));
   assign  wr_mask_reg30  = (reg_wr & (register_addr == 7'd110));
   assign  wr_mask_reg31  = (reg_wr & (register_addr == 7'd111));
`endif // ifdef CAM_4MEG
   

   // ??? x288 mode 
   assign  wr_comp_reg0   = ((search_op1 | search_op2) & (cmd[5:2] === 4'h0));
   assign  wr_comp_reg1   = wr_comp_reg0;
   assign  wr_comp_reg2   = ((search_op1 | search_op2) & (cmd[5:2] === 4'h1));
   assign  wr_comp_reg3   = wr_comp_reg2;
   assign  wr_comp_reg4   = ((search_op1 | search_op2) & (cmd[5:2] === 4'h2));
   assign  wr_comp_reg5   = wr_comp_reg4;
   assign  wr_comp_reg6   = ((search_op1 | search_op2) & (cmd[5:2] === 4'h3));
   assign  wr_comp_reg7   = wr_comp_reg6;
   assign  wr_comp_reg8   = ((search_op1 | search_op2) & (cmd[5:2] === 4'h4));
   assign  wr_comp_reg9   = wr_comp_reg8;
   assign  wr_comp_reg10  = ((search_op1 | search_op2) & (cmd[5:2] === 4'h5));
   assign  wr_comp_reg11  = wr_comp_reg10;
   assign  wr_comp_reg12  = ((search_op1 | search_op2) & (cmd[5:2] === 4'h6));
   assign  wr_comp_reg13  = wr_comp_reg12;
   assign  wr_comp_reg14  = ((search_op1 | search_op2) & (cmd[5:2] === 4'h7));
   assign  wr_comp_reg15  = wr_comp_reg14;
   assign  wr_comp_reg16  = ((search_op1 | search_op2) & (cmd[5:2] === 4'h8));
   assign  wr_comp_reg17  = wr_comp_reg16;
   assign  wr_comp_reg18  = ((search_op1 | search_op2) & (cmd[5:2] === 4'h9));
   assign  wr_comp_reg19  = wr_comp_reg18;
   assign  wr_comp_reg20  = ((search_op1 | search_op2) & (cmd[5:2] === 4'hA));
   assign  wr_comp_reg21  = wr_comp_reg20;
   assign  wr_comp_reg22  = ((search_op1 | search_op2) & (cmd[5:2] === 4'hB));
   assign  wr_comp_reg23  = wr_comp_reg22;
   assign  wr_comp_reg24  = ((search_op1 | search_op2) & (cmd[5:2] === 4'hC));
   assign  wr_comp_reg25  = wr_comp_reg24;
   assign  wr_comp_reg26  = ((search_op1 | search_op2) & (cmd[5:2] === 4'hD));
   assign  wr_comp_reg27  = wr_comp_reg26;
   assign  wr_comp_reg28  = ((search_op1 | search_op2) & (cmd[5:2] === 4'hE));
   assign  wr_comp_reg29  = wr_comp_reg28;
   assign  wr_comp_reg30  = ((search_op1 | search_op2) & (cmd[5:2] === 4'hF));
   assign  wr_comp_reg31  = wr_comp_reg30;

   assign  wr_comp_value  = (search_op2) ? dq_cycle_dataC : dq_cycle_dataA ;

   always @(posedge clk_ref or negedge clk_ref)
     if (clk)
       dq_latched <= #D dq_int;
     else
       dq_latched <= #D dq_latched;

   assign  cam_rd_mod_wr_data = ((cam_data_array[cam_data_mask_addr] & ~global_mask_xREG_WIDTH_0) |
				 (dq_latched & global_mask_xREG_WIDTH_0));

   // DONE TO FIX FULL -- NFA PIPE
   always @(posedge clk) cam_rd_mod_wr_data_pipe1 <= #D cam_rd_mod_wr_data;

   assign  learn_comp_0 = (cmd_comp_indexA == 4'h0) ? comp_reg0  :
	   (cmd_comp_indexA == 4'h1) ? comp_reg2  :
	   (cmd_comp_indexA == 4'h2) ? comp_reg4  :
	   (cmd_comp_indexA == 4'h3) ? comp_reg6  :
	   (cmd_comp_indexA == 4'h4) ? comp_reg8  :
	   (cmd_comp_indexA == 4'h5) ? comp_reg10 :
	   (cmd_comp_indexA == 4'h6) ? comp_reg12 :
	   (cmd_comp_indexA == 4'h7) ? comp_reg14 :
	   (cmd_comp_indexA == 4'h8) ? comp_reg16 :
	   (cmd_comp_indexA == 4'h9) ? comp_reg18 :
	   (cmd_comp_indexA == 4'hA) ? comp_reg20 :
	   (cmd_comp_indexA == 4'hB) ? comp_reg22 :
	   (cmd_comp_indexA == 4'hC) ? comp_reg24 :
	   (cmd_comp_indexA == 4'hD) ? comp_reg26 :
	   (cmd_comp_indexA == 4'hE) ? comp_reg28 :
	   comp_reg30 ;

   assign  learn_comp_1 = (cmd_comp_indexB == 4'h0) ? comp_reg1  :
           (cmd_comp_indexB == 4'h1) ? comp_reg3  :
           (cmd_comp_indexB == 4'h2) ? comp_reg5  :
           (cmd_comp_indexB == 4'h3) ? comp_reg7  :
           (cmd_comp_indexB == 4'h4) ? comp_reg9  :
           (cmd_comp_indexB == 4'h5) ? comp_reg11 :
           (cmd_comp_indexB == 4'h6) ? comp_reg13 :
           (cmd_comp_indexB == 4'h7) ? comp_reg15 :
           (cmd_comp_indexB == 4'h8) ? comp_reg17 :
           (cmd_comp_indexB == 4'h9) ? comp_reg19 :
           (cmd_comp_indexB == 4'hA) ? comp_reg21 :
           (cmd_comp_indexB == 4'hB) ? comp_reg23 :
           (cmd_comp_indexB == 4'hC) ? comp_reg25 :
           (cmd_comp_indexB == 4'hD) ? comp_reg27 :
           (cmd_comp_indexB == 4'hE) ? comp_reg29 :
           comp_reg31 ;

   // ??? Need to put in correct reset values
   always @(posedge clk)
     begin
    	comp_reg0   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg0)  ? wr_comp_value : comp_reg0;
    	comp_reg1   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg1)  ? dq_int 		  : comp_reg1;
    	comp_reg2   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg2)  ? wr_comp_value : comp_reg2;
    	comp_reg3   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg3)  ? dq_int 		  : comp_reg3;
    	comp_reg4   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg4)  ? wr_comp_value : comp_reg4;
    	comp_reg5   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg5)  ? dq_int             : comp_reg5;
    	comp_reg6   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg6)  ? wr_comp_value : comp_reg6;
    	comp_reg7   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg7)  ? dq_int             : comp_reg7;
    	comp_reg8   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg8)  ? wr_comp_value : comp_reg8;
    	comp_reg9   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg9)  ? dq_int             : comp_reg9;
    	comp_reg10  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg10) ? wr_comp_value : comp_reg10;
    	comp_reg11  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg11) ? dq_int             : comp_reg11;
    	comp_reg12  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg12) ? wr_comp_value : comp_reg12;
    	comp_reg13  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg13) ? dq_int             : comp_reg13;
    	comp_reg14  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg14) ? wr_comp_value : comp_reg14;
    	comp_reg15  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg15) ? dq_int             : comp_reg15;
    	comp_reg16  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg16) ? wr_comp_value : comp_reg16;
    	comp_reg17  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg17) ? dq_int             : comp_reg17;
    	comp_reg18  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg18) ? wr_comp_value : comp_reg18;
    	comp_reg19  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg19) ? dq_int             : comp_reg19;
    	comp_reg20  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg20) ? wr_comp_value : comp_reg20;
    	comp_reg21  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg21) ? dq_int             : comp_reg21;
    	comp_reg22  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg22) ? wr_comp_value : comp_reg22;
    	comp_reg23  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg23) ? dq_int             : comp_reg23;
    	comp_reg24  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg24) ? wr_comp_value : comp_reg24;
    	comp_reg25  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg25) ? dq_int             : comp_reg25;
    	comp_reg26  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg26) ? wr_comp_value : comp_reg26;
    	comp_reg27  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg27) ? dq_int             : comp_reg27;
    	comp_reg28  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg28) ? wr_comp_value : comp_reg28;
    	comp_reg29  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg29) ? dq_int             : comp_reg29;
    	comp_reg30  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg30) ? wr_comp_value : comp_reg30;
    	comp_reg31  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_comp_reg31) ? dq_int             : comp_reg31;
    	mask_reg0   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg0)  ? dq_latched : mask_reg0;
    	mask_reg1   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg1)  ? dq_latched : mask_reg1;
    	mask_reg2   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg2)  ? dq_latched : mask_reg2;
    	mask_reg3   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg3)  ? dq_latched : mask_reg3;
    	mask_reg4   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg4)  ? dq_latched : mask_reg4;
    	mask_reg5   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg5)  ? dq_latched : mask_reg5;
    	mask_reg6   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg6)  ? dq_latched : mask_reg6;
    	mask_reg7   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg7)  ? dq_latched : mask_reg7;
    	mask_reg8   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg8)  ? dq_latched : mask_reg8;
    	mask_reg9   <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg9)  ? dq_latched : mask_reg9;
    	mask_reg10  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg10) ? dq_latched : mask_reg10;
    	mask_reg11  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg11) ? dq_latched : mask_reg11;
    	mask_reg12  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg12) ? dq_latched : mask_reg12;
    	mask_reg13  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg13) ? dq_latched : mask_reg13;
    	mask_reg14  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg14) ? dq_latched : mask_reg14;
    	mask_reg15  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg15) ? dq_latched : mask_reg15;
`ifdef CAM_4MEG
    	mask_reg16  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg16) ? dq_latched : mask_reg16;
    	mask_reg17  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg17) ? dq_latched : mask_reg17;
    	mask_reg18  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg18) ? dq_latched : mask_reg18;
    	mask_reg19  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg19) ? dq_latched : mask_reg19;
    	mask_reg20  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg20) ? dq_latched : mask_reg20;
    	mask_reg21  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg21) ? dq_latched : mask_reg21;
    	mask_reg22  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg22) ? dq_latched : mask_reg22;
    	mask_reg23  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg23) ? dq_latched : mask_reg23;
    	mask_reg24  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg24) ? dq_latched : mask_reg24;
    	mask_reg25  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg25) ? dq_latched : mask_reg25;
    	mask_reg26  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg26) ? dq_latched : mask_reg26;
    	mask_reg27  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg27) ? dq_latched : mask_reg27;
    	mask_reg28  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg28) ? dq_latched : mask_reg28;
    	mask_reg29  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg29) ? dq_latched : mask_reg29;
    	mask_reg30  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg30) ? dq_latched : mask_reg30;
    	mask_reg31  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_mask_reg31) ? dq_latched : mask_reg31;
`endif // ifdef CAM_4MEG
     	
    	ssr_reg0    <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_ssr_reg0)   ? wr_ssr_value : ssr_reg0;
    	ssr_reg1    <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_ssr_reg1)   ? wr_ssr_value : ssr_reg1;
    	ssr_reg2    <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_ssr_reg2)   ? wr_ssr_value : ssr_reg2;
    	ssr_reg3    <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_ssr_reg3)   ? wr_ssr_value : ssr_reg3;
    	ssr_reg4    <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_ssr_reg4)   ? wr_ssr_value : ssr_reg4;
    	ssr_reg5    <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_ssr_reg5)   ? wr_ssr_value : ssr_reg5;
    	ssr_reg6    <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_ssr_reg6)   ? wr_ssr_value : ssr_reg6;
    	ssr_reg7    <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_ssr_reg7)   ? wr_ssr_value : ssr_reg7;
    	cmd_reg     <= #D (~reset_l) ? `REG_WIDTH'h4 : (wr_cmd_reg)    ? dq_int[24:0] : cmd_reg;			// ???
    	rd_bst_reg  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_rd_bst_reg)     ? {44'h0,dq_int[27:19],3'h0,dq_int[15:0]} : 
		       (update_rd_bst_reg) ? {44'h0,running_burst_len,3'h0,running_burst_addr}:	// ???
		       rd_bst_reg;
    	wr_bst_reg  <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_wr_bst_reg)     ? {44'h0,dq_int[27:19],3'h0,dq_int[15:0]} :
		       (update_wr_bst_reg) ? {40'h0,running_burst_len,5'h0,running_burst_addr}:	// ???
		       wr_bst_reg;
    	nfa_reg     <= #D (~reset_l) ? `REG_WIDTH'h0 : (wr_nfa_reg)    ? {56'h0, next_free_addr} : nfa_reg;
    	if (cam_data_wr_pipe1)			// Write Op
	  begin
	     if (parallel)
	       begin
		  for (addr_par_write = 7'b0; addr_par_write<64; addr_par_write=addr_par_write+1)
		    begin
		       cam_data_array[ {addr_par_write[5:1],cam_data_mask_addr_pipe1[`LOG_ARRAY_SIZE-6:1],addr_par_write[0]}]  <= #D cam_rd_mod_wr_data_pipe1;
      	  	    end
	       end
	     else
               cam_data_array[cam_data_mask_addr_pipe1] <= #D cam_rd_mod_wr_data_pipe1;

	  end
    	else if (learn_data_wr0 | learn_data_wr1)	// Learn Op
	  begin
	     if (learn_data_wr0)
	       begin
`ifdef CAM_4MEG
		  if(cfg_info[nfa_reg[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-3]] == 2'h0)
		    
		    cam_data_array[nfa_reg[`LOG_ARRAY_SIZE-1:0]]        <= #D learn_comp_0;
		  else if (cfg_info[nfa_reg[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-3]] == 2'h1) 
		    cam_data_array[{nfa_reg[`LOG_ARRAY_SIZE-1:1],1'b0}] <= #D learn_comp_0;
`else
		  if(cfg_info[nfa_reg[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2]] == 2'h0)
		    cam_data_array[nfa_reg[`LOG_ARRAY_SIZE-1:0]]        <= #D learn_comp_0;
		  else if (cfg_info[nfa_reg[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2]] == 2'h1) 
		    cam_data_array[{nfa_reg[`LOG_ARRAY_SIZE-1:1],1'b0}] <= #D learn_comp_0;

`endif // !ifdef CAM_4MEG
		  
		  
	       end
	     if (learn_data_wr1)
	       cam_data_array[{nfa_reg[`LOG_ARRAY_SIZE-1:1],1'b1}]     <= #D learn_comp_1;
	  end
    	if (cam_mask_wr)
	  begin
	     if (parallel)
	       begin
	     		  for (addr_par_write = 7'b0; addr_par_write<64; addr_par_write=addr_par_write+1)
		    begin
		   // cam_mask_array[ {addr_par_write[5:1],cam_data_mask_addr[`LOG_ARRAY_SIZE-6:1],addr_par_write[0]}]  <= #D dq_int;
		       cam_mask_array[ {addr_par_write[5:1],cam_data_mask_addr[`LOG_ARRAY_SIZE-6:1],addr_par_write[0]}]  <= ((cam_mask_array[cam_data_mask_addr] & ~global_mask_xREG_WIDTH_0) |(dq_latched & global_mask_xREG_WIDTH_0));//only dq_int before HUJ modified
      	  	    end
	       end
	     else
	     //cam_mask_array[cam_data_mask_addr]   <= #D dq_int;
	     cam_mask_array[cam_data_mask_addr]   <= ((cam_mask_array[cam_data_mask_addr] & ~global_mask_xREG_WIDTH_0) |(dq_latched & global_mask_xREG_WIDTH_0)); //only dq_int before HUJ modified
	  end
	
     end

   // RD DATA select
   always @(posedge clk)
     begin
    	if (reg_rd)
	  begin
             case(register_addr)
               7'd0:  ref_dq = comp_reg0;
               7'd1:  ref_dq = comp_reg1;
               7'd2:  ref_dq = comp_reg2;
               7'd3:  ref_dq = comp_reg3;
               7'd4:  ref_dq = comp_reg4;
               7'd5:  ref_dq = comp_reg5;
               7'd6:  ref_dq = comp_reg6;
               7'd7:  ref_dq = comp_reg7;
               7'd8:  ref_dq = comp_reg8;
               7'd9:  ref_dq = comp_reg9;
               7'd10: ref_dq = comp_reg10;
               7'd11: ref_dq = comp_reg11;
               7'd12: ref_dq = comp_reg12;
               7'd13: ref_dq = comp_reg13;
               7'd14: ref_dq = comp_reg14;
               7'd15: ref_dq = comp_reg15;
               7'd16: ref_dq = comp_reg16;
               7'd17: ref_dq = comp_reg17;
               7'd18: ref_dq = comp_reg18;
               7'd19: ref_dq = comp_reg19;
               7'd20: ref_dq = comp_reg20;
               7'd21: ref_dq = comp_reg21;
               7'd22: ref_dq = comp_reg22;
               7'd23: ref_dq = comp_reg23;
               7'd24: ref_dq = comp_reg24;
               7'd25: ref_dq = comp_reg25;
               7'd26: ref_dq = comp_reg26;
               7'd27: ref_dq = comp_reg27;
               7'd28: ref_dq = comp_reg28;
               7'd29: ref_dq = comp_reg29;
               7'd30: ref_dq = comp_reg30;
               7'd31: ref_dq = comp_reg31;
               7'd32: ref_dq = mask_reg0;
               7'd33: ref_dq = mask_reg1;
               7'd34: ref_dq = mask_reg2;
               7'd35: ref_dq = mask_reg3;
               7'd36: ref_dq = mask_reg4;
               7'd37: ref_dq = mask_reg5;
               7'd38: ref_dq = mask_reg6;
               7'd39: ref_dq = mask_reg7;
               7'd40: ref_dq = mask_reg8;
               7'd41: ref_dq = mask_reg9;
               7'd42: ref_dq = mask_reg10;
               7'd43: ref_dq = mask_reg11;
               7'd44: ref_dq = mask_reg12;
               7'd45: ref_dq = mask_reg13;
               7'd46: ref_dq = mask_reg14;
               7'd47: ref_dq = mask_reg15;
               7'd48: ref_dq = ssr_reg0;
               7'd49: ref_dq = ssr_reg1;
               7'd50: ref_dq = ssr_reg2;
               7'd51: ref_dq = ssr_reg3;
               7'd52: ref_dq = ssr_reg4;
               7'd53: ref_dq = ssr_reg5;
               7'd54: ref_dq = ssr_reg6;
               7'd55: ref_dq = ssr_reg7;
               7'd56: ref_dq = {cmd_reg[`REG_WIDTH - 1:1],srst};
               6'd57: ref_dq = 

`ifdef CAM_4MEG
			       {40'h0,16'hdc7f,8'h04,1'b0,3'b1,4'b1};    // Info Register
`else
	       
`ifdef CAM_2MEG
			       {40'h0,16'hdc7f,8'h02,1'b0,3'b1,4'b1};    // Info Register
`else
 `ifdef CAM_1MEG
	       			       {40'h0,16'hdc7f,8'h01,1'b0,3'b1,4'b1};    // Info Register
 `else
	       
	       {32'h0,16'hdc7f,8'h1,8'h1};    // Info Register
 `endif
	       
`endif
	       
`endif
	       
               7'd58: ref_dq = rd_bst_reg;
               7'd59: ref_dq = wr_bst_reg;
               7'd60: ref_dq = nfa_reg;
`ifdef CAM_4MEG
               7'd96: ref_dq = mask_reg16;
               7'd97: ref_dq = mask_reg17;
               7'd98: ref_dq = mask_reg18;
               7'd99: ref_dq = mask_reg19;
               7'd100: ref_dq = mask_reg20;
               7'd101: ref_dq = mask_reg21;
               7'd102: ref_dq = mask_reg22;
               7'd103: ref_dq = mask_reg23;
               7'd104: ref_dq = mask_reg24;
               7'd105: ref_dq = mask_reg25;
               7'd106: ref_dq = mask_reg26;
               7'd107: ref_dq = mask_reg27;
               7'd108: ref_dq = mask_reg28;
               7'd109: ref_dq = mask_reg29;
               7'd110: ref_dq = mask_reg30;
               7'd111: ref_dq = mask_reg31;			  
`endif			  
               default: ref_dq = `REG_WIDTH'h0;
             endcase //case
	  end
    	else if (cam_data_rd ) // & (~indirect_mode | (indirect_mode & pio_ssr_index_valid)))	// ???
	  begin
             ref_dq = cam_data_array[cam_data_mask_addr];
	  end
    	else if (cam_mask_rd ) // & (~indirect_mode | (indirect_mode & pio_ssr_index_valid)))	// ???
	  begin
             ref_dq = cam_mask_array[cam_data_mask_addr];
	  end
    	else
             ref_dq = {`REG_WIDTH {1'b1} } ; //`REG_WIDTH'hffffffffffffffffff;
     end //always

   /******************************* COMMAND STATE MACHINE ************************/

   parameter	STATE_CYC1 = 3'h1,
       STATE_CYC2 = 3'h2,
       STATE_CYC3 = 3'h3,
       STATE_CYC4 = 3'h4,
       STATE_CYC5 = 3'h5,
       STATE_CYC6 = 3'h6,
       STATE_BST  = 3'h7,
       STATE_SRAM = 3'h0;

   always @(posedge clk)  
     begin
     #D;
    cmd_state   =  (~reset_l) ? STATE_CYC1 : n_cmd_state;
    end

   always @(posedge clk)
     running_burst_len  <= #D (~reset_l)             ? 9'h1ff :
                           (read_op  & cmd_burst) ? rd_burst_len :
                           (write_op & cmd_burst) ? wr_burst_len :
                           (inc_burst_addr)       ? running_burst_len - 9'h1 :
                           running_burst_len;

   always @(posedge clk)
     running_burst_addr <= #D (~reset_l)             ? 16'h0 :
                           (read_op  & cmd_burst) ? rd_burst_addr :
                           (write_op & cmd_burst) ? wr_burst_addr :
                           (inc_burst_addr)       ? running_burst_addr + 16'h1 :
                           running_burst_addr ;

   // This signal used for start of pipeline that drives SRAM signals
   always @(posedge clk) write_now_sram <= #D sram_wr;

   // Done to sample the cmd correctly
   reg cmdv_dly ;
   always @( second_cycle ) 	
       begin
         if ( cmdv == 1'b1)
            cmdv_dly = 1'b1;
         else
            cmdv_dly = 1'b0;
       end

   always @(posedge clk)
     if (~reset_l | read_op)
       sram_cycle_latency <= #D 4'h0;
     else if (inc_sram_cycle_count)
       sram_cycle_latency <= #D sram_cycle_latency + 4'h1;
     else
       sram_cycle_latency <= #D sram_cycle_latency;

   always @(cmdv_dly or cmd_op or dq_id or cmd_state or cmd_search_x288 or
            //cmd_burst or running_burst_len or indirect_mode or sram_cycle_latency or lcam or dq_pio_target)
            cmd_burst or running_burst_len or indirect_mode or sram_cycle_latency )
     begin

    	n_cmd_state = cmd_state;
    	read_op     = 1'b0;
    	write_op    = 1'b0;
    	search_op1  = 1'b0;
    	search_op2  = 1'b0;
    	learn_op    = 1'b0;
    	read_now    = 1'b0;
    	write_now   = 1'b0;
    	verify_read = 1'b0;
    	inc_burst_addr = 1'b0;
    	ref_eot	= 1'b0;
    	ref_ack	= 1'b0;
    	ref_oe_eot  = 1'b0;
    	ref_oe_ack  = 1'b0;
    	ref_oe_dq   = 1'b0;
    	update_rd_bst_reg = 1'b0;
    	update_wr_bst_reg = 1'b0;
    	inc_sram_cycle_count = 1'b0;
    	case(cmd_state)
	  STATE_CYC1: begin
             case({test,cmdv_dly,cmd_op})
               4'b0100: begin                       // RD	
                  if ((dq_id === id) | ((dq_id === 5'h1f) & lcam))	// Removed Case for qualifying with SSR Valid
                    begin
                       read_op     = 1'b1;
                       n_cmd_state = STATE_CYC2;
                    end
               end
               4'b0101: begin                       // WR
                  if ((dq_id === id) | (dq_id === 5'h1f))
                    begin
                       write_op    = 1'b1;
                       n_cmd_state = STATE_CYC2;
                    end
               end
               4'b0110: begin                       // SRCH
		  if (deve)
		    begin
                       search_op1  = 1'b1;
                       if (cmd_search_x288)      // x288 mode
                         begin
                            n_cmd_state = STATE_CYC2;
                         end
                       else
                         begin
                            n_cmd_state = STATE_CYC1;
                         end
		    end
               end
               4'b0111: begin                       // LRN
                  learn_op    = 1'b1;
                  n_cmd_state = STATE_CYC2;
               end
             endcase
 	  end
	  STATE_CYC2: begin
             if (sample_search_x288)		// SRCH
               begin
                  search_op2  = 1'b1;
                  n_cmd_state = STATE_CYC1;
               end
             else if (cmd_op == 2'b11)		// LRN
               begin
                  n_cmd_state = STATE_CYC1;
               end
             else if (cmd_op == 2'b01)		// WR 
               begin
                  write_now = 1'b1;
		  if (cmd_burst)
		    begin
                       inc_burst_addr  = 1'b1;
                       n_cmd_state     = STATE_BST;
		    end
                  else
                    begin
                       n_cmd_state = STATE_CYC3;
                    end
               end
             else				// RD
               begin
                  n_cmd_state = STATE_CYC3;
               end
	  end
	  STATE_CYC3: begin
             if (cmd_op == 2'b01)                // WR
               begin
                  n_cmd_state = STATE_CYC1;
		  if (cmd_burst)			// Burst Should NOT Happen for SRAM
		    begin
		       ref_oe_eot	      = 1'b1;
		       update_wr_bst_reg = 1'b1;
		    end
               end
             else                                  // RD
               begin
		  if ((dq_pio_target === 2'b10) & (({2'b0,tlsz} + {1'b0,hlat}) !== 4'h0))
		    begin
		       n_cmd_state          = STATE_SRAM;
		       inc_sram_cycle_count = 1'b1;
		    end
		  else
		    begin
                       n_cmd_state = STATE_CYC4;
		       if (cmd_burst)		// Burst Should NOT Happen for SRAM
			 begin
			    ref_oe_eot = 1'b1;
			 end
		    end
               end
	  end
	  STATE_SRAM: begin
	     inc_sram_cycle_count = 1'b1;
             ref_oe_dq   = 1'b1;
	     if (sram_cycle_latency === ({2'b0,tlsz} + {1'b0,hlat}))
	       begin
		  n_cmd_state = STATE_CYC4;
	  	  inc_sram_cycle_count = 1'b0;
	       end
	  end
	  STATE_CYC4: begin
	     ref_oe_ack  = 1'b1;
             read_now    = 1'b1;
             ref_oe_dq   = 1'b1;
             n_cmd_state = STATE_CYC5;
	     if (cmd_burst)
	       begin
		  ref_oe_eot = 1'b1;
	       end
	  end
	  STATE_CYC5: begin                                   // RD
	     ref_ack     = 1'b1;
	     ref_oe_ack  = 1'b1;
             ref_oe_dq   = 1'b1;
             if (dq_pio_target !== 2'b10) // For NOT SRAM RD
               begin
                  verify_read = 1'b1;
                  // ref_oe_dq   = 1'b1;
               end
	     if (cmd_burst)
	       begin
		  ref_oe_eot     = 1'b1;
                  inc_burst_addr = 1'b1;
		  if (running_burst_len == 9'h1)	// ??? SHOULD I VERIFY BURST_LEN >= 4
		    begin
		       ref_eot     = 1'b1;
                       n_cmd_state = STATE_CYC6;
		    end
		  else
		    begin
                       n_cmd_state = STATE_BST;
		    end
	       end
	     else
               begin
		  ref_ack     = 1'b1;
                  n_cmd_state = STATE_CYC6;
               end
	  end
	  STATE_CYC6: begin                                   // RD
	     ref_oe_ack  = 1'b1;
             ref_oe_dq   = 1'b0;
             n_cmd_state = STATE_CYC1;
	     if (cmd_burst)
	       begin	
		  ref_oe_eot        = 1'b1;
		  update_rd_bst_reg = 1'b1;
	       end
	  end
	  STATE_BST: begin
	     if (cmd_op == 2'b00)	// RD
	       begin
		  ref_oe_ack  = 1'b1;
		  ref_oe_eot  = 1'b1;
		  read_now    = 1'b1;
		  n_cmd_state = STATE_CYC5;
                  if (dq_pio_target !== 2'b10) // For NOT SRAM RD
                    begin
                       ref_oe_dq   = 1'b1;
                    end
	       end
	     else			// WR
	       begin
		  ref_oe_eot     = 1'b1;
		  write_now      = 1'b1;
                  inc_burst_addr = 1'b1;
		  if (running_burst_len == 9'h1)	// ??? SHOULD I VERIFY BURST_LEN >= 4
                    begin
		       ref_eot     = 1'b1;
                       n_cmd_state = STATE_CYC3;
                    end
		  else
		    begin
                       n_cmd_state = STATE_BST;
		    end
	       end
          end
    	endcase
     end

   /**************************** SEARCH ***********************************/
   reg first_hit;
   always @(posedge clk_dly)
     begin
    	if (search_op_pipe1)
	  begin
             //#D;
	     cam_data_mask_index = 0;
	     pre_lho = 0;
	     multihit =0;
	     first_hit = 0; 
	     #0;
             while ((cam_data_mask_index <= (`ARRAY_SIZE-1))   /* & ~pre_lho */   & ~multihit  )
	       begin
		  if (sample_search_x288_pipe1)
		    begin
		       
	               cam_data_x288 = {cam_data_array[cam_data_mask_index],
		                 	cam_data_array[cam_data_mask_index+1],
		                 	cam_data_array[cam_data_mask_index+2],
		                 	cam_data_array[cam_data_mask_index+3]};
            	       cam_mask_x288 = {cam_mask_array[cam_data_mask_index],
                                 	cam_mask_array[cam_data_mask_index+1],
                                 	cam_mask_array[cam_data_mask_index+2],
                                 	cam_mask_array[cam_data_mask_index+3]};
		       #0;

		       for (cambit=0; cambit<=`FOUR_TIMES_REG_WIDTH-1; cambit=cambit+1)
              		 begin
			    if (~global_mask_x288[cambit])
			      combined_mask_x288[cambit] = global_mask_x288[cambit];
			    else
			      combined_mask_x288[cambit] = cam_mask_x288[cambit];
              		 end

		       #0;

		       //$display("\n\nDATA = %x -- INDEX = %x", cam_data_x288,cam_data_mask_index);
		       //$display("DATA = %x",{dq_cycle_dataA,dq_cycle_dataB,dq_cycle_dataC,dq_cycle_dataD});

		       if (find_miss ?
			   (({dq_cycle_dataA,dq_cycle_dataB,dq_cycle_dataC,dq_cycle_dataD} & combined_mask_x288) !=
			   (cam_data_x288 & combined_mask_x288))
			   :(({dq_cycle_dataA,dq_cycle_dataB,dq_cycle_dataC,dq_cycle_dataD} & combined_mask_x288) ==
			   (cam_data_x288 & combined_mask_x288) ))


														 
			 begin

			    
`ifdef CAM_4MEG
    			    if (cfg_info[cam_data_mask_index[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-3]] ==2)
			      begin
				 multihit = pre_lho?1:0;
            			 pre_lho = 1'b1;
				 if (~multihit)
				   pre_search_success_index = cam_data_mask_index; 
			      end
			    else
			      begin
				 if (~pre_lho)
				     begin
				 	pre_lho = 1'b0;
				 	pre_search_success_index = {`INDEX_WIDTH {1'b1} }; //'hffff;
				     end				 
			      end
`else
    			//    if (cfg_info[cam_data_mask_index[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2]] ==2)   //original code
			      if ((cfg_info[cam_data_mask_index[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2]] ==2) || (cfg_info[cam_data_mask_index[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2]] ==1) || (cfg_info[cam_data_mask_index[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2]] ==0))	// modified by HUJ for 272 search in 136 bit partition		
			      begin
				 multihit = pre_lho?1:0;
            			 pre_lho = 1'b1;
				 if (~multihit)
				   pre_search_success_index = cam_data_mask_index; 
			      end
			    else
			      begin
				 if (~pre_lho)
				     begin
				 	pre_lho = 1'b0;
				 	pre_search_success_index = {`INDEX_WIDTH {1'b1} }; //'hffff;
				     end				 
			      end



`endif
			    

			    
			 end
			 //***************** HUJ add this piece code for 272 bit search in 68 bit partition**********
			 else if( (((dq_cycle_dataA & combined_mask_x288[271:204]) == (cam_data_x288[271:204] & combined_mask_x288[271:204])) || ((dq_cycle_dataB & combined_mask_x288[203:136]) == (cam_data_x288[203:136] & combined_mask_x288[203:136]))) 
			 		&& (((dq_cycle_dataC & combined_mask_x288[135:68]) == (cam_data_x288[135:68] & combined_mask_x288[135:68])) || ((dq_cycle_dataB & combined_mask_x288[67:0]) == (cam_data_x288[67:0] & combined_mask_x288[67:0]))) )
			 begin
				 if(cfg_info[cam_data_mask_index[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2]] ==0)
			 		begin
			 		 multihit = pre_lho?1:0;
            					 pre_lho = 1'b1;
					 if (~multihit)
				   	pre_search_success_index = cam_data_mask_index; 
			 		end
			 	 else
			     		 begin
				 		if (~pre_lho)
				    		 begin
				 			pre_lho = 1'b0;
				 			pre_search_success_index = {`INDEX_WIDTH {1'b1} }; //'hffff;
				     		end				 
			      		end	
			 end
			 //******************************************************************************************
		       else
			 begin
			    if (~pre_lho)
			      begin
				 pre_lho = 1'b0;
				 pre_search_success_index = {`INDEX_WIDTH {1'b1} }; //'hffff;
			      end
			    
			 end
		       
		       #0;

		       //$display("index = %x, pre_lho = %b, pre_search_success_index = %x",cam_data_mask_index,pre_lho, pre_search_success_index);
	               cam_data_mask_index = cam_data_mask_index + 4;
		    end
		   
		  else
		    begin
	               cam_data_xREG_WIDTH_0 =  cam_data_array[cam_data_mask_index];
	               cam_mask_xREG_WIDTH_0 =  cam_mask_array[cam_data_mask_index];
	               cam_data_xREG_WIDTH_1 = cam_data_array[cam_data_mask_index+1];
	               cam_mask_xREG_WIDTH_1 = cam_mask_array[cam_data_mask_index+1];

                       #0;

		       //$display("\n\nDATA0 = %x, DATA1 = %x -- INDEX = %x", cam_data_xREG_WIDTH_0, cam_data_xREG_WIDTH_1,cam_data_mask_index);
		       
		       for (cambit=0; cambit<=`REG_WIDTH - 1; cambit=cambit+1)
              		 begin
			    if (~global_mask_xREG_WIDTH_0[cambit])
			      combined_mask_xREG_WIDTH_0[cambit] = global_mask_xREG_WIDTH_0[cambit];   
			    else
			      combined_mask_xREG_WIDTH_0[cambit] = cam_mask_xREG_WIDTH_0[cambit];     
              		 end

		       for (cambit=0; cambit<=`REG_WIDTH - 1; cambit=cambit+1)
			 begin
			    if (~global_mask_xREG_WIDTH_1[cambit])
			      combined_mask_xREG_WIDTH_1[cambit] = global_mask_xREG_WIDTH_1[cambit];
			    else
			      combined_mask_xREG_WIDTH_1[cambit] = cam_mask_xREG_WIDTH_1[cambit];
			 end
		       #0;
		       
                       if (find_miss?
                           ((dq_cycle_dataA  & combined_mask_xREG_WIDTH_0) != 
			   (cam_data_xREG_WIDTH_0 & combined_mask_xREG_WIDTH_0))
			   : ((dq_cycle_dataA  & combined_mask_xREG_WIDTH_0) == 
			   (cam_data_xREG_WIDTH_0 & combined_mask_xREG_WIDTH_0)))
									   
			 begin
			    pre_lho_0 = 1'b1;
			    pre_search_success_index_0 = cam_data_mask_index;
			    //************* code added by HUJ to match with the behavior of board**********
			    if(cam_data_mask_index % 4 == 2)   
			    partition272_pre_lho_0 = 1'b1;   
			    else
			    partition272_pre_lho_0 = 1'b0;     
			    //*****************************************************************************
			 end
		       else
			 begin
			    pre_lho_0 = 1'b0;
			    pre_search_success_index_0 = 16'hffff;
			    partition272_pre_lho_0 = 1'b0;    // added by HUJ
			 end

                       if (find_miss?
			   ((dq_cycle_dataB  & combined_mask_xREG_WIDTH_1) != 
			   (cam_data_xREG_WIDTH_1 & combined_mask_xREG_WIDTH_1))
			   : ((dq_cycle_dataB  & combined_mask_xREG_WIDTH_1) == 
			   (cam_data_xREG_WIDTH_1 & combined_mask_xREG_WIDTH_1)))
									   
			 begin
			    pre_lho_1 = 1'b1;
			    pre_search_success_index_1 = {cam_data_mask_index[`LOG_ARRAY_SIZE-1:1],1'b1};
			    //************* code added by HUJ to match with the behavior of board**********
			    if({cam_data_mask_index[`LOG_ARRAY_SIZE-1:1],1'b1} % 4 == 3)   
			    partition272_pre_lho_1 = 1'b1;   
			    else
			    partition272_pre_lho_1 = 1'b0;     
			    //*****************************************************************************
			 end
		       else
			 begin
			    pre_lho_1 = 1'b0;
			    pre_search_success_index_1 = {`LOG_ARRAY_SIZE{1'b1}} ; 
			    partition272_pre_lho_1 = 1'b0;    // added by HUJ
			 end

	               #0;

		       //$display("pre_lho_0 = %b, pre_search_success_index_0 = %x",pre_lho_0, pre_search_success_index_0);
		       //$display("pre_lho_1 = %b, pre_search_success_index_1 = %x",pre_lho_1, pre_search_success_index_1);
		       
		       if (((pre_lho_0 & pre_lho_1) && (cfg_info[pre_search_success_index_0[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-/*3*/2]]==1))/* && sample_search_x144 && cfg_l || (pre_lho_0 & pre_lho_1 & ~cfg_l)*/)  //commented out by HUJ
			 begin
			    multihit = pre_lho?1:0;
			    pre_lho = 1'b1;
			    if (~multihit)
			      pre_search_success_index = pre_search_success_index_0;
			 end
			 //*********************** code added by HUJ to match with the behavior of board***********************
			 else if(((partition272_pre_lho_0 & partition272_pre_lho_1) && (cfg_info[pre_search_success_index_0[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2]]==2)))
			  begin
			    multihit = pre_lho?1:0;
			    pre_lho = 1'b1;
			    if (~multihit)
			      pre_search_success_index = pre_search_success_index_0;
			 end

			 //****************************************************************************************************
		      else if (pre_lho_0 | pre_lho_1)
		    	begin
			    pre_search_success_index_64 = (pre_lho_0) ? pre_search_success_index_0 :
                                                          pre_search_success_index_1 ;
			    #0;
`ifdef CAM_4MEG
			    if((cfg_info[pre_search_success_index_64[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-3]]==0)
			       && sample_search_x72)
			      begin
				   multihit =((pre_lho_0 & pre_lho_1) | pre_lho )?1:0;
                                   first_hit = pre_lho ? 1:0 ; 
				   pre_lho = 1'b1;
				   if (~first_hit) 
				     pre_search_success_index = pre_search_success_index_64;
			      end
			    else if((cfg_info[pre_search_success_index_64[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-3]]==1)
				    && sample_search_x144)
			      begin
				   if (~pre_lho)
				     begin
				  	pre_lho = 1'b0;
				  	pre_search_success_index = { `INDEX_WIDTH{1'b1}};
				     end
			      end
			    
`else // !ifdef CAM_4MEG
			    if(cfg_info[pre_search_success_index_64[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2]]==0)
			      begin
				   multihit = ((pre_lho_0 & pre_lho_1) | pre_lho )?1:0;
                                   first_hit = pre_lho ? 1:0 ; 
				   pre_lho = 1'b1;
				   if (~first_hit) 
				     pre_search_success_index = pre_search_success_index_64;
			      end
			    else if(cfg_info[pre_search_success_index_64[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2]]==1)
			      begin
				   if (~pre_lho)
				     begin
				  	pre_lho = 1'b0;
				  	pre_search_success_index = { `INDEX_WIDTH{1'b1}};
				     end
			      end


`endif // !ifdef CAM_4MEG
			    
			 end
		       else
			 begin
			    if (~pre_lho)
			      begin
				 pre_lho = 1'b0;
				 pre_search_success_index = {`INDEX_WIDTH {1'b1}};
			      end
			    
			 end

	  	       #0;

		       //$display("pre_lho = %b, pre_search_success_index = %x",pre_lho, pre_search_success_index);
		       
	               cam_data_mask_index = cam_data_mask_index + 2;
		    end
		  #0;
	       end
	  end
    	else
	  begin
	     pre_lho = 1'b0;
	     multihit = 1'b0;
	     
             pre_search_success_index = `INDEX_WIDTH'h0;
	  end
     end


   always @(posedge clk) 
     begin
   	search_op_pipe1     <= #D search_op;
     end

   always @(posedge clk)
    begin
    //#(D * 1);
    search_result_pipe2 <=  {1'b1,search_op_pipe1, cmd_ssr_index, pre_search_success_index, pre_lho};
    end
   always @(posedge clk) search_result_pipe3 <= #D search_result_pipe2; 
   always @(posedge clk) search_result_pipe4 <= #D search_result_pipe3;

   always @(posedge clk) multihit_pipe2 <= #D multihit;
   
   always @(posedge clk) multihit_pipe3 <= #D multihit_pipe2; 
   always @(posedge clk) multihit_pipe4 <= #D multihit_pipe3;

   always @(posedge clk) search_result_pipe5 <= #D {(~|lhi_dly),
						    `ifdef CAM_4MEG
						    search_result_pipe4[20:1],
						    `else
						    search_result_pipe4[19:1],
						    `endif						 
   
						    (search_result_pipe4[0]  & ~|lhi_dly)};
						    `ifdef CAM_4MEG
   always @(posedge clk) search_result_pipe6 <= #D {(search_result_pipe5[21] & ~|bhi_dly),
						    search_result_pipe5[20:1], 
						    (search_result_pipe5[0]  & ~|bhi_dly)};
						    `else
   always @(posedge clk) search_result_pipe6 <= #D {(search_result_pipe5[20] & ~|bhi_dly),
						    search_result_pipe5[19:1], 
						    (search_result_pipe5[0]  & ~|bhi_dly)};
						    `endif

   assign ref_lho = (deve & search_result_pipe4[0]) ? 2'b11 : 2'b00;   //changed by HUJ
   
   assign ref_multihit = deve & multihit_pipe4;

   
   always @(posedge clk) ref_lho_pipe1 <= #D ref_lho;
   always @(posedge clk) ref_lho_pipe2 <= #D ref_lho_pipe1;

   assign local_hit = (tlsz === 2'b00) ? (ref_lho==2'b11) :           
	  (tlsz === 2'b01) ? (ref_lho_pipe1==2'b11) :
	  (ref_lho_pipe2==2'b11) ;
	//changed by HUJ   
  // always @(posedge clk) ref_bho <= #D (deve & (search_result_pipe4[0] | (|lhi_dly)) & (tlsz == 2'h2)); //original code
//************************ code added by HUJ **********************************
	always @(posedge clk) 
	if(deve & (search_result_pipe4[0] | (|lhi_dly)) & (tlsz == 2'h2))
	ref_bho <= #D 3'b111;
	else
	ref_bho <= #D 3'b000;
//*****************************************************************************	
	
   assign search_result = (tlsz === 2'b00) ? search_result_pipe4 :
	  (tlsz === 2'b01) ? search_result_pipe5 :
	  search_result_pipe6 ;
`ifdef CAM_4MEG
   assign wr_ssr_reg0 = search_result[20] & (search_result[19:17] === 3'h0);
   assign wr_ssr_reg1 = search_result[20] & (search_result[19:17] === 3'h1);
   assign wr_ssr_reg2 = search_result[20] & (search_result[19:17] === 3'h2);
   assign wr_ssr_reg3 = search_result[20] & (search_result[19:17] === 3'h3);
   assign wr_ssr_reg4 = search_result[20] & (search_result[19:17] === 3'h4);
   assign wr_ssr_reg5 = search_result[20] & (search_result[19:17] === 3'h5);
   assign wr_ssr_reg6 = search_result[20] & (search_result[19:17] === 3'h6);
   assign wr_ssr_reg7 = search_result[20] & (search_result[19:17] === 3'h7);
   assign ssr_reg_value  = (wr_ssr_reg0) ? ssr_reg0[15:0] :
	  (wr_ssr_reg1) ? ssr_reg1[15:0] :
	  (wr_ssr_reg2) ? ssr_reg2[15:0] :
	  (wr_ssr_reg3) ? ssr_reg3[15:0] :
	  (wr_ssr_reg4) ? ssr_reg4[15:0] :
	  (wr_ssr_reg5) ? ssr_reg5[15:0] :
	  (wr_ssr_reg6) ? ssr_reg6[15:0] :
	  ssr_reg7[15:0] ;

   assign wr_ssr_value = (search_result[0]) ? {40'h0, 1'b1, 15'h0, search_result[16:1]} :
	  (local_hit)        ? {40'h0, 1'b0, 15'h0, search_result[16:1]} :
	  {40'h0, 1'b0, 15'h0, ssr_reg_value}       ;

   assign ssv_ssf_pipe0 = {search_result[21], search_result[20],search_result[0]};
`else // !ifdef CAM_4MEG
`ifdef CAM_1MEG
   assign wr_ssr_reg0 = search_result[18] & (search_result[17:15] === 3'h0);
   assign wr_ssr_reg1 = search_result[18] & (search_result[17:15] === 3'h1);
   assign wr_ssr_reg2 = search_result[18] & (search_result[17:15] === 3'h2);
   assign wr_ssr_reg3 = search_result[18] & (search_result[17:15] === 3'h3);
   assign wr_ssr_reg4 = search_result[18] & (search_result[17:15] === 3'h4);
   assign wr_ssr_reg5 = search_result[18] & (search_result[17:15] === 3'h5);
   assign wr_ssr_reg6 = search_result[18] & (search_result[17:15] === 3'h6);
   assign wr_ssr_reg7 = search_result[18] & (search_result[17:15] === 3'h7);
   assign ssr_reg_value  = (wr_ssr_reg0) ? ssr_reg0[13:0] :
	  (wr_ssr_reg1) ? ssr_reg1[13:0] :
	  (wr_ssr_reg2) ? ssr_reg2[13:0] :
	  (wr_ssr_reg3) ? ssr_reg3[13:0] :
	  (wr_ssr_reg4) ? ssr_reg4[13:0] :
	  (wr_ssr_reg5) ? ssr_reg5[13:0] :
	  (wr_ssr_reg6) ? ssr_reg6[13:0] :
	  ssr_reg7[13:0] ;
   assign wr_ssr_value = (search_result[0]) ? {36'h0, 1'b1, 17'h0, search_result[14:1]} :
	  (local_hit)        ? {36'h0, 1'b0, 17'h0, search_result[14:1]} :
	  {36'h0, 1'b0, 17'h0, ssr_reg_value}       ; 
   assign ssv_ssf_pipe0 = {search_result[19], search_result[18],search_result[0]};     
`else
   assign wr_ssr_reg0 = search_result[19] & (search_result[18:16] === 3'h0);
   assign wr_ssr_reg1 = search_result[19] & (search_result[18:16] === 3'h1);
   assign wr_ssr_reg2 = search_result[19] & (search_result[18:16] === 3'h2);
   assign wr_ssr_reg3 = search_result[19] & (search_result[18:16] === 3'h3);
   assign wr_ssr_reg4 = search_result[19] & (search_result[18:16] === 3'h4);
   assign wr_ssr_reg5 = search_result[19] & (search_result[18:16] === 3'h5);
   assign wr_ssr_reg6 = search_result[19] & (search_result[18:16] === 3'h6);
   assign wr_ssr_reg7 = search_result[19] & (search_result[18:16] === 3'h7);
   assign ssr_reg_value  = (wr_ssr_reg0) ? ssr_reg0[14:0] :
	  (wr_ssr_reg1) ? ssr_reg1[14:0] :
	  (wr_ssr_reg2) ? ssr_reg2[14:0] :
	  (wr_ssr_reg3) ? ssr_reg3[14:0] :
	  (wr_ssr_reg4) ? ssr_reg4[14:0] :
	  (wr_ssr_reg5) ? ssr_reg5[14:0] :
	  (wr_ssr_reg6) ? ssr_reg6[14:0] :
	  ssr_reg7[14:0] ;
   assign wr_ssr_value = (search_result[0]) ? {36'h0, 1'b1, 16'h0, search_result[15:1]} :
	  (local_hit)        ? {36'h0, 1'b0, 16'h0, search_result[15:1]} :
	  {36'h0, 1'b0, 16'h0, ssr_reg_value}       ;
   assign ssv_ssf_pipe0 = {search_result[20], search_result[19],search_result[0]};  
`endif // !ifdef CAM_1MEG

`endif // !ifdef CAM_4MEG

   
   

   always @(posedge clk) ssv_ssf_pipe1 <= #D ssv_ssf_pipe0;
   always @(posedge clk) ssv_ssf_pipe2 <= #D ssv_ssf_pipe1;
   always @(posedge clk) ssv_ssf_pipe3 <= #D ssv_ssf_pipe2;
   always @(posedge clk) ssv_ssf_pipe4 <= #D ssv_ssf_pipe3;
   always @(posedge clk) ssv_ssf_pipe5 <= #D ssv_ssf_pipe4;
   always @(posedge clk) ssv_ssf_pipe6 <= #D ssv_ssf_pipe5;
   always @(posedge clk) ssv_ssf_pipe7 <= #D ssv_ssf_pipe6;

   assign {global_miss, ref_ssv, ref_ssf} = (hlat === 3'h0) ? ssv_ssf_pipe0 :
          (hlat === 3'h1) ? ssv_ssf_pipe1 :
          (hlat === 3'h2) ? ssv_ssf_pipe2 :
          (hlat === 3'h3) ? ssv_ssf_pipe3 :
          (hlat === 3'h4) ? ssv_ssf_pipe4 :
          (hlat === 3'h5) ? ssv_ssf_pipe5 :
          (hlat === 3'h6) ? ssv_ssf_pipe6 :
          ssv_ssf_pipe7 ;

   assign ref_oe_ssv = ~rst_l ? 0: (deve & ((lcam & ~ref_ssv)    | 
					    (lcam & global_miss) |
					    (ref_ssv & ref_ssf))) ;
   assign ref_oe_ssf = ref_oe_ssv;

   /*************************** LEARN **************************************/
   // NOTE: next_free_addr and nfa_reg are NOT meant for x288 mode.

   always @(posedge clk) cam_data_wr_pipe1 <= #D cam_data_wr;
   always @(posedge clk) cam_data_wr_pipe2 <= #D cam_data_wr_pipe1;

   assign wr_nfa_reg = (cam_data_wr_pipe2 | learn_op_pipe2);
  
 
   always @(negedge clk)
     if (~reset_l)
       begin
	  #D;
	  next_free_addr = `LOG_ARRAY_SIZE'h0;
       end
     else if (wr_nfa_reg)
       begin 
	  #D;	
	  next_free_addr = `LOG_ARRAY_SIZE'h0;
          
	  calc_nfa_done  = 1'b0;
	  #0;
	  
	  cam_rd_data0   = cam_data_array[{next_free_addr[`LOG_ARRAY_SIZE-1:1],1'b0}]; 
	  cam_rd_data1   = cam_data_array[{next_free_addr[`LOG_ARRAY_SIZE-1:1],1'b1}]; 
	  cam_rd_data2   = cam_data_array[{next_free_addr[`LOG_ARRAY_SIZE-1:2],2'b10}]; 
	  cam_rd_data3   = cam_data_array[{next_free_addr[`LOG_ARRAY_SIZE-1:2],2'b11}]; 
	  #0;

	  cbit0          = cam_rd_data0[0];
	  cbit1          = cam_rd_data1[0];
	  cbit2          = cam_rd_data2[0];
	  cbit3          = cam_rd_data3[0];
	  #0;

 `ifdef CAM_4MEG
	  	  
	  case (next_free_addr[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-3])
	    0: if (cfg0 == 2'h0)
	      cbit = (next_free_addr[0]) ? cbit1 : cbit0;
	    else if (cfg0 == 2'h1)
	      cbit = cbit0 | cbit1;
	    else
	      cbit = cbit0 | cbit1 | cbit2 | cbit3;
	    1: if (cfg1 == 2'h0)
	      cbit = (next_free_addr[0]) ? cbit1 : cbit0;
	    else if (cfg1 == 2'h1)
	      cbit = cbit0 | cbit1;
	    else
	      cbit = cbit0 | cbit1 | cbit2 | cbit3;
	    2: if (cfg2 == 2'h0)
	      cbit = (next_free_addr[0]) ? cbit1 : cbit0;
	    else if (cfg2 == 2'h1)
	      cbit = cbit0 | cbit1;
	    else
	      cbit = cbit0 | cbit1 | cbit2 | cbit3;
	    3: if (cfg3 == 2'h0)
	      cbit = (next_free_addr[0]) ? cbit1 : cbit0;
	    else if (cfg3 == 2'h1)
	      cbit = cbit0 | cbit1;
	    else
	      cbit = cbit0 | cbit1 | cbit2 | cbit3;
	    4: if (cfg4 == 2'h0)
	      cbit = (next_free_addr[0]) ? cbit1 : cbit0;
	    else if (cfg4 == 2'h1)
	      cbit = cbit0 | cbit1;
	    else
	      cbit = cbit0 | cbit1 | cbit2 | cbit3;
	    5: if (cfg5 == 2'h0)
	      cbit = (next_free_addr[0]) ? cbit1 : cbit0;
	    else if (cfg5 == 2'h1)
	      cbit = cbit0 | cbit1;
	    else
	      cbit = cbit0 | cbit1 | cbit2 | cbit3;
	    6: if (cfg6 == 2'h0)
	      cbit = (next_free_addr[0]) ? cbit1 : cbit0;
	    else if (cfg6 == 2'h1)
	      cbit = cbit0 | cbit1;
	    else
	      cbit = cbit0 | cbit1 | cbit2 | cbit3;
	    7: if (cfg7 == 2'h0)
	      cbit = (next_free_addr[0]) ? cbit1 : cbit0;
	    else if (cfg7 == 2'h1)
	      cbit = cbit0 | cbit1;
	    else
	      cbit = cbit0 | cbit1 | cbit2 | cbit3;
	    
	  endcase // case(next_free_addr[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2])
 `else // !ifdef CAM_4MEG
	  
	  
	  case (next_free_addr[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2])
	    2'h0: if (cfg0 == 2'h0)
	      cbit = (next_free_addr[0]) ? cbit1 : cbit0;
	    else if (cfg0 == 2'h1)
	      cbit = cbit0 | cbit1;
	    //else     //orignal code
	      else if(cfg0 == 2'h2)   //Added by HUJ for reserve mode
	      cbit = cbit0 | cbit1 | cbit2 | cbit3;
	      else  //Added by HUJ for reserve mode
	      cbit = 1'b1;		//Added by HUJ for reserve mode
	    2'h1: if (cfg1 == 2'h0)
	      cbit = (next_free_addr[0]) ? cbit1 : cbit0;
	    else if (cfg1 == 2'h1)
	      cbit = cbit0 | cbit1;
	    //else   //orignal code
	    else if(cfg1 == 2'h2)  //Added by HUJ for reserve mode
	      cbit = cbit0 | cbit1 | cbit2 | cbit3;
	      else  //Added by HUJ for reserve mode
	      cbit = 1'b1;   //Added by HUJ for reserve mode
	    2'h2: if (cfg2 == 2'h0)
	      cbit = (next_free_addr[0]) ? cbit1 : cbit0;
	    else if (cfg2 == 2'h1)
	      cbit = cbit0 | cbit1;
	   // else        //orignal code
	   else if(cfg2 == 2'h2)			//Added by HUJ for reserve mode
	      cbit = cbit0 | cbit1 | cbit2 | cbit3;
	      else			//Added by HUJ for reserve mode
	      cbit = 1'b1;			//Added by HUJ for reserve mode
	    2'h3: if (cfg3 == 2'h0)
	      cbit = (next_free_addr[0]) ? cbit1 : cbit0;
	    else if (cfg3 == 2'h1)
	      cbit = cbit0 | cbit1;
	    //else		//orignal code
	    else if(cfg3 == 2'h2)			//Added by HUJ for reserve mode
	      cbit = cbit0 | cbit1 | cbit2 | cbit3;
	      else			//Added by HUJ for reserve mode
	      cbit = 1'b1; 			//Added by HUJ for reserve mode
	  endcase // case(next_free_addr[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2])
`endif // !ifdef CAM_4MEG
	  
	  #0;

	  //$display("--1-- DATA0 = %x, DATA1 = %x, CBIT0 = %b, CBIT1 = %b, CBIT = %b, NFA = %x",cam_rd_data0,cam_rd_data1,cbit0,cbit1,cbit, next_free_addr);

	  //      while (cbit & (next_free_addr[`LOG_ARRAY_SIZE-1:0] != {`LOG_ARRAY_SIZE{1'b1}}))
	  while (cbit & ~calc_nfa_done)
            begin
`ifdef CAM_4MEG
	       case (next_free_addr[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-3])
		 0: if (cfg0 == 2'h0)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:0] != {`LOG_ARRAY_SIZE{1'b1}})
            		next_free_addr = next_free_addr + 1;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
	  	 else if (cfg0 == 2'h1)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:1] != {`LOG_ARRAY_SIZE-1{1'b1}})
	    		next_free_addr = next_free_addr + 2;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 else
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:2] != {`LOG_ARRAY_SIZE-2{1'b1}})
			next_free_addr = next_free_addr + 4;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 1: if (cfg1 == 2'h0)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:0] != {`LOG_ARRAY_SIZE{1'b1}})
            		next_free_addr = next_free_addr + 1;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
	  	 else if (cfg1 == 2'h1)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:1] != {`LOG_ARRAY_SIZE-1{1'b1}})
	    		next_free_addr = next_free_addr + 2;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 else
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:2] != {`LOG_ARRAY_SIZE-2{1'b1}})
			next_free_addr = next_free_addr + 4;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 2: if (cfg2 == 2'h0)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:0] != {`LOG_ARRAY_SIZE{1'b1}})
            		next_free_addr = next_free_addr + 1;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
	  	 else if (cfg2 == 2'h1)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:1] != {`LOG_ARRAY_SIZE-1{1'b1}})
	    		next_free_addr = next_free_addr + 2;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 else
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:2] != {`LOG_ARRAY_SIZE-2{1'b1}})
			next_free_addr = next_free_addr + 4;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 3: if (cfg3 == 2'h0)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:0] != {`LOG_ARRAY_SIZE{1'b1}})
            		next_free_addr = next_free_addr + 1;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
	  	 else if (cfg3 == 2'h1)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:1] != {`LOG_ARRAY_SIZE-1{1'b1}})
	    		next_free_addr = next_free_addr + 2;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 else
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:2] != {`LOG_ARRAY_SIZE-2{1'b1}})
			next_free_addr = next_free_addr + 4;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 4: if (cfg4 == 2'h0)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:0] != {`LOG_ARRAY_SIZE{1'b1}})
            		next_free_addr = next_free_addr + 1;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
	  	 else if (cfg4 == 2'h1)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:1] != {`LOG_ARRAY_SIZE-1{1'b1}})
	    		next_free_addr = next_free_addr + 2;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 else
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:2] != {`LOG_ARRAY_SIZE-2{1'b1}})
			next_free_addr = next_free_addr + 4;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 5: if (cfg5 == 2'h0)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:0] != {`LOG_ARRAY_SIZE{1'b1}})
            		next_free_addr = next_free_addr + 1;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
	  	 else if (cfg5 == 2'h1)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:1] != {`LOG_ARRAY_SIZE-1{1'b1}})
	    		next_free_addr = next_free_addr + 2;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 else
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:2] != {`LOG_ARRAY_SIZE-2{1'b1}})
			next_free_addr = next_free_addr + 4;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 6: if (cfg6 == 2'h0)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:0] != {`LOG_ARRAY_SIZE{1'b1}})
            		next_free_addr = next_free_addr + 1;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
	  	 else if (cfg6 == 2'h1)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:1] != {`LOG_ARRAY_SIZE-1{1'b1}})
	    		next_free_addr = next_free_addr + 2;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 else
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:2] != {`LOG_ARRAY_SIZE-2{1'b1}})
			next_free_addr = next_free_addr + 4;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 7: if (cfg7 == 2'h0)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:0] != {`LOG_ARRAY_SIZE{1'b1}})
            		next_free_addr = next_free_addr + 1;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
	  	 else if (cfg7 == 2'h1)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:1] != {`LOG_ARRAY_SIZE-1{1'b1}})
	    		next_free_addr = next_free_addr + 2;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		 else
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:2] != {`LOG_ARRAY_SIZE-2{1'b1}})
			next_free_addr = next_free_addr + 4;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
	       endcase // case(next_free_addr[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2])

`else
	 /*******************************  HUJ Command this away ******************************************      
	       case (next_free_addr[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2])
		 2'h0: if (cfg0 == 2'h0)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:0] != {`LOG_ARRAY_SIZE{1'b1}})
            		next_free_addr = next_free_addr + 1;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
	  	 else if (cfg0 == 2'h1)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:1] != {`LOG_ARRAY_SIZE-1{1'b1}})
	    		next_free_addr = next_free_addr + 2;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		   //else    // orignal code
		 else if (cfg0 == 2'h2)   // added by HUJ for reserved mode
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:2] != {`LOG_ARRAY_SIZE-2{1'b1}})
			next_free_addr = next_free_addr + 4;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		  else			// added by HUJ for reserved mode
		  	begin  	 // added by HUJ for reserved mode
		  	 next_free_addr = (1 << `LOG_ARRAY_SIZE)/4;			// added by HUJ for reserved mode
		  	
		  	end		   // added by HUJ for reserved mode
		 2'h1: if (cfg1 == 2'h0)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:0] != {`LOG_ARRAY_SIZE{1'b1}})
            		next_free_addr = next_free_addr + 1;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
	  	 else if (cfg1 == 2'h1)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:1] != {`LOG_ARRAY_SIZE-1{1'b1}})
	    		next_free_addr = next_free_addr + 2;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		// else   // original code
		else if(cfg1 == 2'h2)  //added by HUJ for reserved mode
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:2] != {`LOG_ARRAY_SIZE-2{1'b1}})
			next_free_addr = next_free_addr + 4;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		   else 			//added by HUJ for reserved mode
		   begin	  		//added by HUJ for reserved mode
		   next_free_addr = (1 << `LOG_ARRAY_SIZE)/2;	  //added by HUJ for reserved mode
		   end				  //added by HUJ for reserved mode
		 2'h2: if (cfg2 == 2'h0)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:0] != {`LOG_ARRAY_SIZE{1'b1}})
            		next_free_addr = next_free_addr + 1;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
	  	 else if (cfg2 == 2'h1)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:1] != {`LOG_ARRAY_SIZE-1{1'b1}})
	    		next_free_addr = next_free_addr + 2;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
                         
		   end
		 //  else         // original code
		 else if (cfg2 == 2'h2)    //added by HUJ for reserved mode
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:2] != {`LOG_ARRAY_SIZE-2{1'b1}})
			next_free_addr = next_free_addr + 4;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		   else			    //added by HUJ for reserved mode
		   begin				    //added by HUJ for reserved mode
		   next_free_addr = (1 << `LOG_ARRAY_SIZE)*3/4;	    //added by HUJ for reserved mode
		   end			    //added by HUJ for reserved mode
		 2'h3: if (cfg3 == 2'h0)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:0] != {`LOG_ARRAY_SIZE{1'b1}})
            		next_free_addr = next_free_addr + 1;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
	  	 else if (cfg3 == 2'h1)
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:1] != {`LOG_ARRAY_SIZE-1{1'b1}})
	    		next_free_addr = next_free_addr + 2;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		   //else    // original code
		 else if(cfg3 == 2'h2)       //added by HUJ for reserved mode
		   begin
		      if (next_free_addr[`LOG_ARRAY_SIZE-1:2] != {`LOG_ARRAY_SIZE-2{1'b1}})
			next_free_addr = next_free_addr + 4;
		      else
                        begin
			calc_nfa_done = 1'b1;
                        end
		   end
		   else        //added by HUJ for reserved mode
		     calc_nfa_done = 1'b1;        //added by HUJ for reserved mode
	       endcase // case(next_free_addr[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2])
 *******************************  HUJ Command this away ******************************************/ 
 
 
 //*******************************HUJ edit this piece of code ************************************
   case (next_free_addr[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2])
 		2'h0: begin
 				if(((next_free_addr == `LAST_PARTITION_0_ADDR) & (cfg0 == 2'h0))  || 
 			   	((next_free_addr == (`LAST_PARTITION_0_ADDR-1)) & (cfg0 == 2'h1)) ||
 			   	((next_free_addr == (`LAST_PARTITION_0_ADDR-3)) & (cfg0 == 2'h2)) ||
 			   	(cfg0 == 2'h3) )
 					begin
 					if(cfg1 != 2'h3)
 					next_free_addr = `LAST_PARTITION_0_ADDR + 1;
 					else if (cfg2 != 2'h3)
 					next_free_addr = `LAST_PARTITION_1_ADDR + 1;
 					else if (cfg3 != 2'h3)
 					next_free_addr = `LAST_PARTITION_2_ADDR + 1;
 					else begin
 					next_free_addr = `LAST_PARTITION_3_ADDR;
 					calc_nfa_done = 1'b1;
 					     end
 					end
 				else	
 					begin
 					if(cfg0 == 2'h0)
 					next_free_addr = next_free_addr + 1;
 					else if (cfg0 == 2'h1)
 					next_free_addr = next_free_addr + 2;
 					else if (cfg0 == 2'h2)
 					next_free_addr = next_free_addr + 4;
 					end
 			end  
 			
 		2'h1: begin
 				if(((next_free_addr == `LAST_PARTITION_1_ADDR) & (cfg1 == 2'h0))  || 
 			   	((next_free_addr == (`LAST_PARTITION_1_ADDR-1)) & (cfg1 == 2'h1)) ||
 			   	((next_free_addr == (`LAST_PARTITION_1_ADDR-3)) & (cfg1 == 2'h2)) ||
 			   	(cfg1 == 2'h3) )
 					begin
 					if(cfg2 != 2'h3)
 					next_free_addr = `LAST_PARTITION_1_ADDR + 1;
 					else if (cfg3 != 2'h3)
 					next_free_addr = `LAST_PARTITION_2_ADDR + 1;
 					else begin
 					next_free_addr = `LAST_PARTITION_3_ADDR;
 					calc_nfa_done = 1'b1;
 					     end
 					end
 				else	
 					begin
 					if(cfg1 == 2'h0)
 					next_free_addr = next_free_addr + 1;
 					else if (cfg1 == 2'h1)
 					next_free_addr = next_free_addr + 2;
 					else if (cfg1 == 2'h2)
 					next_free_addr = next_free_addr + 4;
 					end
 			end  

 		2'h2: begin
 				if(((next_free_addr == `LAST_PARTITION_2_ADDR) & (cfg2 == 2'h0))  || 
 			   	((next_free_addr == (`LAST_PARTITION_2_ADDR-1)) & (cfg2 == 2'h1)) ||
 			   	((next_free_addr == (`LAST_PARTITION_2_ADDR-3)) & (cfg2 == 2'h2)) ||
 			   	(cfg2 == 2'h3) )
 					begin
 					if (cfg3 != 2'h3)
 					next_free_addr = `LAST_PARTITION_2_ADDR + 1;
 					else begin
 					next_free_addr = `LAST_PARTITION_3_ADDR;
 					calc_nfa_done = 1'b1;
 					     end
 					end
 				else	
 					begin
 					if(cfg2 == 2'h0)
 					next_free_addr = next_free_addr + 1;
 					else if (cfg2 == 2'h1)
 					next_free_addr = next_free_addr + 2;
 					else if (cfg2 == 2'h2)
 					next_free_addr = next_free_addr + 4;
 					end
 			end  
	
 		2'h3: begin
 				if(((next_free_addr == `LAST_PARTITION_3_ADDR) & (cfg3 == 2'h0))  || 
 			   	((next_free_addr == (`LAST_PARTITION_3_ADDR-1)) & (cfg3 == 2'h1)) ||
 			   	((next_free_addr == (`LAST_PARTITION_3_ADDR-3)) & (cfg3 == 2'h2)) ||
 			   	(cfg3 == 2'h3) )
 					begin
 					next_free_addr = `LAST_PARTITION_3_ADDR;
 					calc_nfa_done = 1'b1;
 					end
 				else	
 					begin
 					if(cfg3 == 2'h0)
 					next_free_addr = next_free_addr + 1;
 					else if (cfg3 == 2'h1)
 					next_free_addr = next_free_addr + 2;
 					else if (cfg3 == 2'h2)
 					next_free_addr = next_free_addr + 4;
 					end
 			end 
	endcase // case(next_free_addr[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2])
	       
 //******************************* the end of HUJ's edition *************************************************
         #0;      
   
`endif // !ifdef CAM_4MEG
                // this is used to make next free address compatible with Chip 
                // In the chip nfa is defined 16 bit 
	       
               #0; 


               cam_rd_data0 = cam_data_array[{next_free_addr[`LOG_ARRAY_SIZE-1:1],1'b0}];
               cam_rd_data1 = cam_data_array[{next_free_addr[`LOG_ARRAY_SIZE-1:1],1'b1}]; 
               cam_rd_data2 = cam_data_array[{next_free_addr[`LOG_ARRAY_SIZE-1:2],2'b10}]; 
               cam_rd_data3 = cam_data_array[{next_free_addr[`LOG_ARRAY_SIZE-1:2],2'b11}]; 
               #0;

               cbit0        = cam_rd_data0[0];
               cbit1        = cam_rd_data1[0];
               cbit2        = cam_rd_data2[0];
               cbit3        = cam_rd_data3[0];
	       #0;
	       
`ifdef CAM_4MEG
	       case (next_free_addr[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-3])
		 0: if (cfg0 == 2'h0)
                   cbit = (next_free_addr[0]) ? cbit1 : cbit0;
              	 else if (cfg0 == 2'h1)
                   cbit = cbit0 | cbit1;
		 else
		   cbit = cbit0 | cbit1 | cbit2 | cbit3;
		 1: if (cfg1 == 2'h0)
                   cbit = (next_free_addr[0]) ? cbit1 : cbit0;
                 else if (cfg1 == 2'h1)
                   cbit = cbit0 | cbit1;
		 else
		   cbit = cbit0 | cbit1 | cbit2 | cbit3;
		 2: if (cfg2 == 2'h0)
                   cbit = (next_free_addr[0]) ? cbit1 : cbit0;
              	 else if (cfg2 == 2'h1)
                   cbit = cbit0 | cbit1;
		 else
		   cbit = cbit0 | cbit1 | cbit2 | cbit3;
		 3: if (cfg3 == 2'h0)
                   cbit = (next_free_addr[0]) ? cbit1 : cbit0;
                 else if (cfg3 == 2'h1)
                   cbit = cbit0 | cbit1;
		 else
		   cbit = cbit0 | cbit1 | cbit2 | cbit3;
		 4: if (cfg4 == 2'h0)
                   cbit = (next_free_addr[0]) ? cbit1 : cbit0;
                 else if (cfg4 == 2'h1)
                   cbit = cbit0 | cbit1;
		 else
		   cbit = cbit0 | cbit1 | cbit2 | cbit3;
		 5: if (cfg5 == 2'h0)
                   cbit = (next_free_addr[0]) ? cbit1 : cbit0;
                 else if (cfg5 == 2'h1)
                   cbit = cbit0 | cbit1;
		 else
		   cbit = cbit0 | cbit1 | cbit2 | cbit3;
		 6: if (cfg6 == 2'h0)
                   cbit = (next_free_addr[0]) ? cbit1 : cbit0;
                 else if (cfg6 == 2'h1)
                   cbit = cbit0 | cbit1;
		 else
		   cbit = cbit0 | cbit1 | cbit2 | cbit3;
		 7: if (cfg7 == 2'h0)
                   cbit = (next_free_addr[0]) ? cbit1 : cbit0;
                 else if (cfg7 == 2'h1)
                   cbit = cbit0 | cbit1;
		 else
		   cbit = cbit0 | cbit1 | cbit2 | cbit3;
               endcase // case(next_free_addr[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-3])	       
`else
	       
	       case (next_free_addr[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2])
		 2'h0: if (cfg0 == 2'h0)
                   cbit = (next_free_addr[0]) ? cbit1 : cbit0;
              	 else if (cfg0 == 2'h1)
                   cbit = cbit0 | cbit1;
                   //else   //original code
		 else if(cfg0 == 2'h2)      //added by HUJ for reserved mode
		   cbit = cbit0 | cbit1 | cbit2 | cbit3;
		   else			//added by HUJ for reserved mode
		   cbit = 1'b1;       //added by HUJ for reserved mode
		 2'h1: if (cfg1 == 2'h0)
                   cbit = (next_free_addr[0]) ? cbit1 : cbit0;
                 else if (cfg1 == 2'h1)
                   cbit = cbit0 | cbit1;
                   //else   //original code
		 else if(cfg1 == 2'h2)		    //added by HUJ for reserved mode
		   cbit = cbit0 | cbit1 | cbit2 | cbit3;
		   else			    //added by HUJ for reserved mode
		   cbit = 1'b1;			    //added by HUJ for reserved mode
		 2'h2: if (cfg2 == 2'h0)
                   cbit = (next_free_addr[0]) ? cbit1 : cbit0;
              	 else if (cfg2 == 2'h1)
                   cbit = cbit0 | cbit1;
                   //else   //original code
		 else if(cfg2 == 2'h2)		    //added by HUJ for reserved mode
		   cbit = cbit0 | cbit1 | cbit2 | cbit3;
		   else			    //added by HUJ for reserved mode
		   cbit = 1'b1;				    //added by HUJ for reserved mode
		 2'h3: if (cfg3 == 2'h0)
                   cbit = (next_free_addr[0]) ? cbit1 : cbit0;
                 else if (cfg3 == 2'h1)
                   cbit = cbit0 | cbit1;
                   //else    //original code
		 else if(cfg3 == 2'h2)		    //added by HUJ for reserved mode
		   cbit = cbit0 | cbit1 | cbit2 | cbit3;
		   else 				    //added by HUJ for reserved mode
		   cbit = 1'b1;					    //added by HUJ for reserved mode
               endcase // case(next_free_addr[`LOG_ARRAY_SIZE-1:`LOG_ARRAY_SIZE-2])
`endif // !ifdef CAM_4MEG
	       
	       #0;

	       //$display("--2-- DATA0 = %x, DATA1 = %x, CBIT0 = %b, CBIT1 = %b, CBIT = %b, NFA = %x",cam_rd_data0,cam_rd_data1,cbit0,cbit1,cbit, next_free_addr);
            end
       end
     else
       begin
	  #D;
	  next_free_addr = next_free_addr;
       end

   // FULL happens when next_free addr = the last address in CAM and C-Bit is also set for that location.

   assign last_entry              = cam_data_array[`ARRAY_SIZE-1];	// xREG_WIDTH, x128
   assign last_entry_minus_1      = cam_data_array[`ARRAY_SIZE-2];	// x128 
   assign last_entry_minus_2      = cam_data_array[`ARRAY_SIZE-3];	// x288
   assign last_entry_minus_3      = cam_data_array[`ARRAY_SIZE-4];	// x288
   assign last_entry_cbit         = last_entry[0];
   assign last_entry_cbit_minus_1 = last_entry_minus_1[0];
   assign last_entry_cbit_minus_2 = last_entry_minus_2[0];
   assign last_entry_cbit_minus_3 = last_entry_minus_3[0];
`ifdef CAM_4MEG
   assign last_cfg_mode_144 = (cfg7 == 2'h1) ? 1'b1 : 1'b0 ;
   assign last_cfg_mode_288 = (cfg7 == 2'h2) ? 1'b1 : 1'b0 ;
`else
   assign last_cfg_mode_144 = (cfg3 == 2'h1) ? 1'b1 : 1'b0 ;
   assign last_cfg_mode_288 = (cfg3 == 2'h2) ? 1'b1 : 1'b0 ;
   /***** added by HUJ ******
   assign partition_0_reserved = (cfg0 == 2'b11) ? 1'b1: 1'b0;
   assign partition_1_reserved = (cfg1 == 2'b11) ? 1'b1: 1'b0;
   assign partition_2_reserved = (cfg2 == 2'b11) ? 1'b1: 1'b0;
   assign partition_3_reserved = (cfg3 == 2'b11) ? 1'b1: 1'b0;
   *************************/
`endif
   always @(posedge clk)
     if (~reset_l)
       ref_fulo <= #D 2'b00;    ///
     else
       //  ref_fulo <= #D (deve & ( ( (next_free_addr[`LOG_ARRAY_SIZE-1:1] == {`LOG_ARRAY_SIZE-1{1'b1}}) |
    /**************************** HUJ comment this section away **************************
       ref_fulo <= #D (deve & ( ( (next_free_addr[`LOG_ARRAY_SIZE-1:0] == {`LOG_ARRAY_SIZE{1'b1}})   |
				  (next_free_addr[`LOG_ARRAY_SIZE-1:1] == {`LOG_ARRAY_SIZE-1{1'b1}}) |
				  (next_free_addr[`LOG_ARRAY_SIZE-1:2] == {`LOG_ARRAY_SIZE-2{1'b1}})) &
                                ((last_cfg_mode_288 & ( (last_entry_cbit         === 1'b1) | 
							(last_entry_cbit_minus_1 === 1'b1) |
							(last_entry_cbit_minus_2 === 1'b1) |
							(last_entry_cbit_minus_3 === 1'b1))) |
                                 (last_cfg_mode_144 & ( (last_entry_cbit         === 1'b1) | 
							(last_entry_cbit_minus_1 === 1'b1))) |
                                 ((last_entry_cbit         === 1'b1) & 
				  (last_entry_cbit_minus_1 === 1'b1)))));
	*********************************************************************************/
	/********** HUJ added this section for Full signal behave like the silicon ***************
	 ref_fulo <= #D (deve & ( (~partition_3_reserved) ? 
	 			( (cfg3==2'h0) ? (next_free_addr[`LOG_ARRAY_SIZE-1:0] == {`LOG_ARRAY_SIZE{1'b1}}) 
	 			: (cfg3==2'h1) ? (next_free_addr[`LOG_ARRAY_SIZE-1:1] == {`LOG_ARRAY_SIZE-1{1'b1}})
	 			: (cfg3==2'h2) ? (next_free_addr[`LOG_ARRAY_SIZE-1:2] == {`LOG_ARRAY_SIZE-2{1'b1}}):0)
	 			: (~partition_2_reserved) ? 
	 			( (cfg2==2'h0) ? (next_free_addr[`LOG_ARRAY_SIZE-1:0] == ((`ARRAY_SIZE*3/4)-1)) 
	 			: (cfg2==2'h1) ? (next_free_addr[`LOG_ARRAY_SIZE-1:1] == ((`ARRAY_SIZE*3/4)-2))
	 			: (cfg2==2'h2) ? (next_free_addr[`LOG_ARRAY_SIZE-1:2] == ((`ARRAY_SIZE*3/4)-4)):0)
	 			: (~partition_1_reserved) ? 
	 			( (cfg1==2'h0) ? (next_free_addr[`LOG_ARRAY_SIZE-1:0] == ((`ARRAY_SIZE/2)-1)) 
	 			: (cfg1==2'h1) ? (next_free_addr[`LOG_ARRAY_SIZE-1:1] == ((`ARRAY_SIZE/2)-2))
	 			: (cfg1==2'h2) ? (next_free_addr[`LOG_ARRAY_SIZE-1:2] == ((`ARRAY_SIZE/2)-4)):0)
	 			: (~partition_0_reserved) ? 
	 			( (cfg0==2'h0) ? (next_free_addr[`LOG_ARRAY_SIZE-1:0] >= ((`ARRAY_SIZE/4)-1)) 
	 			: (cfg0==2'h1) ? (next_free_addr[`LOG_ARRAY_SIZE-1:1] == ((`ARRAY_SIZE/4)-2))
	 			: (cfg0==2'h2) ? (next_free_addr[`LOG_ARRAY_SIZE-1:2] == ((`ARRAY_SIZE/4)-4)):0)
	 			: 1));	
	*****************************************************************************************/
	//ref_fulo <= #D (deve & (next_free_addr == `LAST_PARTITION_3_ADDR));   ///original code
	if(deve & (next_free_addr == `LAST_PARTITION_3_ADDR))   //added by HUJ
	ref_fulo <= #D 2'b11;							//added by HUJ
	else									// added by HUJ
	ref_fulo <= #D 2'b00;							// added by HUJ
	
   /*
    ref_fulo <= #D (deve & ( ( (next_free_addr[`LOG_ARRAY_SIZE-1:1] == {`LOG_ARRAY_SIZE-1{1'b1}}) |
    (next_free_addr[`LOG_ARRAY_SIZE-1:1] == {`LOG_ARRAY_SIZE{1'b1}})) &
    ((last_cfg_mode_144 & (last_entry_cbit | last_entry_cbit_minus_1))             |
    (last_entry_cbit & last_entry_cbit_minus_1)                                   |
    (last_entry_cbit & dq_latched[0] & cam_data_wr &
    (cam_data_mask_addr == {next_free_addr[`LOG_ARRAY_SIZE-1:1],1'b0})) |
    (last_entry_cbit_minus_1 & dq_latched[0] & cam_data_wr &
    (cam_data_mask_addr == {next_free_addr[`LOG_ARRAY_SIZE-1:1],1'b1}))) ));
    */
   
   always @(posedge clk)
     if (~reset_l)
       ref_full <= #D 1'b0;
     else
       ref_full <= #D (ref_fulo==2'b11) & (&fuli_dly) & deve;    ///changed by HUJ

   /********************* SRAM SIGNAL TIMING  ******************************/

   // Hot Encoded
   always @(posedge clk)
     begin
     #D;
     sram_cmd_pipe1 <=  (~reset_l)                                   ? 4'h0 :
                       (read_op        & (dq_pio_target === 2'b10)) ? 4'h1 :
                       (write_now_sram & (dq_pio_target === 2'b10)) ? 4'h2 :
                       (search_op)                                  ? 4'h4 :
		       (learn_data_wr0)                             ? 4'h8 :
                       4'h0 ;
     end
   always @(posedge clk) sram_cmd_pipe2 <= #D (~reset_l) ? 4'h0 : sram_cmd_pipe1;
   always @(posedge clk) sram_cmd_pipe3 <= #D (~reset_l) ? 4'h0 : sram_cmd_pipe2;
   always @(posedge clk) sram_cmd_pipe4 <= #D (~reset_l) ? 4'h0 : sram_cmd_pipe3;
   always @(posedge clk) sram_cmd_pipe5 <= #D (~reset_l) ? 4'h0 : sram_cmd_pipe4;
   always @(posedge clk) sram_cmd_pipe6 <= #D (~reset_l) ? 4'h0 : sram_cmd_pipe5;

   always @(posedge clk) ext_sram_addr_pipe2 <= #D ext_sram_addr;
   always @(posedge clk) ext_sram_addr_pipe3 <= #D ext_sram_addr_pipe2;
   always @(posedge clk) ext_sram_addr_pipe4 <= #D ext_sram_addr_pipe3;
   always @(posedge clk) ext_sram_addr_pipe5 <= #D ext_sram_addr_pipe4;
   always @(posedge clk) ext_sram_addr_pipe6 <= #D ext_sram_addr_pipe5;

`ifdef CAM_1MEG
assign ref_sadr = (tlsz === 2'b00) ? ((sram_cmd_pipe4 === 4'h4) ? {ext_sram_addr_pipe4[`SADR_WIDTH-1:`SADR_WIDTH-8],search_result_pipe4[`INDEX_WIDTH:1]} :
                                                                  ext_sram_addr_pipe4)       :
                  (tlsz === 2'b01) ? ((sram_cmd_pipe5 === 4'h4) ? {ext_sram_addr_pipe5[`SADR_WIDTH-1:`SADR_WIDTH-8],search_result_pipe5[`INDEX_WIDTH:1]} :
                                                                  ext_sram_addr_pipe5)       :
                                     ((sram_cmd_pipe6 === 4'h4) ? {ext_sram_addr_pipe6[`SADR_WIDTH-1:`SADR_WIDTH-8],search_result_pipe6[`INDEX_WIDTH:1]} :
                                                                  ext_sram_addr_pipe6) ;

`endif
`ifdef CAM_2MEG
   assign ref_sadr = (tlsz === 2'b00) ? ((sram_cmd_pipe4 === 4'h4) ? {ext_sram_addr_pipe4[`SADR_WIDTH-1:`SADR_WIDTH-7],search_result_pipe4[`INDEX_WIDTH:1]} :
					 ext_sram_addr_pipe4)       : 
					  (tlsz === 2'b01) ? ((sram_cmd_pipe5 === 4'h4) ? {ext_sram_addr_pipe5[`SADR_WIDTH-1:`SADR_WIDTH-7],search_result_pipe5[`INDEX_WIDTH:1]} :
                                                              ext_sram_addr_pipe5)       :
	  ((sram_cmd_pipe6 === 4'h4) ? {ext_sram_addr_pipe6[`SADR_WIDTH-1:`SADR_WIDTH-7],search_result_pipe6[`INDEX_WIDTH:1]} :
           ext_sram_addr_pipe6) ;
`else
   
   
      assign ref_sadr = (tlsz === 2'b00) ? ((sram_cmd_pipe4 === 4'h4) ? {ext_sram_addr_pipe4[`SADR_WIDTH-1:`SADR_WIDTH-8],search_result_pipe4[`INDEX_WIDTH:1]} :
					 ext_sram_addr_pipe4)       : 
					  (tlsz === 2'b01) ? ((sram_cmd_pipe5 === 4'h4) ? {ext_sram_addr_pipe5[`SADR_WIDTH-1:`SADR_WIDTH-8],search_result_pipe5[`INDEX_WIDTH:1]} :
                                                              ext_sram_addr_pipe5)       :
	  ((sram_cmd_pipe6 === 4'h4) ? {ext_sram_addr_pipe6[`SADR_WIDTH-1:`SADR_WIDTH-8],search_result_pipe6[`INDEX_WIDTH:1]} :
           ext_sram_addr_pipe6) ;

`endif // !ifdef CAM_2MEG
   
   assign sram_op  = (tlsz === 2'b00) ? (((sram_cmd_pipe4 === 4'h4) & ~search_result[0]) ? 4'h0 :
	 				 sram_cmd_pipe4) :
					  (tlsz === 2'b01) ? (((sram_cmd_pipe5 === 4'h4) & ~search_result[0]) ? 4'h0 :
							      sram_cmd_pipe5) :
	  (((sram_cmd_pipe6 === 4'h4) & ~search_result[0]) ? 4'h0 :
           sram_cmd_pipe6) ;

   assign verify_sadr = |sram_op;

   assign ref_ce_l  = ~verify_sadr;
   assign ref_we_l  = ~(verify_sadr & ((sram_op === 4'h2) | (sram_op === 4'h8)));
   assign ref_ale_l = ~verify_sadr;

   // OE only deasserted for 2 clks for Wrs/Lrns.
   // Need to check when a WRITE or LEARN command occurs.
   // ??? Currently RTL still deasserts OE even in SUPRRESS MODE ???


   always @(posedge clk)
     
     sram_oe_pipe1 <=  #D (~reset_l)                                     			 ? 1'b0 :
                      (cmdv_pipe2 & (cmd_op_pipe2 == 2'h1) & (dq_pio_target === 2'b10)) ? 1'b1 :
                      (learn_op_pipe1)                                			 ? 1'b1 :
                      1'b0 ;
   always @(posedge clk) sram_oe_pipe2 <= #D sram_oe_pipe1;
   always @(posedge clk) sram_oe_pipe3 <= #D sram_oe_pipe2;
   always @(posedge clk) sram_oe_pipe4 <= #D sram_oe_pipe3;
   always @(posedge clk) sram_oe_pipe5 <= #D sram_oe_pipe4;
   always @(posedge clk) sram_oe_pipe6 <= #D sram_oe_pipe5;

   assign ref_oe_l = (tlsz === 2'h0) ? (sram_oe_pipe3 | sram_oe_pipe4) :
					 (tlsz === 2'h1) ? (sram_oe_pipe4 | sram_oe_pipe5) :
	  (sram_oe_pipe5 | sram_oe_pipe6) ;

   // Need to keep state for LRAM that a SRAM RD or WR operation is pending so know
   // who gets to drive the SRAM bus.
   // Also for Learns, if the device above not full, current device will sit idle.
   // Don't need to worry about SEARCH since all devices process concurrently.
   // Arbitration will be done via LHI and BHI.

   // Also need to delay WR cycle by 2 cycle since that is where the SRAM pipe begins.

   always @(posedge clk) cmd_op_pipe1 <= #D cmd_op;
   always @(posedge clk) cmd_op_pipe2 <= #D cmd_op_pipe1;

   always @(posedge clk) cmdv_pipe1 <= #D cmdv;
   always @(posedge clk) cmdv_pipe2 <= #D cmdv_pipe1;

   always @(posedge clk)
     begin
     #(D );
     sram_cmd_pending_pipe1 =  (~test & 
				   ((learn_op_pipe1 & (~&fuli)) |
				    ((dq_pio_target === 2'b10) &
			             ((cmdv & (cmd_op == 2'h0)) | 
				      (cmdv_pipe2 & (cmd_op_pipe2 == 2'h1))))));
     end
   always @(posedge clk) sram_cmd_pending_pipe2 <= #D (~reset_l) ? 1'b0 : sram_cmd_pending_pipe1;
   always @(posedge clk) sram_cmd_pending_pipe3 <= #D (~reset_l) ? 1'b0 : sram_cmd_pending_pipe2;
   always @(posedge clk) sram_cmd_pending_pipe4 <= #D (~reset_l) ? 1'b0 : sram_cmd_pending_pipe3;
   always @(posedge clk) sram_cmd_pending_pipe5 <= #D (~reset_l) ? 1'b0 : sram_cmd_pending_pipe4;
   always @(posedge clk) sram_cmd_pending_pipe6 <= #D (~reset_l) ? 1'b0 : sram_cmd_pending_pipe5;

   assign sram_op_pending = (tlsz === 2'b00) ? sram_cmd_pending_pipe4 :
          (tlsz === 2'b01) ? sram_cmd_pending_pipe5 :
          sram_cmd_pending_pipe6 ;

   assign ref_oe_ce_l  = ~rst_l? 0:(deve & (verify_sadr | (lram & ~sram_op_pending &
`ifdef CAM_4MEG							   
							   (~verify_sadr & search_result[21]))));
`else
  `ifdef CAM_1MEG
                                                           (~verify_sadr & search_result[19]))));
   `else
                                                           (~verify_sadr & search_result[20]))));
   `endif
`endif // !ifdef CAM_4MEG
   

   

   assign ref_oe_we_l  = ref_oe_ce_l;
   assign ref_oe_oe_l  = ~rst_l? 0: lram;
   assign ref_oe_ale_l = ref_oe_ce_l;
   assign ref_oe_sadr  = ref_oe_ce_l;

   /********************* COMPARE THE SIGNALS DRIVEN by RTL ****************/

   always @(posedge clk) read_transaction <= #D {cam_data_rd, cam_mask_rd, reg_rd};


   /********** resets ***************************/
   always @(posedge clk)
     begin
     	if (~reset_l)
	  begin
	     multihit <= #D 1'b0;
	  end
     end
   


   /************************************************************************/
   // Done only to ignore MISCOMPARES caused by RTL driving SSV and SSF OE.

   reg 	  verification_on;

   always @(posedge clk)
     if (~reset_l)
       verification_on <= #D 1'b0;
     else if (search_op1)
       verification_on <= #D 1'b1;
     else
       verification_on <= #D verification_on;

   /************************************************************************/

endmodule
