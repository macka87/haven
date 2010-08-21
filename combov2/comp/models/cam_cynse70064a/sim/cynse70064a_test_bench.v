/************************************************************************/
/* Cypress Semiconductor Company Confidential                           */
/* Copyright 2004, Cypress Semiconductor. All Rights reserved           */
/* Cypress Semiconductor proprietary source code                        */
/* Permission to use, modify or copy this code is prohibited            */
/* without the express written consent of                               */
/* Cypress Semiconductor                                                */
/* Filename: cynse70064A_Test_Bench.v									*/
/* Release: 0.1 								        */
/* Last Updated: 24th September 2004 by HUJ,AOG                 								*/
/* This test bench verifies the basic Read, Write, Search and Learn     */
/* functionality of the CYNSE70064A device. Includes "Reserved Mode"    */
/* test as well                                                         */
/************************************************************************/

`define CAM_2MEG 1 //Simulating CYNSE70064: 2Mb device
`define PRE_LOAD 1
`include "../cynse70032_064_128.vh"  //including the definition module
		
module CYNSE70064A_tb;

//****************** Inputs to the CYNSE70064 model *****************************************************************
   reg 	   CLK2X;
   reg 	   PHS_L;  
   reg 	   RST_L;
   reg 		    CMDV;           // cmd valid
   reg [`CMD_WIDTH-1:0]   CMD;      // cmd
   reg [6:0] 		    LHI;            // local hit in
   reg [2:0] 		    BHI;            // block hit in
   reg [6:0] 		    FULI;           // local full in
   reg [4:0] 		    ID;             // device id
   

//****************** InOuts to the CYNSE70064 model *****************************************************************
   wire [`REG_WIDTH - 1:0] DQ;      // data bus

//****************** Outputs from  CYNSE70064 model *****************************************************************
   wire 		    ACK;
   wire 		    EOT;
   wire 		    SSV;
   wire 		    SSF;
   wire 		    CE_L;
   wire 		    WE_L;
   wire 		    OE_L;
   wire 		    ALE_L;
   wire [`SADR_WIDTH-1:0] SADR;
   wire 		    FULL;
   wire 	[1:0]	    FULO;
   wire 	[1:0]	    LHO;
   wire 	[2:0]	    BHO;
   
//****************** Variables used in the CYNSE70064 TestBench *****************************************************
   reg		    enable;
   reg [67:0]	    taro;	
   reg  [`REG_WIDTH - 1:0] DQ_reg;
   integer 		cnt;
   
   	// Instantiating the CYNSE70064 model
	cynse70064A Main  (    
			 .CLK2X(CLK2X),
			 .PHS_L(PHS_L),
                         .RST_L(RST_L),
                         .DQ(DQ),
                         .CMDV(CMDV),
                         .CMD(CMD),
			 .ID(ID),
			 .LHI(LHI),
			 .BHI(BHI),
			 .FULI(FULI),
                	 		 .ACK(ACK),
                	 		 .EOT(EOT),
                	 		 .SSV(SSV),
                	 		 .SSF(SSF),
                	  		 .CE_L(CE_L),
                	 		 .WE_L(WE_L),
                	 		 .OE_L(OE_L),
                			 .ALE_L(ALE_L),
                			 .SADR(SADR),
                			 .FULL(FULL),
                	 		 .FULO(FULO),
                			 .LHO(LHO),
                			 .BHO(BHO)
			 );

`include "cynse70064a_read_task.v"    //including read task file
`include "cynse70064a_write_task.v"   //including write task file
`include "cynse70064a_search_task.v"  //including search task file
`include "cynse70064a_learn_task.v"   //including learn task file

assign DQ = enable ? DQ_reg : `REG_WIDTH'bZ; // Driving the dq bus 

//*********************************** Clock-generation logic *******************************************************
always
	# `T_CLK2X  CLK2X = !CLK2X;
	
always
	# (2*`T_CLK2X)  PHS_L = !PHS_L;
//******************************************************************************************************************

//************************************* dump the waveform file for VCS or NC-Verilog *******************************
initial
begin
`ifdef NSE70K_VCS
	$dumpfile("NSE70K.vcd");
	$dumpvars(0, brecken_ref_leaf_tb);
`endif  // ifdef NSE70K_VCS

`ifdef NSE70K_FSDB	
	$fsdbDumpfile("NSE70K.fsdb");
	$fsdbDumpvars(0, brecken_ref_leaf_tb);
`endif  //ifdef NSE70K_FSDB
end
//*****************************************************************************************************************	

initial
	begin
		CLK2X = 0;
		PHS_L = 0;
				
                CMDV = 0;
                CMD = 9'b0;
		$display("Value of T_CLK2X  %d   Value of 2*T_ClK2X  %d",`T_CLK2X, 2*`T_CLK2X);
		//******* Initialization of CYNSE70064 Network Search Engines on Power-up: Refer App Note************
		ID = 5'h11; // Device ID Initialisation
		LHI = 7'b0; // Connected to ground for single device mode
		BHI = 3'b0; // Connected to ground for single device mode
		FULI = 7'b1111111; // All inputs should be connected to '1' for single device mode
		RST_L =0; // Hardware Reset to the device
		#(64 *(2*`T_CLK2X)); // Hardware reset should be provided for 64 clock cycles once the device is stable
		RST_L = 1;
		#(2*`T_CLK2X);

		//******** Writing to the Command Register **********************************************************
		//[67:17]	[16:9]		[8]	[7]	[6:4]		[3:2]			[1]	[0]
		//Rsrvd	  CFG		LRAM	LDEV	HLAT(HitLatency)TLSZ(Latency)					DEVE	SRST
		//	  00:8K×68 		Last	Last	000: 0 100: 4		00:4(1 device)			Device	Software
		//	  01:4K×136 		Device	Device	001: 1 101: 5		01:5(Upto 8 devices)			Enable	Reset
		//	  10:2K×272 		on SRAM	in the 	010: 2 110: 6		10:6(Upto 31 devices)				1= Reset
		//	  11:Rsrvd		bus	cascade	011: 3 111: 7		11:Rsrvd
		//51'h0	  8'h0		1	1	3'h0		2'h0			1'h1	1'h0=68'h182	
		//***************************************************************************************************
		// sWrited68(region, sadr, gmr_index, chip_id, address, data);
		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd56,68'h182); // configure all four partitions to be 68-bit
		
		//******** Writing to GMR[0] register****************************************************************
		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd32,68'hF_FFFF_FFFF_FFFF_FFFF);  //GMR[0] 
		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd33,68'hF_FFFF_FFFF_FFFF_FFFF); //Writing to GMR[1] register
		
		//*************** read out the important registers **************************************************
		// sReadd68(region, sadr, chip_id, address);
		sReadd68(2'd3,2'h0,5'h11,15'd56); // Reading Command Register 
		//Expected value: 0x182 on data bus
		sReadd68(2'd3,2'h0,5'h11,15'd57); // Reading information Register 
		//Expected value: 0xdc7f0211 on data bus
		sReadd68(2'd3,2'h0,5'h11,15'd32); // Reading GMR[0] Register 
		//Expected value: 0xFFFFFFFFFFFFFFFFFF on data bus
		sReadd68(2'd3,2'h0,5'h11,15'd33); // Reading GMR[1] Register 
		//Expected value: 0xFFFFFFFFFFFFFFFFFF on data bus
		
		#(200*`T_CLK2X);
		//*********************************************************************
		//******** Initialize Data Array and Mask Array ***********************
		//*********************************************************************
		//sWrited68 ([1:0] region; [2:0] sadr; [2:0] gmr_index; [4:0] chip_id; [14:0] address; [67:0] data;)
		//bWrite ([1:0] region; [2:0] gmr_index; [4:0] chip_id; [8:0] burst_length; [8*15:0] file;
		$display("Initialize the data array and mask array");
		`ifdef PRE_LOAD  //this option will preload the initial values to mask array and data array
				`ifdef MODELSIM //.dat files have smaller size for modelsim
				$readmemh("./data/modelsim_data_init.dat", Main.model.cam_data_array);
 				$readmemh("./data/modelsim_mask_init.dat", Main.model.cam_mask_array);
 				`else
 				$readmemh("unix_data_init.dat", Main.model.cam_data_array);
 				$readmemh("unix_mask_init.dat", Main.model.cam_mask_array);
 				`endif	//endif of MODELSIM
 		`else		//this option will initialize the data array and mask array with burst write to each location
			`ifdef MODELSIM
				taro = 68'h8000000;
				for(cnt = 0; cnt < 4; cnt = cnt +1)
				begin
				sWrited68(2'd3,2'h0,3'h0,5'h11,15'd59,taro);
		    		//bWrite(region, gmr_index, chip_id, burst_length, file);
		    		bWrite(2'h0,3'h0,5'h11,9'd256,"data_init.dat");
		    		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd59,taro);
		    		bWrite(2'h1,3'h0,5'h11,9'd256,"mask_init.dat");
		    		taro = taro + 68'h100;
		    		$display (" %d ",cnt);	
				end
		
			`else		 
				taro = 68'h8000000;
				//writes 128 times 
				for (cnt=0;cnt < 128; cnt= cnt + 1)  
				begin			
				sWrited68(2'd3,2'h0,3'h0,5'h11,15'd59,taro);
		    		//bWrite(region, gmr_index, chip_id, burst_length, file);
		    		bWrite(2'h0,3'h0,5'h11,9'd256,"data_init.dat");
		    		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd59,taro);
		    		bWrite(2'h1,3'h0,5'h11,9'd256,"mask_init.dat");
		    		taro = taro + 68'h100;
		    		$display (" %d ",cnt);
				end
 			`endif	//endif of MODELSIM
 		`endif  //endif of PRE_LOAD
 		
		//********************************************************************
		//**** INIT DONE ***
		//******************	
		
		#(1000*`T_CLK2X);
		$display("Functionality testing");
		//*********************************************************************
		//********* Single Write, Single Read Testing**************************
		//*********************************************************************
		$display("Single Write and Single Read");
		// single read and single write to data array using GMR[0]
		sWrited68(2'd0,2'h0,3'h0,5'h11,15'h4,68'h44444444444444444);
		sReadd68(2'd0,2'h0,5'h11,15'h4);
		//expected value 0x44444444444444444 on data bus
		#(20*`T_CLK2X);
		//single read and single write to data rray with gmr mask
		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd34,68'hF_F0F0_F0F0_F0F0_F0F0);  // setup GMR to mask write 
		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd35,68'hF_F0F0_F0F0_F0F0_F0F0); //Writing to GMR [2] and GMR[3] register
		sWrited68(2'd0,2'h0,3'h1,5'h11,15'h8,68'h88888888888888888);
		sReadd68(2'd0,2'h0,5'h11,15'h8);
		// expected value 0x88080808080808080 on data bus
		#(20*`T_CLK2X);
		
		//*********************************************************************
		//********* Burst Write, Burst Read Testing ***************************
		//*********************************************************************
		$display("Burst Write and Burst Read");
		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd59,68'h400010); // Writing to WBURREG register Length = 8 starting address = 16
		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd58,68'h400010); // Writing to RBURREG register Length = 8 starting address = 16
		bWrite(2'h0, 3'h0, 5'h11, 9'h8, "./data/test.dat");       // Burst Write
		//bRead(region, chip_id, burst_length);
		bRead(2'h0,5'h11,9'h8);       // Burst read
		//expected data from test.dat file sequentially show up on data bus
		//*********************************************************************
		//******************* Search and Learn ********************************
		//*********************************************************************
		
		//*********************68 bit Search*******************************
		$display("68 bit Search");
		//Search68(gmr_index, sadr, comp, ssr, data);
		Search68(3'h0, 2'h0, 4'h0, 3'h0, 68'h44444444444444444);		     //hit
		//expected address 0x4 on sadr bus and SSF and SSV are both HIGH
		Search68(3'h0, 2'h0, 4'h4, 3'h0, 68'h123456789abcdef);		       //miss and store the data in comparand register=4
		//expected SSF is LOW and SSV is HIGH
		Search68(3'h0, 2'h0, 4'h0, 3'h0, 68'h77777777777777777);		     //hit
		//expected address 0x17 on sadr bus and SSF and SSV are both HIGH
		Search68(3'h0, 2'h0, 4'h1, 3'h0, 68'h77777777777777776);		       //miss and store the data in comparand register=1
		//expected SSF is LOW and SSV is HIGH
		$display("68 bit Learn");
		//Learn68(sadr, comp);
		Learn68(2'h0, 4'h4); // learn from comparand register 4
		Learn68(2'h0, 4'h1); // learn from comparand register 1
		#(20*`T_CLK2X);
		Search68(3'h0, 2'h0, 4'h0, 3'h3, 68'h123456789abcdef);        // search the learnt data and store the address in SSR=3 
		//expected address 0x0 on sadr bus and SSF and SSV are both HIGH
		Search68(3'h0, 2'h0, 4'h1, 3'h0, 68'h77777777777777776);						// search the learnt data and store the address in SSR=3 
		//expected address 0x1 on sadr bus and SSF and SSV are both HIGH
		#(20*`T_CLK2X);
		$display("68 bit Indirect write");
		//sWritei68(region, sadr, ssr, gmr_index, chip_id, data);
		sWritei68(2'h0, 2'h0, 3'h3, 3'h0, 5'h11, 68'h99999999999999999);
		$display("68 bit Indirect read");
		//sReadi68(region, sadr, ssr, chip_id);
		sReadi68(2'h0, 2'h0, 3'h3, 5'h11);
		//expected value 0x99999999999999999 on data bus
		#(20*`T_CLK2X);
		
		//*********************136 bit Search*******************************
		$display("136 bit Search");
		sWrited68(2'd3,3'h0,3'h0,5'h11,15'd56,68'hab82); // configure all four partitions to be 136-bit
		//Search136(gmr_index, sadr, comp, ssr, data0, data1);       
		//data0 is most significant part and data1 is least significant part
		Search136(3'h0, 2'h0, 4'h0, 3'h0, 68'h66666666666666666, 68'h77777777777777777);//hit
		//expected address 0x16 on sadr bus and SSV and SSF are both HIGH
		Search136(3'h0, 2'h0, 4'h8, 3'h0, 68'h12345, 68'h54321);										//miss and store the data in comparand register 8
		//expected SSV is HIGH and SSF is LOW
		//#(20*`T_CLK2X);
		$display("136 bit Learn");
		//Learn136(sadr, comp);
		Learn136(2'h0, 4'h8);	
		#(20*`T_CLK2X);
		Search136(3'h0, 2'h0, 4'h0, 3'h0, 68'h12345, 68'h54321);			                     //hit search the learnt data	
		//expected address 0x0 on sadr bus and SSV and SSF are both HIGH
		#(20*`T_CLK2X);
		
		//*********************272 bit Search *******************************
		$display("272 bit Search");
		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd56,68'h15582); // configure all four partitions to be 272-bit
		//Search272(gmr_index1, gmr_index0, sadr, ssr, data3, data2, data1, data0); 
		//gmr_index1 is most significant mask part and gmr_index0 is least significant mask part
		//data3 is most significant data part and data0 is least significant data part
		Search272(3'h0, 3'h0, 2'h0, 3'h0, 68'h44444444444444444, 68'h55555555555555555, 68'h66666666666666666, 68'h77777777777777777); //hit
		//expected address 0x14 on sadr bus and SSV and SSF are both HIGH
		#(20*`T_CLK2X);
		sReadd68(2'd3,2'h0,5'h11,15'd48);//read SSR[0]
		Search272(3'h0, 3'h0, 2'h0, 3'h0, 68'hffff, 68'hffff, 68'hffff, 68'hffff); 										  //miss
		//expected SSV is HIGH and SSF is LOW
		#(20*`T_CLK2X);
		
		//*************************** Testing for software reset **********************************
		// software reset will not change the data in data array and mask array
		// software reset will rset the internal registers.  all GMR registers will be set to 0
		$display("Software Reset");
		sWrited68(2'd3,3'h0,3'h0,5'h11,15'd56,68'h183);  //command register[0] is the software reset pin.
		#(32*`T_CLK2X);	//once it is set, it will go low after 16 cycles
		sReadd68(2'd3,2'h0,5'h11,15'd56);  //reading the command register to see if command register[0] goes to 0
		//expected the 0 bit of the value shown on data bus is LOW
		
		//setup GMR[0] and GMR[1] register for write to data or mask array
		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd32,68'hF_FFFF_FFFF_FFFF_FFFF);  //GMR[0] 
		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd33,68'hF_FFFF_FFFF_FFFF_FFFF); //Writing to GMR[1] register
		
		//*****************************************************************************************
		
		//*************************** Reserved Partition Mode **********************************
		$display("Reserved Partition Mode");
		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd56,68'h1FF82); //Set all four partitions to be reseved mode
		sReadd68(2'd3,2'h0,5'h11,15'd60); // Reading the NFA register
		//expected value 0x0 on data bus because NFA is not update yet NFA only gets update after write or learn
		sWrited68(2'd0,2'h0,3'h0,5'h11,15'h20,68'h0);  // after any write the NFA will update and full signal goes high
		sReadd68(2'd3,2'h0,5'h11,15'd60); // Reading the NFA register, NFA shows the last address 
		//expected the max address shows on data bus and FULL and FULO signals go HIGH
		#(20*`T_CLK2X);
		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd56,68'h12782); //set first partition to be reseved, second partition to be 68-bit, third partition to be 136-bit and four partition to be 272-bit 
		sWrited68(2'd0,2'h0,3'h0,5'h11,15'hff,68'h0);  // after any write the NFA will update
		sReadd68(2'd3,2'h0,5'h11,15'd60);              // since the first partition is reseved, NFA points to the first address of second partition
		
		// The HDL code below shows how if a partition is "reserved" it is possible to Read, Write 
		// to that partition. However, it is not possible to "Search" a reserved partition.
		#(20*`T_CLK2X);
		sWrited68(2'd3,2'h0,3'h0,5'h11,15'd56,68'h1E182);  // set the first two partitions to be 68 bit and the last two partitions to be reserved
		`ifdef MODELSIM
		sWrited68(2'd0, 2'h0, 3'h0, 5'h11, 15'h45, 68'haaabbbccc);   //Writing to the 1st partition
		sReadd68(2'd0,2'h0,5'h11,15'h45);// Reading from the 1st partition
		//Expected Value: 0xaaabbbccc on data bus
		Search68(3'h0, 2'h0, 4'h0, 3'h0, 68'haaabbbccc);	// 68-bit search: Results in a hit
		//expected address 0x45 on sadr bus and SSV and SSF are both HIGH
		
		sWrited68(2'd0, 2'h0, 3'h0, 5'h11, 15'h1a4, 68'hdddeeefff);   //Writing to the 2nd partition
		sReadd68(2'd0,2'h0,5'h11,15'h1a4);// Reading from the 2nd partition
		//Expected Value: 0xdddeeefff on data bus
		Search68(3'h0, 2'h0, 4'h0, 3'h0, 68'hdddeeefff);	// 68-bit search: Results in a hit
		//Expected address 0x1a4 on sadr bus and SSV and SSF are both HIGH
		
		sWrited68(2'd0,2'h0,3'h0,5'h11,15'h234,68'h778899aa); // Writing to the 3rd Partition
		sReadd68(2'd0,2'h0,5'h11,15'h234);// Reading from the 3rd partition
		//Expected value: 0x778899aa on data bus
		Search68(3'h0, 2'h0, 4'h0, 3'h0, 68'h778899aa);	// 68-bit search: Results in a miss as partition 3 is reserved
		//expected SSV is HIGH and SSF is LOW

		sWrited68(2'd0,2'h0,3'h0,5'h11,15'h3e7,68'h111222333); // Writing to the 4th partition
		sReadd68(2'd0,2'h0,5'h11,15'h3e7); // Reading from the 4th partition
		//expected value 0x111222333 on data bus
		Search68(3'h0, 2'h0, 4'h0, 3'h0, 68'h111222333);	// 68-bit search: Results in a miss as partition 4 is reserved
		//expected SSV is HIGH and SSF is LOW
		
		`else
		sWrited68(2'd0, 2'h0, 3'h0, 5'h11, 15'h1450, 68'haaabbbccc);   //Writing to the 1st partition
		sReadd68(2'd0,2'h0,5'h11,15'h1450);// Reading from the 1st partition
		//Expected Value: 0xaaabbbccc on data bus
		Search68(3'h0, 2'h0, 4'h0, 3'h0, 68'haaabbbccc);	// 68-bit search: Results in a hit
		//expected address 0x1450 on sadr bus and SSV and SSF are both HIGH
		
		sWrited68(2'd0, 2'h0, 3'h0, 5'h11, 15'h21a4, 68'hdddeeefff);   //Writing to the 2nd partition
		sReadd68(2'd0,2'h0,5'h11,15'h21a4);// Reading from the 2nd partition
		//Expected Value: 0xdddeeefff on data bus
		Search68(3'h0, 2'h0, 4'h0, 3'h0, 68'hdddeeefff);	// 68-bit search: Results in a hit
		//Expected address 0x21a4 on sadr bus and SSV and SSF are both HIGH
		
		sWrited68(2'd0,2'h0,3'h0,5'h11,15'h5234,68'h778899aa); // Writing to the 3rd Partition
		sReadd68(2'd0,2'h0,5'h11,15'h5234);// Reading from the 3rd partition
		//Expected value: 0x778899aa on data bus
		Search68(3'h0, 2'h0, 4'h0, 3'h0, 68'h778899aa);	// 68-bit search: Results in a miss as partition 3 is reserved
		//expected SSV is HIGH and SSF is LOW

		sWrited68(2'd0,2'h0,3'h0,5'h11,15'h73e7,68'h111222333); // Writing to the 4th partition
		sReadd68(2'd0,2'h0,5'h11,15'h73e7); // Reading from the 4th partition
		//expected value 0x111222333 on data bus
		Search68(3'h0, 2'h0, 4'h0, 3'h0, 68'h111222333);	// 68-bit search: Results in a miss as partition 4 is reserved
		//expected SSV is HIGH and SSF is LOW
		`endif
		#(120*`T_CLK2X);
		
		$stop;
		end
	endmodule
