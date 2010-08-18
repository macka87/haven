/************************************************************************/
/* Cypress Semiconductor Company Confidential                           */
/* Copyright 2004, Cypress Semiconductor. All Rights reserved           */
/* Cypress Semiconductor proprietary source code                        */
/* Permission to use, modify or copy this code is prohibited            */
/* without the express written consent of                               */
/* Cypress Semiconductor                                                */
/* Filename: cynse70064A_Read_Task.v									*/
/* Release: 0.1 								        */
/* Last Updated: 24th September 2004 by HUJ,AOG                 								*/
/* This task file contains single direct read, single indirect read		   */
/* and burst read function inputs									*/
/************************************************************************/




//**************************** Read Command: Command bus fields *****************************************************
//Command	CYC	8	 7	   6 		5 	4 	3 	2 			1 	0
//Read 	A 	SADR[21]	SADR[20] 	x 		0 	0 	0 	0 = Single 1 = Burst			0 	0
//	B 	0 	 0 	   0 		0 	0 	0 	0 = Single 1 = Burst			0 	0
//*******************************************************************************************************************/
	
//***************************** sReadd68 ********************************************************************************
//Description:		Reads a single location of the data array, mask array, SRAM, or device registers in DIRECT mode
//Syntax:		sReadd68(REGION,SADR,CHIP_ID,ADDRESS);
//		Parameters		Size	Description
//		REGION 		2'h 	0 = Data Array		1 = Mask Array		2 = External SRAM 		3 = Register
//		SADR		2'h 	This parameter is supplied by the host ASIC for SRAM data reads
//		CHIP_ID		5'h	This parameter carries the Chip ID of the device 
//		ADDRESS		15'h 	This parameter carries the address of the data array, mask array or the SRAM
//Example:		sReadd68(1,0,2,3000);
//Number of cycles:			6 (See Figure 10-1 in the CYNSE70064A datasheet)
//*********************************************************************************************************************

task sReadd68;
	
	input [1:0] region; 
	input [1:0] sadr;
	input [4:0] chip_id;
	input [14:0] address; 
	
	begin
    		CMDV = 1;
    		enable = 1;
    		//	Command	CYCLE	8	 7	   6 		5 	4 	3 	2 	1 	0
		//	Read 	A 	SADR[21]	SADR[20] 	x 		0 	0 	0 	0 	0 	0
		CMD = sadr << 7;
    	        		
    		//DQ	[67:30]	[29]		[28:26]		[25:21]	[20:19]	[18:14] 		[13:0]
		//	Rsrvd 	0: Direct		Not Applicable		ID 	Region	Reserved		Address
		DQ_reg = (chip_id << 21) | (region << 19) | address;
    		# (`T_CLK2X *2);
    		
    		//	Command	CYCLE	8	 7	6	5 	4 	3 	2 	1 	0
		//	Read	B 	0 	 0 	0 	0 	0 	0 	0 	0 	0 = 9'h000
    		CMD = 9'h000;
    		#(`T_CLK2X *2);
    		CMDV = 0;
    		enable = 0;
    		CMD = 9'hZ;
    		DQ_reg = 68'hZ;
    		#(`T_CLK2X *4);
    		#(`T_CLK2X *4);
    		#(`T_CLK2X *4);
    		#(`T_CLK2X *4);
    		#(`T_CLK2X *4);
	end
endtask

//***************************** sReadi68 ********************************************************************************
//Description:		Reads a single location of the data array, mask array, SRAM, or device registers in INDIRECT mode
//Syntax:		sReadi68(REGION,SADR,SSR,CHIP_ID);
//		Parameters		Size	Description
//		REGION 		2'h 	0 = Data Array		1 = Mask Array		2 = External SRAM 		3 = Register
//		SADR		2'h 	This parameter is supplied by the host ASIC for SRAM data reads
//		SSR		3'h	This parameter carries the SSR index for the indirect read operation
//		CHIP_ID		5'h	This parameter carries the Chip ID of the device 
//Example:		sReadi68(1,0,2,11);
//Number of cycles:			6 (See Figure 10-1 in the CYNSE70064 datasheet)
//*********************************************************************************************************************
task sReadi68;
	input [1:0] region;
	input [1:0] sadr;
	input [2:0] ssr;
	input [4:0] chip_id;
			
	begin
    		CMDV = 1;
    		enable =1;
    		//	Command	CYCLE	8	 7	   6 		5 	4 	3 	2 	1 	0
		//	Read 	A 	SADR[21]	SADR[20] 	x 		0 	0 	0 	0 	0 	0
		CMD = sadr << 7;
    		
    		//DQ	[67:30]	[29]		[28:26]		[25:21]	[20:19]	[18:14] 		[13:0]
		//	Rsrvd 	1: Indirect		SSR Index		ID 	Region	Reserved		Don't Care
		DQ_reg = (1 << 29) | (ssr << 26) | (chip_id << 21) | (region << 19);
    		#(`T_CLK2X *2);
    		
    		//	Command	CYCLE	8	 7	6	5 	4 	3 	2 	1 	0
		//	Read	B 	0 	 0 	0 	0 	0 	0 	0 	0 	0 = 9'h000
    		CMD = 9'h000;
    		
    		#(`T_CLK2X *2);
    		CMDV = 0;
 		enable = 0;
   		CMD = 9'hZ;
    		DQ_reg = 68'hZ;
    		#(`T_CLK2X *4);
    		#(`T_CLK2X *4);
    		#(`T_CLK2X *4);
    		#(`T_CLK2X *4);
    		#(`T_CLK2X *4);
	end
endtask

//***************************** bRead ********************************************************************************
//Description:		Reads a block of locations from the data or mask arrays as a burst. The RBURADR specifies the starting
//		address and the length of the data transfer.
//		RBURADR 		[67:28] [27:19] 				[18:14]		[13:0] 
//				Rsrvd	Length of burst(4-511)	 Rsrvd				Starting Address
//Syntax:		bRead(REGION,CHIP_ID,BURST_LENGTH);
//		Parameters		Size	Description
//		REGION 		2'h 	0 = Data Array		1 = Mask Array
//		CHIP_ID		5'h	This parameter carries the Chip ID of the device 
//		BURST_LENGTH		9'h	This parameter carries the length of the burst
//Example:		bRead(1,2,10);
//Number of cycles:			4+2n (See Figure 10-2 in the CYNSE70064 datasheet)
//********************************************************************************************************************
task bRead;
	input [1:0] region;
	input [4:0] chip_id;
	input [8:0] burst_length;
		
	begin
    		CMDV = 1;
    		enable = 1;
    		
    		//	Command	CYCLE	8	 7	  6 	5 	4 	3 	2 	1 	0
		//	Read 	A 	0	 0 	  0 	0 	0 	0 	1 	0 	0 = 9'h004
		CMD = 9'h004;
    		
    		//DQ	[67:26]	[25:21]	[20:19]	[18:14] 		[13:0]
		//	Rsrvd 	ID 	Region	Reserved		Don't Care
		DQ_reg = (chip_id << 21) | (region << 19) ;
    		#(`T_CLK2X *2);
    		
    		//	Command	CYCLE	8	 7	6	5 	4 	3 	2 	1 	0
		//	Read	B 	0 	 0 	0 	0 	0 	0 	1 	0 	0 = 9'h004
    		CMD = 9'h004;
    		
    		#(`T_CLK2X *2);
    		CMDV = 0;
    		enable = 0;
    		CMD = 9'hZ;
    		DQ_reg = 68'hZ;
    		#(`T_CLK2X *4);
    		#(`T_CLK2X *4);
    		#(`T_CLK2X *4);
    		#((`T_CLK2X *4) * 2 * burst_length);
    		
    		
	end
endtask