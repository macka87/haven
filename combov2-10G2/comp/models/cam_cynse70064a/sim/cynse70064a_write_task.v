/************************************************************************/
/* Cypress Semiconductor Company Confidential                           */
/* Copyright 2004, Cypress Semiconductor. All Rights reserved           */
/* Cypress Semiconductor proprietary source code                        */
/* Permission to use, modify or copy this code is prohibited            */
/* without the express written consent of                               */
/* Cypress Semiconductor                                                */
/* Filename: cynse70064A_Write_Task.v									*/
/* Release: 0.1 								        */
/* Last Updated: 24th September 2004 by HUJ,AOG                 								*/
/* This task file contains single direct write, single indirect write   */
/* and burst write function inputs									*/
/************************************************************************/



//**************************** Write Command: Command bus fields *****************************************************
//Command	CYC	8	 7	   6 		5 	4 	3 	2 			1 	0
//Write	A 	SADR[21]	SADR[20] 	x 		GMR  Index  [2:0]			0 = Single 1 = Burst			0 	1
//	B 	0 	 0 	   0 		GMR  Index	 [2:0] 		0 = Single 1 = Burst			0 	1
//*******************************************************************************************************************/
	
//***************************** sWrited68 ******************************************************************************
//Description:		Writes a single location of the data array, mask array, SRAM, or device registers in DIRECT mode
//Syntax:		sWrited68(REGION,SADR,GMR_Index,CHIP_ID,ADDRESS,DATA);
//		Parameters		Size	Description
//		REGION 		2'h 	0 = Data Array		1 = Mask Array		2 = External SRAM 		3 = Internal Register
//		SADR		2'h 	This parameter is supplied by the host ASIC for SRAM data write
//		GMR_Index		3'h	This parameter contains the GMR Index to mask the write to the data/mask array
//		CHIP_ID		5'h	This parameter carries the Chip ID of the device 
//		ADDRESS		15'h 	This parameter carries the address of the data array, mask array or the SRAM
//		DATA		68'h	This parameter carries the data to be written
//Example:		sWrited68(1,0,2,2,3000,23456789F);
//Number of cycles:			3 (See Figure 10-3 in the CYNSE70064A datasheet)
//********************************************************************************************************************
task sWrited68;
	input [1:0] region;
	input [1:0] sadr;
	input [2:0] gmr_index;
	input [4:0] chip_id;
	input [14:0] address;
	input [67:0] data;
		
	begin
    		CMDV = 1;
    		enable = 1;
    		
    		//	Command	CYCLE	8	 7	   6 		5 	4 	3 	2 	1 	0
		//	Read 	A 	SADR[21]	SADR[20]	 x		GMR  Index  [2:0]			0 	0 	1
		CMD = (sadr << 7) | (gmr_index << 3) | 3'b001;
    		
    		//DQ	[67:30]	[29]		[28:26]		[25:21]	[20:19]	[18:14] 		[13:0]
		//	Rsrvd 	0: Direct		Not Applicable		ID 	Region	Reserved		Address
		DQ_reg = (0 << 29)| (chip_id << 21) | (region << 19) | address;
    		#(`T_CLK2X *2);
    		
    		//	Command	CYCLE	8	 7	6	5 	4 	3 	2 	1 	0
		//	Read	B 	0 	 0 	0 	GMR   Index  [2:0] 		 	0 	0 	1
    		CMD = (gmr_index << 3) | 3'b001;
    		#(`T_CLK2X *2);
    		CMDV = 0;
    		CMD = 9'hZ;
    		DQ_reg = data;
    		#(`T_CLK2X *4);
    		DQ_reg = 68'h0;
    		#(`T_CLK2X *4);
    		DQ_reg = 68'hZ;
    	end
endtask

//***************************** sWritei68 ********************************************************************************
//Description:		Writes a single location of the data array, mask array, SRAM, or device registers in INDIRECT mode
//Syntax:		sWritei68(REGION,SADR,SSR,GMR_INDEX,CHIP_ID,DATA);
//		Parameters		Size	Description
//		REGION 		2'h 	0 = Data Array		1 = Mask Array		2 = External SRAM 		3 = Internal Register
//		SADR		2'h 	This parameter is supplied by the host ASIC for SRAM data write
//		SSR		3'h	This parameter carries the SSR index for the indirect write operation
//		GMR_Index		3'h	This parameter contains the GMR Index to mask the write to the data/mask array
//		CHIP_ID		5'h	This parameter carries the Chip ID of the device 
//		DATA		68'h	This parameter carries the data to be written
//Example:		sWritei68(1,0,2,2,2,3000);
//Number of cycles:			3 (See Figure 10-3 in the CYNSE70064A datasheet)
//*********************************************************************************************************************
task sWritei68;
	input [1:0] region;
	input [1:0] sadr;
	input [2:0] ssr;
	input [2:0] gmr_index;
	input [4:0] chip_id;
	input [67:0] data;
		
	begin
    		CMDV = 1;
    		enable = 1;
    		//	Command	CYCLE	8	 7	   6 		5 	4 	3 	2 	1 	0
		//	Read 	A 	SADR[21]	SADR[20] 	x		GMR  Index  [2:0]			0 	0 	1
		CMD = (sadr << 7) | (gmr_index << 3) | 3'b001;
    		
    		//DQ	[67:30]	[29]		[28:26]		[25:21]	[20:19]	[18:14] 		[13:0]
		//	Rsrvd 	1: Indirect		SSR[2:0]		ID 	Region	Reserved		Don't Care
		DQ_reg = (1 << 29) | (ssr << 26) | (chip_id << 21) | (region << 19);
    		#(`T_CLK2X *2);
    		
    		//	Command	CYCLE	8	 7	6	5 	4 	3 	2 	1 	0
		//	Read	B 	0 	 0 	0 	GMR   Index  [2:0] 		 	0 	0 	1
    		CMD = (gmr_index << 3) | 3'b001;
    		#(`T_CLK2X *2);
    		CMDV = 0;
    		CMD = 9'hZ;
    		DQ_reg = data;
    		#(`T_CLK2X *4);
    		DQ_reg = 68'h0;
    		#(`T_CLK2X *4);
    		DQ_reg = 68'hZ;
    	end
endtask

//***************************** bWrite********************************************************************************
//Description:		Writes a block of locations from the data or mask arrays as a burst.The WBURREG specifies the starting
//		address and the length of the data transfer.
//		WBURREG 		[67:28] [27:19] 				[18:14]		[13:0] 
//				Rsrvd	Length of burst(4-511)	 Rsrvd				Starting Address
//Syntax:		bWrite(REGION,GMR_INDEX,CHIP_ID,BURST_LENGTH, FILE);
//		Parameters		Size	Description
//		REGION 		2'h 	0 = Data Array		1 = Mask Array
//		GMR_Index		3'h	This parameter contains the GMR Index to mask the write to the data/mask array
//		CHIP_ID		5'h	This parameter carries the Chip ID of the device 
//		BURST_LENGTH		9'd	This parameter carries the length of the burst Range: 4-FF
//		FILE_NAME		8*16'h  This parameter carries the file name containing the data to be written.
//					Max_File_Name_Size = 16 characters
//Example:		bWrite(1,2,10);
//Number of cycles:		2+n (See Figure 10-4 in the CYNSE70064A datasheet)
//********************************************************************************************************************
task bWrite;
	input [1:0] region;
	input [2:0] gmr_index;
	input [4:0] chip_id;
	input [8:0] burst_length;
	input [8*15:0] file;
	reg [`REG_WIDTH-1:0] memory [511:0];
	reg [8:0] i;
	begin
		$readmemh(file, memory);
    		CMDV = 1;
    		enable = 1;
    		
    		
    		//	Command	CYCLE	8	 7	   6 	5 	4 	3 	2 	1 	0
		//	Read 	A 	0	 0 	   0 	GMR  Index  [2:0]		 	1=burst	0 	1
		CMD = (gmr_index << 3) | 3'b101;
    		
    		//DQ	[67:30]	[29]		[28:26]		[25:21]	[20:19]	[18:14] 		[13:0]
		//	Rsrvd 	0: Direct		Not Applicable		ID 	Region	Reserved		Dont care
		DQ_reg = (chip_id << 21) | (region << 19);
    		#(`T_CLK2X *2);
    		
    		//	Command	CYCLE	8	 7	6	5 	4 	3 	2 	1 	0
		//	Read	B 	0 	 0 	0 	GMR   Index  [2:0] 		 	1=burst	0	1
    		CMD = (gmr_index << 3) | 3'b101;
    		#(`T_CLK2X *2);
    		CMDV = 0;
    		CMD = 9'hZ;
    		for (i=0;i< burst_length; i= i + 1)
    			begin
    			DQ_reg = memory[i];
    			#(`T_CLK2X *4);
    			end
    			
    		DQ_reg = 68'h0;
    		#(`T_CLK2X *4);
    		DQ_reg = 68'hZ;
    	end
endtask