/************************************************************************/
/* Cypress Semiconductor Company Confidential                           */
/* Copyright 2004, Cypress Semiconductor. All Rights reserved           */
/* Cypress Semiconductor proprietary source code                        */
/* Permission to use, modify or copy this code is prohibited            */
/* without the express written consent of                               */
/* Cypress Semiconductor                                                */
/* Filename: cynse70064A_Search_Task.v									*/
/* Release: 0.1 								        */
/* Last Updated: 24th September 2004 by HUJ,AOG                 								*/
/* This task file contains 68 bit search, 136 bit search and 272 bit    */
/* search funtion input									*/
/************************************************************************/



//**************************** Search Command: Command bus fields *****************************************************
//Command	CYC	8	 7	   6 		5 	4 	3 	2 			1 	0
//Search	A 	SADR[21]	SADR[20] 	x 		GMR  Index  [2:0]			0 = 68/136 bit 			1	0
//									272-bit: 1 in 1st cycle
//										 0 in 2nd cycle	
//	B 	SSR  	Index 	[2:0]		Comparand     Register    Index	 					1	0
//*******************************************************************************************************************/

//***************************** Search68 ****************************************************************************
//Description:		Performs a 68-bit search on tables configured as x68 in device
//Syntax:		Search68(GMR_INDEX, SADR, COMP, SSR, DATA);
//		Parameters		Size	Description
//		GMR_Index		3'h	This parameter carries the GMR Index to mask the search on the data/mask array
//		SADR		3'h 	This parameter is supplied by the host ASIC for SRAM data write
//		COMPARAND		4'h 	This parameter carries the index of the Comparand Register (COMP0-31)
//		SSR		3'h 	This parameter carries the index of the Search Successful Register(SSR0-7)
//		DATA		68'h	This parameter carries the 68-bit data to be searched
//Example:		Search68(0,0,2,0,23456789F);
//Number of cycles:			4: 1 device  5: 1-8 devices  6: 1-31 devices (See Table 10-10 in the CYNSE70064A datasheet)
//********************************************************************************************************************
task Search68;

	input [2:0] gmr_index;
	input [1:0] sadr;
	input [3:0] comp;
	input [2:0] ssr;
	input [67:0] data;

	begin
			
    		CMDV = 1;
    		enable = 1;
    		
    		//Cycle A
    		//Command	CYC	8	 7	   6 		5 	4 	3 	2 		1 	0
		//Search 	A 	SADR[21]	SADR[20] 	x 		GMR  Index  [2:0]			0 = 68 bit 		1	0
      		CMD = (sadr<<7) | (gmr_index << 3)| 3'b010;
    		
    		//DQ	[67:0]
		//	Data
		DQ_reg = data;
		#(`T_CLK2X *2);

		//Command	CYC	8	 7	   6 		5 	4 	3 	2 		1 	0
		//Search	B 	SSR  	Index 	[2:0]		Comparand     Register    Index	 				1	0
		CMD = (ssr << 6) | (comp << 2) | 3'b10;
		  		
    		#(`T_CLK2X *2);
    		CMDV = 0;
    		CMD = 9'hZ;
    		DQ_reg = 68'hZ;
    		enable = 0;
	end
endtask

//***************************** Search136 ****************************************************************************
//Description:		Performs a 136-bit search on tables configured as x136 in device
//Syntax:		Search136(GMR_Index,SADR, COMP, SSR, DATA0, DATA1);
//		Parameters		Size	Description
//		GMR_Index		3'h	This parameter carries the GMR Index to mask the search on the data/mask array
//		SADR		3'h 	This parameter is supplied by the host ASIC for SRAM data write
//		COMPARAND		4'h 	This parameter carries the index of the Comparand Register (COMP0-31)
//		SSR		3'h 	This parameter carries the index of the Search Successful Register(SSR0-7)
//		DATA0		68'h	This parameter carries the 68-bit data to be searched in all even locations
//		DATA1		68'h	This parameter carries the 68-bit data to be searched in all odd locations
//Example:		Search68(0,0,2,0,23456789F,98765432F);
//Number of cycles:			4: 1 device  5: 1-8 devices  6: 1-31 devices (See Table 10-21 in the CYNSE70064A datasheet)
//********************************************************************************************************************
task Search136;

	input [2:0] gmr_index;
	input [1:0] sadr;
	input [3:0] comp;
	input [2:0] ssr;
	input [67:0] data0;
	input [67:0] data1;

	begin
    		CMDV = 1;
    		enable = 1;
    		
    		//Command	CYC	8	 7	   6 		5 	4 	3 	2 		1 	0
		//Search 	A 	SADR[21]	SADR[20] 	x 		GMR  Index  [2:0]			0 = 136 bit 		1	0
      		CMD = (sadr<<6) | (gmr_index << 3)| 3'b010;
    		
    		//DQ	[67:0]
		//	Data0
		DQ_reg = data0;
		#(`T_CLK2X *2);

		//Command	CYC	8	 7	   6 		5 	4 	3 	2 		1 	0
		//Search	B 	SSR  	Index 	[2:0]		Comparand     Register    Index	 				1	0
	
  		CMD = (ssr << 6) | (comp << 2) | 3'b10;
  		//DQ	[67:0]
		//	Data1
		DQ_reg = data1;
    		#(`T_CLK2X *2);
    		CMDV = 0;
    		CMD = 9'hZ;
    		DQ_reg = 68'hZ;
    		enable = 0;
	end
endtask

//***************************** Search272 ****************************************************************************
//Description:		Performs a 272-bit search on tables configured as x272 in device
//Syntax:		Search272(gmr_index1, gmr_index0, sadr, ssr, data3, data2, data1, data0);
//		Parameters		Size	Description
//		GMR_Index1		3'h	This parameter carries the GMR Index to mask the search on the data/mask array
//		GMR_Index0		3'h	This parameter carries the GMR Index to mask the search on the data/mask array
//		SADR		2'h 	This parameter is supplied by the host ASIC for SRAM data write
//		SSR		3'h 	This parameter carries the index of the Search Successful Register(SSR0-7)
//		DATA3		68'h	This parameter carries the 68-bit data 
//		DATA2		68'h	This parameter carries the 68-bit data 
//		DATA1		68'h	This parameter carries the 68-bit data 
//		DATA0		68'h	This parameter carries the 68-bit data 
//Example:		Search272(0,0,2,0,23456789F,98765432F, 987654333, 987653333);
//Number of cycles:			4: 1 device  5: 1-8 devices  6: 1-31 devices (See Table 10-26 in the CYNSE70064 datasheet)
//********************************************************************************************************************
task Search272;
	
	input [2:0] gmr_index1;
	input [2:0] gmr_index0;
	input [1:0] sadr;
	input [2:0] ssr;
	input [67:0] data3;
	input [67:0] data2;
	input [67:0] data1;
	input [67:0] data0;
	
	begin
		CMDV =1 ;
		enable = 1;
		
		//Cycle A
    		//Command	CYC	8	 7	   6 		5 	4 	3 	2 		1 	0
		//Search 	A 	ignore 	 ignore	   ignore 		GMR  Index1  [2:0]			1 = 272 bit 		1	0
		CMD = {3'b0, gmr_index1, 3'b110};    
		//DQ	[67:0]
		//data3
		DQ_reg = data3;
		#(`T_CLK2X *2);
		
		//Cycle B
		//Command CYC is same as Cycle A
		
		//DQ [67:0]
		//data2
		DQ_reg = data2;
		#(`T_CLK2X *2);
		
		//Cycle C
		//Command	CYC	8	 7	   6 		5 	4 	3 	2 		1 	0
		//Search 	C sadr[21] sadr[20]	   ignore 			     GMR  Index0  [2:0]				0 		1	0
		CMD = {sadr, 1'b0, gmr_index0, 3'b010};  
//DQ[67:0]
//	data1		
		DQ_reg = data1;
		#(`T_CLK2X *2);
		
		//Cycle D
		//Command	CYC	8	 7	   6 		5 	4 	3 	2 		1 	0
		//Search 	C    	    ssr 	     [2:0]	     		ignore  ignore  ignore	ignore 				1	0

		CMD = {ssr, 6'b000010}; 
		
//DQ[67:0]
//	data0		
		DQ_reg = data0;
		
		#(`T_CLK2X *2);
    		CMDV = 0;
    		CMD = 9'hZ;
    		DQ_reg = 68'hZ;
    		enable = 0;		
		
	end
endtask