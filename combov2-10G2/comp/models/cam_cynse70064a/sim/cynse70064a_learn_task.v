/************************************************************************/
/* Cypress Semiconductor Company Confidential                           */
/* Copyright 2004, Cypress Semiconductor. All Rights reserved           */
/* Cypress Semiconductor proprietary source code                        */
/* Permission to use, modify or copy this code is prohibited            */
/* without the express written consent of                               */
/* Cypress Semiconductor                                                */
/* Filename: cynse70064A_Learn_Task.v									*/
/* Release: 0.1 								        */
/* Last Updated: 24th September 2004 by HUJ,AOG                 								*/
/* This task file contains 68 bit learn and 136 bit learn function input*/
/************************************************************************/




//***************************** Learn68 ****************************************************************************
//Description:		Performs a 68-bit learn
//Syntax:		Learn68(SADR,COMP);
//		Parameters	Size	Description
//		SADR		2'h 	Bits that will be driven on SADR[21:20] in the SRAM write cycle
//		COMP		4'h	index of comparand reg pair (even #'d used for 68bit) 
//		
//		
//Example:		Learn68(0,0);
//Number of cycles:			4: 1 device  5: 1-8 devices  6: 1-31 devices (See Table 10-34 in the CYNSE70064 datasheet)
//********************************************************************************************************************

task Learn68;

	input [1:0] sadr;
	input [3:0] comp;

	begin
		//Cycle 1A
		//cmdv=1
		//cmd [1:0] learn inst
		//cmd [5:2] index of comparand reg pair (even #'d for 68bit)
		//cmd [8:7] bits that will be driven on SADR[21:20] in SRAM write cycle
	  	CMDV = 1;
    		enable = 1;
    		CMD = (sadr<<7) | (comp << 2)| 2'b11;
    		#(`T_CLK2X *2);
		
		//Cycle 1B
		//cmdv=1
		//cmd[1:0] =11
		//cmd[5:2] comparand pair
		//cmd[6] =0 for 68 bit, 1 for 136 bit
		CMD =  (comp << 2) | 2'b11;		
    		#(`T_CLK2X *2);
    		
    		//Cycle 2
		//cmdv=0 
    		CMDV = 0;
    		CMD = 9'hZ;
    		enable = 0;
    		#(`T_CLK2X *4);
	end
endtask

//***************************** Learn136 ****************************************************************************
//Description:		Performs a 136-bit learn
//Syntax:		Learn136(SADR,COMP);
//		Parameters	Size	Description
//		SADR		2'h 	Bits that will be driven on SADR[21:20] in the SRAM write cycle
//		COMP		4'h	index of comparand reg pair (even #'d used for 68bit) 
//		
//		
//Example:		Learn136(0,0);
//Number of cycles:			4: 1 device  5: 1-8 devices  6: 1-31 devices (See Table 10-34 in the CYNSE70064 datasheet)
//********************************************************************************************************************
task Learn136;

	
	input [1:0] sadr;
	input [3:0] comp;

	begin
		//Cycle 1A
		//cmdv=1
		//cmd [1:0] learn inst
		//cmd [5:2] index of comparand reg pair (even #'d for 68bit)
		//cmd [8:7] bits that will be driven on SADR[21:20] in SRAM write cycle
	   	CMDV = 1;
    		enable = 1;
      		CMD = (sadr<<7) | (comp << 2)| 2'b11;
		#(`T_CLK2X *2);
		
		//Cycle 1B
		//cmdv=1
		//cmd[1:0] =11
		//cmd[5:2] comparand pair
		//cmd[6] = 1 for 68 bit, 1 for 136 bit
		CMD = (1 << 6) | (comp << 2) | 3'b10; 		
    		#(`T_CLK2X *2);
    		
    		//Cycle 2
		//cmdv=0 
    		CMDV = 0;
    		CMD = 9'hZ;
    		enable = 0;
    		#(`T_CLK2X *4);
	end
endtask