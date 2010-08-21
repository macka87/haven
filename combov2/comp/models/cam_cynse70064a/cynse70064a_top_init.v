/*
-- cynse70064a_top_init.v: Inicialization of the CAM model
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Dedek <dedek@liberouter.org>
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
-- $Id: cynse70064a_top_init.v 2269 2008-04-24 11:25:44Z dedekt1 $
--
-- TODO:
--
-- 
*/
`define CAM_2MEG 1 //Simulating CYNSE70064: 2Mb device
//`include "cynse70032_064_128.vh"  //including the definition module
		
module CYNSE70064A_top(	CLK2X,
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
//parameters
parameter data_file = "modelsim_data_init.dat";
parameter mask_file = "modelsim_mask_init.dat";			
			
//inputs
input 				CLK2X;
input 				PHS_L;
input 				RST_L;
inout [67:0] 	DQ;		//data bus
input 		    		CMDV;           // cmd valid
input [8:0]   	CMD;            // cmd
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
output [21:0] 	SADR;
output 		    		FULL;
output [1:0]		    	FULO;
output [1:0]		    	LHO;
output [2:0]		    	BHO;



   
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


initial
	/*Init */
	begin
	$readmemh(data_file, Main.model.cam_data_array);
	$readmemh(mask_file, Main.model.cam_mask_array);
	end
endmodule
