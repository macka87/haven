/* *****************************************************************************
 * Project Name: FIFO Functional Verification 
 * File Name:    fifo interface
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011         
 * ************************************************************************** */

/*
 *  FrameLink FIFO Control Interface declaration
 */ 
 interface iFrameLinkFifo #(STATUS_WIDTH = 8) (input logic CLK, RESET);  
   logic LSTBLK                    ;   // Last block detection
   logic [STATUS_WIDTH-1:0] STATUS ;   // MSBs of exact number of free items in the FIFO
   logic EMPTY                     ;   // FIFO is empty
   logic FULL                      ;   // FIFO is full
   logic FRAME_RDY                 ;   // At least one whole frame is in the FIFO
    

   // Clocking blocks  
   clocking ctrl_cb @(posedge CLK);
     input  LSTBLK, STATUS, EMPTY, FULL, FRAME_RDY;
   endclocking: ctrl_cb;

   // Control Modport
   modport ctrl (output  LSTBLK,
                 output  STATUS,
                 output  EMPTY,
                 output  FULL,
                 output  FRAME_RDY
                );
  
   modport ctrl_tb (clocking ctrl_cb);
 endinterface : iFrameLinkFifo
