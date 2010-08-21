//
// Internal Bus Master Endpoint Interface
//

interface iIbEndpointMaster (input logic CLK, RESET);

   logic [63:0] GLOBAL_ADDR;
   logic [31:0] LOCAL_ADDR;
   logic [11:0] LENGTH;
   logic [15:0] TAG;
   logic [ 1:0] TRANS_TYPE;
   logic        REQ;
   logic        ACK;
   logic [15:0] OP_TAG;
   logic        OP_DONE;

   modport driver (
      input  CLK, RESET, ACK, OP_TAG, OP_DONE,
      output GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TRANS_TYPE, REQ
   );

   modport endpoint (
      input  CLK, RESET, GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TRANS_TYPE, REQ,
      output ACK, OP_TAG, OP_DONE
   );

   modport monitor (
      input  CLK, RESET, ACK, OP_TAG, OP_DONE,
             GLOBAL_ADDR, LOCAL_ADDR, LENGTH, TAG, TRANS_TYPE, REQ
   );

endinterface


