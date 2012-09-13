//xbeles00
//dut_if - interface medzi testovacim prostredim a testovanym zariadenim

interface dut_if();

  logic CLK;
  logic RESET;
  logic[1:0] OPERACIA;
  logic[3:0] OPERAND_A;
  logic[3:0] OPERAND_B;
  logic[4:0] VYSLEDOK;

endinterface: dut_if