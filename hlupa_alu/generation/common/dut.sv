//xbeles00
//dut - testovane zariadenie

module dut(dut_if _if);

  en_alu #()

   VHDL_DUT_U (
     .CLK            (_if.CLK),
     .RST            (_if.RESET),
     .OPERACIA       (_if.OPERACIA),
     .OPERAND_A      (_if.OPERAND_A),
     .OPERAND_B      (_if.OPERAND_B),
     .VYSLEDOK       (_if.VYSLEDOK));
  

endmodule: dut