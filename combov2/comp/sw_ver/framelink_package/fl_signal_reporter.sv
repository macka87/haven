/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    FrameLink Signal Reporter Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         11.8.2011 
 * ************************************************************************** */
 
import math_pkg::*;

class FrameLinkSignalReporter #(int FL_WIDTH = 0) extends SignalReporter;

  time clkPer;
  time rstTime;
  time timeCnt;


  const integer REM_WIDTH = log2(FL_WIDTH/8);
 /*! 
  * Constructor 
  */    
  function new(string inst,
               byte id,
               tTransMbx mbx,
               time clkPer,
               time rstTime
               ); 
    super.new(inst, id, mbx);
    this.clkPer  = clkPer;
    this.rstTime = rstTime;
    this.timeCnt = 0ps;

    // general assert
    if ((FL_WIDTH != 8) && (FL_WIDTH != 16) && (FL_WIDTH != 32) &&
      (FL_WIDTH != 64) && (FL_WIDTH != 128)) begin
      $fatal;
    end

    // we currently do not support anything beyond 64b (the modifications to
    // support other widths should not be hard though)
    if (FL_WIDTH != 64) begin
      $fatal;
    end

  endfunction: new

  virtual function void writeReport(ref NetCOPETransaction ntr, integer fId);

    // see   http://en.wikipedia.org/wiki/Value_change_dump   for the
    // description of the VCD format

  endfunction

  virtual function void writeProtocolHeader(integer fId);

    string initData;
    string initRem;
    bit clkVal = 1;

    for (int i = 0; i < FL_WIDTH; ++i) begin
      initData = {initData, "0"};
    end

    for (int i = 0; i < REM_WIDTH; ++i) begin
      initRem = {initRem, "0"};
    end

    // see   http://en.wikipedia.org/wiki/Value_change_dump   for the
    // description of the VCD format

    // the boring part
    $fwrite(fId, "$comment\n");
    $fwrite(fId, "  FrameLink signal dump from reporter %d\n", id);
    $fwrite(fId, "$end\n");
    $fwrite(fId, "\n");
    $fwrite(fId, "$timescale 1ps $end\n");
    $fwrite(fId, "\n");

    // signals declaration
    $fwrite(fId, "$scope module top $end\n");
    $fwrite(fId, "$var wire  1 c clk $end\n");
    $fwrite(fId, "$var wire  1 ^ reset $end\n");
    $fwrite(fId, "$var wire %d d data $end\n", FL_WIDTH);
    $fwrite(fId, "$var wire %d r rem $end\n", REM_WIDTH);
    $fwrite(fId, "$var wire  1 [ sof_n $end\n");
    $fwrite(fId, "$var wire  1 ( sop_n $end\n");
    $fwrite(fId, "$var wire  1 ] eof_n $end\n");
    $fwrite(fId, "$var wire  1 ) eop_n $end\n");
    $fwrite(fId, "$var wire  1 > src_rdy_n $end\n");
    $fwrite(fId, "$var wire  1 < dst_rdy_n $end\n");
    $fwrite(fId, "$upscope $end\n");
    $fwrite(fId, "\n");

    // write initial values
    $fwrite(fId, "$enddefinitions $end\n");
    $fwrite(fId, "#0\n");
    $fwrite(fId, "1c\n");
    $fwrite(fId, "1^\n");
    $fwrite(fId, "b%s d\n", initData);
    $fwrite(fId, "b%s r\n", initRem);
    $fwrite(fId, "1[\n");
    $fwrite(fId, "1(\n");
    $fwrite(fId, "1]\n");
    $fwrite(fId, "1)\n");
    $fwrite(fId, "1>\n");
    $fwrite(fId, "1<\n");

    // process reset
    while (timeCnt < rstTime) begin
      $fwrite(fId, "#%d\n", timeCnt);
      $fwrite(fId, "%bc\n", clkVal);
      timeCnt += clkPer / 2;
      clkVal ^= 1;
    end

    $fwrite(fId, "#%d\n", rstTime);
    $fwrite(fId, "0^\n");
    $fwrite(fId, "%bc\n", clkVal);

  endfunction
endclass
