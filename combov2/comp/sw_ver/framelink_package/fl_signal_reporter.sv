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
  time timeCnt = 0ps;
  bit clkVal = 0;

  byte buffer [15:0];
  integer bufferStart = 0;
  const integer bufferEnd = 16;

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

    if (ntr.size % 8 != 0) begin
      $display("Invalid size of reporter packet!\n");
      $fatal;
    end

    for (int i = 8; i < ntr.size; ++i) begin
      buffer[bufferStart++] = ntr.data[i];

      if (bufferStart == bufferEnd) begin
        writeCycle(fId);
        bufferStart = 0;
      end
    end

  endfunction

  function void writeCycle(integer fId);

    // see   http://en.wikipedia.org/wiki/Value_change_dump   for the
    // description of the VCD format

    string dta;
    string drem;
    string tmpStr;

    for (int i = FL_WIDTH-1; i >= 0; --i) begin
      tmpStr.itoa(buffer[i / 8][i % 8]);
      dta = {dta, tmpStr};
    end

    for (int i = 6+REM_WIDTH-1; i >= 6; --i) begin
      tmpStr.itoa(buffer[8 + i / 8][i % 8]);
      drem = {drem, tmpStr};
    end

    // write values of signals
    $fwrite(fId, "b%s d\n", dta);
    $fwrite(fId, "b%s r\n", drem);
    $fwrite(fId, "%b[\n", buffer[8][5]);
    $fwrite(fId, "%b(\n", buffer[8][4]);
    $fwrite(fId, "%b]\n", buffer[8][3]);
    $fwrite(fId, "%b)\n", buffer[8][2]);
    $fwrite(fId, "%b>\n", buffer[8][1]);
    $fwrite(fId, "%b<\n", buffer[8][0]);

    // write time and clock
    $fwrite(fId, "#%d\n", timeCnt);
    $fwrite(fId, "%bc\n", clkVal);
    // perform a clock half-period
    timeCnt += clkPer / 2;
    clkVal ^= 1;
    $fwrite(fId, "#%d\n", timeCnt);
    $fwrite(fId, "%bc\n", clkVal);
    timeCnt += clkPer / 2;
    clkVal ^= 1;

  endfunction

  virtual function void writeProtocolHeader(integer fId);

    string initData;
    string initRem;

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
