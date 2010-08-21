/*
 * test.sv: SystemVerilog DPI functions test
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 * 3. Neither the name of the Company nor the names of its contributors
 *    may be used to endorse or promote products derived from this
 *    software without specific prior written permission.
 *
 * This software is provided ``as is'', and any express or implied
 * warranties, including, but not limited to, the implied warranties of
 * merchantability and fitness for a particular purpose are disclaimed.
 * In no event shall the company or contributors be liable for any
 * direct, indirect, incidental, special, exemplary, or consequential
 * damages (including, but not limited to, procurement of substitute
 * goods or services; loss of use, data, or profits; or business
 * interruption) however caused and on any theory of liability, whether
 * in contract, strict liability, or tort (including negligence or
 * otherwise) arising in any way out of the use of this software, even
 * if advised of the possibility of such damage.
 *
 * $Id: test.sv 2014 2008-03-30 20:47:16Z xkobie00 $
 *
 * TODO:
 *
 */
import dpi_scoreboard_pkg::*;

module testbench();
 
  initial begin
      tFlTransactionInfo info;
      $display("\n\n");
      $display("-------------------------------------\n");
      $display("SystemVerilog DPI: dpi_scoreboard_pkg\n");
      $display("-------------------------------------\n\n");

        info.stream_id=0;
        info.scenario_id=0;
        info.data_id=1;
        info.inst="Driver";
        assert(c_flPostTx(info,0,"1Prvni"));
        assert(c_flPostTx(info,0,"1Druhy"));
        assert(c_flPostTx(info,1,"1Treti")); 

        info.stream_id=0;
        info.scenario_id=0;
        info.data_id=1;
        info.inst="Monitor";
        assert(c_flPostRx(info,0,"1Prvni"));
        assert(c_flPostRx(info,0,"1Druhy"));
        assert(c_flPostRx(info,1,"1Treti"));

        info.stream_id=0;
        info.scenario_id=0;
        info.data_id=2;
        info.inst="Driver";
        assert(c_flPostTx(info,0,"2Prvni"));
        assert(c_flPostTx(info,0,"2Druhy"));
        assert(c_flPostTx(info,1,"2Treti")); 

        info.stream_id=0;
        info.scenario_id=0;
        info.data_id=2;
        info.inst="Monitor";
        assert(c_flPostRx(info,0,"2Prvni"));
        assert(c_flPostRx(info,0,"2Druhy"));
        assert(c_flPostRx(info,1,"2Treti"));

        c_display();
  end
endmodule

