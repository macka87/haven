/*
 * sv_sum_pkg.sv: SystemVerilog Status Update Manager package
 * Copyright (C) 2009 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
 *
 * TODO:
 */

package sv_sum_pkg; 

  import sv_common_pkg::*; // Import SV common classes

  `include "sum_mi32_transaction.sv"
  `include "su_transaction.sv"
  `include "su_driver.sv"
  `include "sum_rf_transaction.sv"
  `include "sum_rf_driver.sv"
  `include "sum_misc_driver.sv"
  `include "../../tx_ctrl/tbench/dma_modul.sv"
  `include "sum_timeout_module.sv"
  `include "sum_transaction.sv"
  `include "sum_checker.sv"
  `include "sum_ib_monitor.sv"
  `include "scoreboard.sv"
  `include "sum_reference_model.sv"

endpackage : sv_sum_pkg
