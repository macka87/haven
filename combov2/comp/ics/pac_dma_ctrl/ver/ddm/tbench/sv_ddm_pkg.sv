/*
 * \file sv_ddm_pkg.sv
 * \brief SystemVerilog Descriptor Download Manager package
 * \date Copyright (C) 2009 CESNET
 * \author Marcela Simkova <stud.fit.vutbr.cz>
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

package sv_ddm_pkg; 
   
  import sv_common_pkg::*; //! Import SV common classes
 
  `include "ddm_transaction.sv"
  `include "ddm_sw_modul.sv"
  `include "ddm_ring_modul.sv"
  `include "../../tx_ctrl/tbench/dma_modul.sv"
  `include "ddm_ib_modul.sv"
  `include "ddm_tx_driver.sv"
  `include "ddm_rx_driver.sv"
  `include "ddm_tx_monitor.sv"
  `include "ddm_rx_monitor.sv"
  `include "ddm_rxreq_modul.sv"
  `include "scoreboard.sv"
  `include "ddm_coverage.sv"

endpackage : sv_ddm_pkg
