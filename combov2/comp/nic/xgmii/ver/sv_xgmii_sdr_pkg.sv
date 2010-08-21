/*
 * sv_xgmii_sdr_pkg.sv: SystemVerilog XGMII SDR package
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

// XGMII Interface
`include "xgmii_ifc.sv"

package sv_xgmii_sdr_pkg; 

  import sv_common_pkg::*; // Import SV common classes

  `include "xgmii_transaction.sv"
  `include "xgmii_driver_sdr.sv"
  `include "xgmii_monitor_sdr.sv"

endpackage : sv_xgmii_sdr_pkg

package sv_xgmii_sdr_monitor_pkg; 

  import sv_common_pkg::*; // Import SV common classes

  `include "xgmii_transaction.sv"
  `include "xgmii_monitor_sdr.sv"

endpackage : sv_xgmii_sdr_monitor_pkg

package sv_xgmii_sdr_driver_pkg; 

  import sv_common_pkg::*; // Import SV common classes

  `include "xgmii_transaction.sv"
  `include "xgmii_driver_sdr.sv"

endpackage : sv_xgmii_sdr_driver_pkg
