/*
 * coverage.sv: Base class for coverage definition classes 
 * Copyright (C) 2009 CESNET
 * Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 0. Redistributions of source code must retain the above copyright
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
 * $Id: coverage.sv 8657 2009-06-04 10:57:57Z washek $
 *
 * TODO:
 *
 */

package coverage_pkg;

import sv_common_pkg::*;

// ----------------------------------------------------------------------------
// -- Coverage Base Class
// ----------------------------------------------------------------------------
/* Base class for all functional coverage measurement classes. It contains
 * definitions of common tasks and functions.
 */
virtual class Coverage extends DriverCbs;
  
  bit enabled = 0;
  
  // Enable coverage checking
  virtual task setEnabled();
    enabled = 1;
    fork
       run();
    join_none;
  endtask
  
  // Disable coverage checking
  virtual task setDisabled();
    enabled = 0;
  endtask
  
  // Runs coverage checking (main loop)
  virtual task run();
    // By default it does nothing
  endtask
  
  // Returns current coverage in percents
  virtual function real getCoverage();
    getCoverage = 0.0; // By default it does nothing
  endfunction
  
  // Print coverage info to output
  virtual function void display();
    // By default it does nothing
  endfunction
  
endclass : Coverage


// ----------------------------------------------------------------------------
// -- Coverage Wrapper
// ----------------------------------------------------------------------------
/* Wrapper that contains other coverages. All coverage measuring objects must
 * be put into covList and then enabling, disabling, getting total coverage
 * and writing it to output, is done by this class.
 */
virtual class CoverageWrapper extends Coverage;
  
  Coverage covList[$]; // List of all measured coverages
  
  // Enable coverage measures
  virtual task setEnabled();
    foreach (covList[i])
      covList[i].setEnabled();
  endtask : setEnabled
  
  // Disable coverage measures
  virtual task setDisabled();
    foreach (covList[i])
      covList[i].setDisabled();
  endtask : setDisabled
  
  // Get total coverage
  virtual function real getCoverage();
    foreach (covList[i])
      getCoverage += covList[i].getCoverage();
    getCoverage /= covList.size();
  endfunction : getCoverage
  
  // Display coverage statistic
  virtual function void display();
    $display("\n*************** Coverage: ***************");
    foreach (covList[i])
      covList[i].display();
    $display("------------------------------------------------------------");
    $display("Total functional coverage: \t\t%3.2f %%", getCoverage());
  endfunction : display
  
endclass : CoverageWrapper

endpackage
