/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_coverage_info.svh
 * Description:  Information about coverage for ALU.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         2.8.2013
 * ************************************************************************** */

/*!
 * \brief AluCoverageInfo
 * 
 * This class stores information about ALU coverage.
 */
 
 class AluCoverageInfo extends uvm_object;
    
   //! UVM Factory Registration Macro
   `uvm_object_utils(AluCoverageInfo)
   
  /*! 
   * Data Members
   */  
   
   real alu_in_coverage;
   real alu_out_coverage;
       
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluCoverageInfo");
   
 endclass: AluCoverageInfo
 
 
 
/*! 
 * Constructor - creates the ChromosomeArray object  
 */
 function AluCoverageInfo::new(string name = "AluCoverageInfo");
   super.new(name);
 endfunction: new 