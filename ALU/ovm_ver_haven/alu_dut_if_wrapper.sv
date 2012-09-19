/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_dut_if_wrapper.sv
 * Description:  OVM ALU Interface Wrapper
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         11.9.2012
 * ************************************************************************** */

package sv_alu_pkg;
 
   import ovm_pkg::*;
   
   /*!
   * \brief AluDutIfWrapper
   * 
   * OVM ALU Interface Wrapper
   * Wrapper is needed for an object in case it has to be stored in the
   * configuration table. Afterwards, other objects can easily manipulate with
   * interface signals. 
   */
   
   class AluDutIfWrapper #(int pDataWidth = 8) extends ovm_object;
      
     virtual iAluIn  #(pDataWidth) dut_alu_in_if;
     virtual iAluOut #(pDataWidth) dut_alu_out_if; 
     
   /*! 
     * Constructor - creates AluDutIfWrapper object  
     *
     * \param name     - instance name
     * \param arg      - virtual interface
     */ 
     function new(string name, 
                  virtual iAluIn #(pDataWidth) dut_alu_in_if,
                  virtual iAluOut #(pDataWidth) dut_alu_out_if
                  );
       super.new(name);
       this.dut_alu_in_if  = dut_alu_in_if;
       this.dut_alu_out_if = dut_alu_out_if;
     endfunction: new
  
   endclass: AluDutIfWrapper
 
endpackage