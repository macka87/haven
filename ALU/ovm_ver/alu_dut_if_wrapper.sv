/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_dut_if_wrapper.sv
 * Description:  OVM ALU Interface Wrapper
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         11.9.2012
 * ************************************************************************** */

 /*!
 * \brief AluDutIfWrapper
 * 
 * OVM ALU Interface Wrapper
 * wrapper is needed for object when it has to be stored into the configuration 
 * table, we store object into the configuration table when number of other 
 * objects need to manipulate with it    
 */
 
 class AluDutIfWrapper #(int pDataWidth = 8) extends ovm_object;
    
   virtual AluDutIf #(pDataWidth) dut_if1;

  /*! 
   * Constructor - creates AluDutIfWrapper object  
   *
   * \param name     - instance name
   * \param arg      - virtual interface
   */ 
   function new(string name, virtual dut_if arg);
     super.new(name);
     dut_if1 = arg;
   endfunction: new

 endclass: AluDutIfWrapper