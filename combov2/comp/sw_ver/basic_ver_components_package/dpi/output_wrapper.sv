/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Output Wrapper
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */

 import dpi_wrapper_pkg::*;

/*!
 * This class is responsible for taking NetCOPE transactions from HW through DPI
 * layer and sending them to SW part of the verification environment. Unit must
 * be enabled by "setEnable()" function call. Unit can be stoped by 
 * "setDisable()" function call.  
 */
 class OutputWrapper;
   /*
    * Public Class Atributes
    */
    string    inst;      //! Output Wrapper identification
    bit       enabled;   //! Output Wrapper enabling
    int       counter;   //! Output Wrapper busy signal
    tTransMbx outputMbx; //! NetCOPE transactions mailbox
        
   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates Output Wrapper object  
    *
    * \param inst     - Output Wrapper instance name
    * \param inputMbx - transaction mailbox     
    */     
    function new (string inst, 
                  tTransMbx outputMbx);
      this.inst        = inst;      //! Store wrapper identifier
      this.enabled     = 0;         //! Output Wrapper is disabled by default
      this.counter     = 0;
      this.outputMbx   = outputMbx; //! Store pointer to mailbox
    endfunction: new          
   
   /*! 
    * Enable Output Wrapper - eable wrapper and runs wrapper process
    */     
    virtual task setEnabled();
      enabled = 1;    //! Wrapper Enabling
      fork
        run();        //! Creating wrapper subprocess
      join_none;  
    endtask : setEnabled
        
   /*! 
    * Disable Output Wrapper
    */      
    virtual task setDisabled();
      enabled = 0;   //! Disable Wrapper
    endtask : setDisabled

   /*
    * Private Class Methods
    */
   
   /*! 
    * Run Output Wrapper - receives transactions through DPI and sends them 
    * to SW.
    */
    task run();
      Transaction tr;
      int res;
      int unsigned size;   
      NetCOPETransaction ntr;
            
			while (enabled) begin 
        size = 0;
				
				ntr = new();
			  ntr.hwpacket = new[4096];
        
        // we call C function (through DPI layer) for data transfer from hw
        res = c_receiveData(size, ntr.hwpacket);
        
        if (res == 1) $fatal("RECEIVE DATA in output wrapper failed!!!"); 
        else begin
          if (size > 0) begin
            // store the right size of data
						ntr.data = new[size]; 
						for (int i=0; i<size; i++)
						  ntr.data[i] = ntr.hwpacket[i]; 
						  
						// put received data to output mailbox
						$cast(tr, ntr);
						
						outputMbx.put(tr);  
            counter++;
            //$write("number of received transactions: %d\n",counter);
          end
					else begin
						#10ns;
					end
				end  
      end
    endtask : run 
 
 endclass : OutputWrapper 
