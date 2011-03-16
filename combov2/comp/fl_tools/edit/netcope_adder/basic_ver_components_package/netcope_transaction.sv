/* *****************************************************************************
 * Project Name: Hardware-Software Framework for Functional Verification
 * File Name:    NetCOPE Transaction Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
 
 class NetCOPETransaction extends Transaction;
      
   /*
    * Public Class Atributes
    */
   
    //int headerWidth       = 8;  //! header width in Bytes
   
    // NetCOPE header
    byte endpointID       = 0;  //! hardware endpoint indentification
    byte endpointProtocol = 0;  //! hardware endpoint protocol
    byte transType        = 0;  //! transaction type (data, control)
    byte ifcProtocol      = 0;  //! interface protocol
    byte ifcInfo          = 0;  //! support interface information
    
    // transported data 
    byte unsigned data[];

   /*
    * Public Class Methods
    */
    
   /*!
    * Function displays the current values of the transaction or data described
    * by this instance in a human-readable format on the standard output.
    *
    * \param prefix - transaction type
    */
    virtual function void display(string prefix = "");
      if (prefix != "") begin
        $write("---------------------------------------------------------\n");
        $write("-- %s\n",prefix);
        $write("---------------------------------------------------------\n");
      end
      
      //$write("headerWidth in bytes : %d\n",headerWidth);
      $write("endpointID: %x\n",endpointID);
      $write("endpointProtocol: %x\n",endpointProtocol);
      
      if (transType == 0) $write("Data transaction\n");
      else if (transType == 1) $write("Control START transaction\n");
      else if (transType == 2) $write("Control WAIT transaction\n");
      else if (transType == 3) $write("Control WAITFOREVER transaction\n");
      else if (transType == 4) $write("Control STOP transaction\n");
      else if (transType == 5) $write("Control SRC_RDY transaction\n");
      
      $write("ifcProtocol: %x\n",ifcProtocol);
      $write("ifcInfo: %x\n",ifcInfo);
      $write("\n");
      
      for (int j=0; j < data.size; j++) begin 
        $write("%x ",data[j]);
      end  
        
      $write("\n");    
    endfunction : display
    
 endclass: NetCOPETransaction