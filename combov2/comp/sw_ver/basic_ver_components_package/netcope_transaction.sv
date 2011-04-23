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
   
    // NetCOPE header
    byte endpointID       = 0;  //! hardware endpoint indentification
    byte endpointProtocol = 0;  //! hardware endpoint protocol
    byte transType        = 0;  //! transaction type (data, control)
    byte ifcProtocol      = 0;  //! interface protocol
    byte ifcInfo          = 0;  //! support interface information
    
    // transported data 
    byte unsigned data[];
    
    // hardware packet
    byte unsigned hwpacket[];

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
      
      if (transType == 0) $write("Data transaction: %x\n",transType);
      else if (transType == 1) $write("Control START transaction: %x\n",transType);
      else if (transType == 2) $write("Control WAIT transaction: %x\n",transType);
      else if (transType == 3) $write("Control WAITFOREVER transaction: %x\n",transType);
      else if (transType == 4) $write("Control STOP transaction: %x\n",transType);
      else if (transType == 5) $write("Control SRC_RDY transaction: %x\n",transType);
      
      $write("ifcProtocol: %x\n",ifcProtocol);
      $write("ifcInfo: %x\n",ifcInfo);
      $write("\n");
      
      for (int j=0; j < data.size; j++) begin 
        $write("%x ",data[j]);
      end  
        
      $write("\n");    
    endfunction : display
    
    /*!
    * Function prepares data for transfer to hardware - it connects NetCOPE
    * header with data to one block.  
    * !!! This function changes ENDIANITY for transfer through hardware !!!
    */
    virtual function void createHardwarePacket();
      // size of hardware packet = header(8B) + data size  
      hwpacket = new[8 + data.size];
      
      $write("<<<<<   INPUT  WRAPPER: HARDWARE PACKET: ");
      
      // copy of NetCOPE header
      hwpacket[0] = endpointID;
      $write("%x ",hwpacket[0]);
      hwpacket[1] = endpointProtocol;
      $write("%x ",hwpacket[1]);
      hwpacket[2] = 0; 
      $write("%x ",hwpacket[2]);
      hwpacket[3] = 0;
      $write("%x ",hwpacket[3]);
      hwpacket[4] = transType;
      $write("%x ",hwpacket[4]);
      hwpacket[5] = 0;
      $write("%x ",hwpacket[5]);
      hwpacket[6] = ifcProtocol;
      $write("%x ",hwpacket[6]);
      hwpacket[7] = ifcInfo; 
      $write("%x ",hwpacket[7]);

     /* hwpacket[7] = endpointID;
      hwpacket[6] = enpointProtocol;
      hwpacket[5] = 0;
      hwpacket[4] = 0;
      hwpacket[3] = transType;
      hwpacket[2] = 0;
      hwpacket[1] = ifcProtocol;
      hwpacket[0] = ifcInfo;*/  
      
      // copy of data
      
      for (int i= 8; i<(data.size+8); i++)begin
        hwpacket[i] = data[i-8]; 
        $write("%x ",hwpacket[i]);
      end  
      $write("\n");


    endfunction : createHardwarePacket
    
 endclass: NetCOPETransaction
