/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Generated Input Controller Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
 
 class GenInputController extends InputController;
   
   /*
    * Public Class Atributes
    */ 
    
   Generator  generator;  // Transaction Generator 
   tTransMbx  transMbx;   // Transaction Mailbox
    
   /*
    * Public Class Methods
    */ 
    
   // Send generated transaction 
   virtual task sendGenerated(int unsigned transCount);
   endtask : sendGenerated 
   
 endclass : GenInputController  