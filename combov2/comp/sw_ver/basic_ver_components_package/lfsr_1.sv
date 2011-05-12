/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    LFSR (1 bit) Pseudo-random numbers generator 
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         12.5.2011 
 * ************************************************************************** */
 
/* 
 * This class is responsible for generating pseudo-random numbers. 
 * Implementation is based on principles of LFSR register. Unit must be enabled
 * by "setEnable()" function call. Unit can be stoped by "setDisable()" function
 * call.
 * 
 * \param pOutputWidth - required width of output random number 
 */   
 class LFSR_1 #(int pOutputWidth = 8);
 
   /*
    * Public Class Atributes
    */
    string    inst;                       //! Generator identification
    bit       enabled;                    //! Generator is enabled
    mailbox #(logic) lfsrMbx; 
    
    //! random numbers of LFSR generator
    logic [pOutputWidth-1:0] lfsr;     
    //! Polynomial in bit notation   
    logic [pOutputWidth-1:0] polynomial;  
    
   /*
    * Public Class Methods
    */
    
   /*!
    * Constructor - creates generator object 
    *
    * \param inst     - generator instance name
    * \param lfsrMbx  - mailbox for generated values  
    */           
    function new (string inst, 
                  mailbox #(logic) lfsrMbx,
                  logic [pOutputWidth-1:0] seed,
                  logic [pOutputWidth-1:0] polynomial
                  ); 
      this.enabled     = 0;         //! Generator is disabled by default
      this.inst        = inst;      //! Store generator identifier 
      this.lfsrMbx     = lfsrMbx;   //! Store pointer to mailbox
      this.lfsr        = seed;
      this.polynomial  = polynomial;
    endfunction: new   
    
   /*! 
    * Enable Generator - enable generator and runs its process
    */
    task setEnabled();
      enabled = 1;  //! Generator Enabling
      fork         
        run();      //! Creating generator subprocess
      join_none;    //! Don't wait for ending
    endtask : setEnabled
        
   /*! 
    * Disable Generator
    */
    task setDisabled();
      enabled = 0;  //! Disable generator
    endtask : setDisabled
    
   /*! 
    * Run Generator - produce random numbers 
    */  
    task run();
      logic fb;
    
      // initialization  
      fb = lfsr[pOutputWidth-1];
      
      while (enabled) begin   //! Repeat while enabled
      
        // we use Fibonnaci scheme to product output of LFSR register using
        // XOR function 
        for (int i=0; i<pOutputWidth-1; i++)
          if (polynomial[i] == 1) fb = fb ^ lfsr[i];
          
        // actualization of LFSR registers
        lfsr = (lfsr >> 1);
        lfsr[pOutputWidth-1] = fb;
         
        //! put created random number to mailbox 
        lfsrMbx.put(fb);
      end
    endtask : run
 endclass : LFSR_1