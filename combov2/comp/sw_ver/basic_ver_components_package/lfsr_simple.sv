/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Generic LFSR Pseudo-random numbers generator 
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         29.5.2012 
 * ************************************************************************** */
 
/* 
 * This class is responsible for generating pseudo-random numbers. 
 * Implementation is based on principles of LFSR register. Unit must be enabled
 * by "setEnable()" function call. Unit can be stoped by "setDisable()" function
 * call.
 * 
 * \param pOutputWidth - required width of output random number 
 */   
 class LFSRSimple #(int pOutputWidth = 8);
 
   /*
    * Public Class Atributes
    */
    string    inst;                       //! Generator identification
    bit       enabled;                    //! Generator is enabled
    mailbox #(logic [pOutputWidth-1:0]) lfsrMbx; 
    
    //! random numbers of LFSR generator
    logic [pOutputWidth-1:0] lfsr;     
    //! Polynomial in bit notation (e.g. x^3 + x^2 + 1 = [110]1, the last 1 is
    //  fixed, so we need only part [110]   
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
                  mailbox #(logic [pOutputWidth-1:0]) lfsrMbx,
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
       
      logic new_bit; 
    
      while (enabled) begin   //! Repeat while enabled
        // initialization with the highest bit of seed value - the highest bit
        // of polynomial is always set to 1!
        new_bit = lfsr[pOutputWidth-1];
        
        //! put created random number to mailbox 
        lfsrMbx.put(lfsr);
        
        // we use Fibonnaci scheme to product output of LFSR register using
        // XOR function (pOutputWidth-1) because the last bit is used in init 
        for (int i=0; i<pOutputWidth-1; i++)
          if (polynomial[i] == 1) new_bit = new_bit ^ lfsr[i];
        
        // actualization of LFSR registers
        lfsr = (lfsr >> 1);
        lfsr[pOutputWidth-1] = new_bit;
      end
    endtask : run
 endclass : LFSRSimple