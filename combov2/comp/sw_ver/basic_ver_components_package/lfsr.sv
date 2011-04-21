/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    LFSR Pseudo-random numbers generator 
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         10.4.2011 
 * ************************************************************************** */
 
/* 
 * This class is responsible for generating pseudo-random numbers. 
 * Implementation is based on principles of LFSR register. Unit must be enabled
 * by "setEnable()" function call. Unit can be stoped by "setDisable()" function
 * call.
 * 
 * \param pOutputWidth - required width of output random number 
 */   
 class LFSR #(int pOutputWidth = 8);
 
   /*
    * Public Class Atributes
    */
    string    inst;                       //! Generator identification
    bit       enabled;                    //! Generator is enabled
    mailbox #(logic [pOutputWidth-1:0]) lfsrMbx; 
    
    //! random numbers of LFSR generators
    logic [pOutputWidth-1:0][pOutputWidth-1:0] lfsr;     
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
                  mailbox #(logic [pOutputWidth-1:0]) lfsrMbx,
                  logic [pOutputWidth-1:0][pOutputWidth-1:0] seed,
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
      logic [pOutputWidth-1:0] fb;
    
      // initialization  
      for (int i=0; i<pOutputWidth; i++)
        fb[i] = lfsr[i][pOutputWidth-1];
      
      //$write("polynomial: %b\n", polynomial); 
            
      while (enabled) begin   //! Repeat while enabled
      
        // we use "pOutputWidth" number of LFSR registers to create random 
        // number 
        for (int i=0; i<pOutputWidth; i++) begin
        
          // we use Fibonnaci scheme to product output of LFSR register using
          // XOR function 
          for (int j=0; j<pOutputWidth-1; j++)
            if (polynomial[j] == 1) fb[i] = fb[i] ^ lfsr[i][j];
          
          //$write("i: %d fb: %b\n", i, fb[i]); 
          
          // actualization of LFSR registers
          lfsr[i] = (lfsr[i] >> 1);
          lfsr[i][pOutputWidth-1] = fb[i];
          //$write("i: %d lfsr: %b\n", i, lfsr[i]);
        end 
        
        //! put created random number to mailbox 
        //$write("fb: %b\n", fb); 
        lfsrMbx.put(fb);
      end
    endtask : run
 endclass : LFSR  