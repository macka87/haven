/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_chromosome.sv
 * Description:  Genetic Algorithm ALU Chromosome Class.
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         24.6.2013 
 * ************************************************************************** */

/*! 
 * Constructor - creates the ALU Chromosome object  
 */
 function AluChromosome::new(string name = "AluChromosome");
   super.new(name);
   
   // check configuration for ALU Chromosome
   //if (!uvm_config_db #(AluChromosomeConfig)::get(this, "", "AluChromosomeConfig", alu_chromosome_cfg)) 
   //  `uvm_error("MYERR", "AluChromosomeConfig doesn't exist!"); 
      
 endfunction: new



/*
 * It is recommended to use the following methods:
 * copy();
 * clone(); 
 * print();
 * compare();
 */   



/*! 
 * Print - displays Chromosome content  
 */    
 function void AluChromosome::print(string name);
 endfunction: print



/*! 
 * Evaluate - evaluate coverage of Chromosome   
 */    
 function void AluChromosome::evaluate(int coveredBins);
 endfunction: evaluate
   


