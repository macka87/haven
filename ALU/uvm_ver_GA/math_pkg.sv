/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    math_pkg.sv
 * Description:  Package of mathematics functions.
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013 
 * ************************************************************************** */
 
 package math_pkg;

/*
 * log2 function
 */   
 function int log2 (input int n);
   int a;
   int m;  
   a=0;
   m=1;
   while (m<n) begin
     a=a+1;
     m=m*2;
   end
   log2=a;
 endfunction : log2

/*
 * pow function
 */
 function longint pow (input int x, int a);
   longint mocnina; 
  
   if (a==0) mocnina=1;
   else begin
     mocnina=1;
     for (int i=0; i<a; i++)
     mocnina=mocnina*x;
   end
  
   pow=mocnina;
 endfunction : pow
 
/*
 * abs function
 */
 function int abs (input int n);
   if (n<0) return -n;
   else return n;
 endfunction : abs

/*
 * max function
 */
 function int max (input int x, int y);
   if (x < y)
     return y;
   else
     return x;
 endfunction : max

/*
 * min function
 */
 function int min (input int x, int y);
   if (x < y)
     return x;
   else
     return y;
 endfunction : min

 endpackage : math_pkg
