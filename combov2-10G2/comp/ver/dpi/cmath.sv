package cmath;

  /* "pure" function
   * - he result of the function solely depends on the
   *   values of its inputs.
   * - The function has no side effects, i.e., it does
   *   not change the value of any variable directly or indirectly
   *   (by calling other functions). 
   */
  import "DPI-C" pure function real c_sin(input real x);
  import "DPI-C" pure function real c_sqrt(input real x);

  import "DPI-C" function void c_testPassing(output int x);


endpackage

