/* *****************************************************************************
 * Project Name: Hardware - Software Framework for Functional Verification 
 * File Name:    Output Wrapper
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <err.h>
#include <libsze2.h>
#include "dpi_output_wrapper_pkg.h"

int c_receiveData(const svOpenArrayHandle hwpacket){
  char *sze_dev       = "/dev/szedataII0";	/*!< path to hw device */
  unsigned int rx     = 0x00;
  unsigned int tx     = SZE2_ALL_INTERFACES;
  struct szedata *sze = NULL;
  unsigned short ifc  = 0;
  unsigned int len;
  bool ret;
  
  unsigned char *auxPkt;                      // pointer to hwpacket data
  
  // create sze 
  sze = szedata_open(sze_dev);
  if (sze == NULL)
    errx(3, "szedata_open failed");
		
	ret = szedata_subscribe3(sze, &rx, &tx);
	if (ret) 
    goto free_res;

	ret = szedata_start(sze);
	if (ret) 
    goto free_res;
  
  // set pointer to hwpacket 
  auxPkt = (unsigned char*) svGetArrayPtr(hwpacket);
  // receive data from hardware
  auxPkt = szedata_read_next(sze, &len);

free_res:
	szedata_close(sze);
	
  return ret;
}
