/* *****************************************************************************
 * Project Name: Hardware - Software Framework for Functional Verification 
 * File Name:    Input Wrapper
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <err.h>
#include <libsze2.h>
#include "dpi_input_wrapper_pkg.h"

int c_sendData(const svOpenArrayHandle hwpacket){
  char *sze_dev       = "/dev/szedataII0";	/*!< path to hw device */
  unsigned int rx     = 0x00;
  unsigned int tx     = SZE2_ALL_INTERFACES;
  struct szedata *sze = NULL;
  unsigned short ifc  = 0;
  unsigned int len;
  bool ret;
  
  unsigned char *test_data;                   // sze test data
  unsigned char *auxPkt;                      // pointer to hwpacket data
  unsigned int pktSize = svSize(hwpacket, 1); // get packet size treba ???
  
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
  
  // receive data from hwpacket 
  auxPkt = (unsigned char*) svGetArrayPtr(hwpacket);
  // prepare packet for transfer to hardware    
  test_data = szedata_prepare_packet(sze, NULL, 0, auxPkt, sizeof(auxPkt), len);  
  // szewrite
  ret = szedata_try_write_next(sze, test_data, len, ifc);

free_res:
	szedata_close(sze);
	
  return ret;
}
