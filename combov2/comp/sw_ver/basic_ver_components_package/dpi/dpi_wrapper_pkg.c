/* *****************************************************************************
 * Project Name: Hardware - Software Framework for Functional Verification 
 * File Name:    C Wrapper
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         3.5.2011 
 * ************************************************************************** */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <err.h>
#include <libsze2.h>
#include "dpi_wrapper_pkg.h"

//-----------------------------------------------------------------------------
//- GLOBAL VARIABLES
//-----------------------------------------------------------------------------
static struct szedata *sze = NULL;

//-----------------------------------------------------------------------------
//- USER Functions
//-----------------------------------------------------------------------------

/*
 *  Open DMA Channel for data transport. 
 */ 
int c_openDMAChannel(){
  char *sze_dev       = "/dev/szedataII0";	  // path to hw device 
  unsigned int rx     = SZE2_ALL_INTERFACES;
  unsigned int tx     = SZE2_ALL_INTERFACES;
  bool ret;
  
	// check if sze is not already initialized
	if (sze != NULL)
		return EXIT_FAILURE;

  // create sze 
  sze = szedata_open(sze_dev);
  if (sze == NULL)
    return EXIT_FAILURE;
		
	ret = szedata_subscribe3(sze, &rx, &tx);
	
	if (ret){
    szedata_close(sze); 
    sze = NULL;
    return EXIT_FAILURE; 
  }
  
  else { 
    ret = szedata_start(sze);
	  if (ret){
      szedata_close(sze); 
      sze = NULL;
      return EXIT_FAILURE; 
    }   
  }
  return EXIT_SUCCESS;
}    

/*
 *  Close DMA Channel after data transport. 
 */    
int c_closeDMAChannel(){
	if (sze == NULL)
		return EXIT_FAILURE;

  szedata_close(sze);
  sze = NULL;
  return EXIT_SUCCESS;
}

/*
 *  Data transport through DMA Channel - transaction is sent to hardware. 
 */
int c_sendData(const svOpenArrayHandle inhwpkt){
  unsigned char *test_data;                     // sze test data
  unsigned char *auxPkt;                        // pointer to hwpacket data
  unsigned int pktSize = svSize(inhwpkt, 1);
  unsigned int len;
  bool ret;
  unsigned short ifc  = 0;
  
  // set pointer to hwpacket  
  auxPkt = (unsigned char*) svGetArrayPtr(inhwpkt);
  
  // prepare packet for transfer to hardware    
  test_data = szedata_prepare_packet(sze, NULL, 0, auxPkt, pktSize, &len);  

  // szewrite - send data to hardware
  ret = szedata_try_write_next(sze, test_data, len, ifc);
	if (ret){
		return EXIT_FAILURE;
	}
  return EXIT_SUCCESS;
}  

/*
 *  Data transport through DMA Channel - transaction is received from hardware.
 */
int c_receiveData(unsigned int* size, const svOpenArrayHandle outhwpkt){
  unsigned int len;
  unsigned char *data;
	unsigned char *outData;

  // retrieve the pointer to the SystemVerilog array
	outData = svGetArrayPtr(outhwpkt);

	// read next data from the buffer
  data = szedata_read_next(sze, &len);

	if (data) {
		unsigned short print_options =
			SZE2_PRINT_OPTION_SW | SZE2_PRINT_OPTION_HW | SZE2_PRINT_OPTION_ALL;
		//szedata_print_packet(data, print_options);

		// in case something was read, copy it to the SystemVerilog array
		if (len <= 8){	
      // in case the length read is smaller than expected
			// (i.e. there is not complete header or any data)
			fprintf(stderr, "Received data too small! (%d)\n", len);
			return EXIT_FAILURE;
		}

		if (len > 4096)
		{
      // in case the length read is bigger than expected
			// (i.e. there is some other problem)
			fprintf(stderr, "Received data too large! (%d)\n", len);
			return EXIT_FAILURE;
		}

		// omit the first 8 bytes so that we can omit the NetCOPE header

		// !!!!!!!!!!!!!!!!!! ATTENTION !!!!!!!!!!!!!!!!!!!!!!!!!!
		// the following is ONLY for debugging purposes, so that the wrapper would
		// work with FL_HW_MONITOR_SMART without changes to the SystemVerilog
		// code! After the SystemVerilog code is changed to reflect this, delete
		// the following two lines and uncomment the other ones.
		//data += 16;
		//len -= 16;

		data += 8;
		len -= 8;
		*size = len;
		
    // copy to the SystemVerilog array without the NetCOPE header
		memcpy(outData, data, len);    		
  }
	else{
		*size = 0;
	}

  return EXIT_SUCCESS;
}  
