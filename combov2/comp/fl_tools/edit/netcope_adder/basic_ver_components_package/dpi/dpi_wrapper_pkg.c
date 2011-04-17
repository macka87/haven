/* *****************************************************************************
 * Project Name: Hardware - Software Framework for Functional Verification 
 * File Name:    C Wrapper
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
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
static unsigned char* lastData = NULL;

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
		return 1;

  // create sze 
  sze = szedata_open(sze_dev);
  if (sze == NULL)
    return 1;
		
	ret = szedata_subscribe3(sze, &rx, &tx);
	
	if (ret){
    szedata_close(sze); 
    sze = NULL;
    return 1; 
  }
  
  else { 
    ret = szedata_start(sze);
	  if (ret){
      szedata_close(sze); 
      sze = NULL;
      return 1; 
    }   
  }
  
  return 0;
}    

/*
 *  Close DMA Channel after data transport. 
 */    
int c_closeDMAChannel(){
	if (sze == NULL)
		return 1;

  szedata_close(sze);
  sze = NULL;
  return 0;
}

/*
 *  Data transport through DMA Channel. 
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
  
  return 0;
}  

/*
 *  Data transport through DMA Channel. 
 */
int c_receiveData(unsigned int* size, const svOpenArrayHandle outhwpkt) {
  unsigned int len;
  unsigned char *data;
	unsigned char *outData;

	// retrieve the pointer to the SystemVerilog array
	outData = svGetArrayPtr(outhwpkt);

	// read next data from the buffer
  data = szedata_read_next(sze, &len);

	if (data) {
		// in case something was read, copy it to the SystemVerilog array
		lastData = data;
		memcpy(outData, data, len);
		*size = len;
	}
	else
	{
		*size = 0;
	}

  return 0;
} 
