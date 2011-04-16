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
struct szedata *sze = NULL;

//-----------------------------------------------------------------------------
//- USER Functions
//-----------------------------------------------------------------------------

/*
 *  Open DMA Channel for data transport. 
 */ 
int c_openDMAChannel(){
  char *sze_dev       = "/dev/szedataII0";	  // path to hw device 
  unsigned int rx     = 0x00;
  unsigned int tx     = SZE2_ALL_INTERFACES;
  bool ret;
  
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
int c_receiveData(unsigned int* size, unsigned char* outhwpkt){
  unsigned int len;
  int i;
  unsigned char *data;
  short events = SZEDATA_POLLRX;

  if (szedata_poll(sze, &events, SZE2_TX_POLL_TIMEOUT)<0) return 1;
  
  data = szedata_read_next(sze, &len);
  memcpy(outhwpkt, data, len);
  size = &len; 
   
  return 0;
} 
