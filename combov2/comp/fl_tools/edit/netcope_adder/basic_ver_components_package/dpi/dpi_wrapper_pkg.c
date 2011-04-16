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
    errx(3, "szedata_open failed");
		
	ret = szedata_subscribe3(sze, &rx, &tx);
	
	if (ret) szedata_close(sze);  
  
  else { 
    ret = szedata_start(sze);
	  if (ret) szedata_close(sze);   
  }
  
  return ret;
}    

/*
 *  Close DMA Channel after data transport. 
 */    
int c_closeDMAChannel(){
  szedata_close(sze);
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
  
  return ret;
}  

/*
 *  Data transport through DMA Channel. 
 */
int c_receiveData(unsigned int size, const svOpenArrayHandle outhwpkt){
  unsigned char *test;
  unsigned char *auxPkt;                        // pointer to hwpacket data
  unsigned int len;
  int i;
   
  unsigned char test_data[] = {0x00,0x18,0xF3};
  test = test_data;
  
  // set pointer to hwpacket  
  auxPkt = (unsigned char*) svGetArrayPtr(outhwpkt);
  
  for (i=0; i<3; i++)
    *auxPkt++ = *test++;
  
  /*  //auxPkt = {0x00,0x18,0xF3};
    auxPkt[0] = 0x00;
    auxPkt[1] = 0x18;
    auxPkt[2] = 0xF3;
  
  printf("test data: \n");
  for (i=0; i<3; i++)
    printf("%x ",auxPkt[i]);
  printf("\n"); */
  
  // szeread - receive data from hardware
  //test_data = szedata_read_next(sze, &len);
  
  //for (i=0; i<len; i++)
  //  printf("%x ",test_data[i]);
  //printf("\n");
  
  return 0;
} 
