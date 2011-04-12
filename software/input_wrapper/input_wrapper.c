/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
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

unsigned char * prepare_test_packet(struct szedata *sze, unsigned int *len);

/*
 * Main
 */
int main(){
  char *sze_dev       = "/dev/szedataII0";	/*!< path to device */
  unsigned int rx     = 0x00;
  unsigned int tx     = SZE2_ALL_INTERFACES;
  struct szedata *sze = NULL;
  unsigned short ifc  = 0;
  bool ret;
  unsigned int len;
  unsigned char *test_data;
  
  sze = szedata_open(sze_dev);
  if (sze == NULL)
    errx(3, "szedata_open failed");
		
	ret = szedata_subscribe3(sze, &rx, &tx);
	if (ret) 
    goto free_res;

	ret = szedata_start(sze);
	if (ret) 
    goto free_res;

  test_data = prepare_test_packet(sze, &len);
  
  ret = szedata_try_write_next(sze, test_data, len, ifc);

free_res:
	szedata_close(sze);
	return ret;
}

/*
 * Prepare test packet
 */
unsigned char * prepare_test_packet (struct szedata *sze, unsigned int *len){
	static const unsigned char data[] = {0x11,0x22,0x33};
  return szedata_prepare_packet(sze, NULL, 0, data, sizeof(data), len);
}
