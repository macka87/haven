/*
 * ics.c:
 * Copyright (C) 2007 CESNET
 * Author: Petr  Springl  <xsprin01@liberouter.org>
 *
 * LICENSE TERMS
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 * 3. Neither the name of the Company nor the names of its contributors
 *    may be used to endorse or promote products derived from this
 *    software without specific prior written permission.
 *
 * ALTERNATIVELY, provided that this notice is retained in full, this
 * product may be distributed under the terms of the GNU General Public
 * License (GPL), in which case the provisions of the GPL apply INSTEAD
 * OF those given above.
 *
 * This software is provided ``as is'', and any express or implied
 * warranties, including, but not limited to, the implied warranties of
 * merchantability and fitness for a particular purpose are disclaimed.
 * In no event shall the company or contributors be liable for any
 * direct, indirect, incidental, special, exemplary, or consequential
 * damages (including, but not limited to, procurement of substitute
 * goods or services; loss of use, data, or profits; or business
 * interruption) however caused and on any theory of liability, whether
 * in contract, strict liability, or tort (including negligence or
 * otherwise) arising in any way out of the use of this software, even
 * if advised of the possibility of such damage.
 *
 * $Id: ics.c 4748 2008-08-13 13:28:28Z xhanka00 $
 *
 */

#include "ics.h"

__RCSID("$Id: ics.c 4748 2008-08-13 13:28:28Z xhanka00 $");

void diff_buffers(u_char *buf1, u_char *buf2, unsigned int len, unsigned int offset1, unsigned int offset2);

/* TODO move to libcommlbr */
void cl_dump_buffer(FILE *out, u_char *buf, uint32_t len, char *prefix, uint32_t chars_per_line, uint32_t chars_per_word, uint32_t offset);

/**
 * \brief Write value of data_size to position specified by offset in LB_EP memory and
 * 	  to SW mem too which copying LB_EP memory - because of testing   
 *
 * \param dev           device file
 * \param lb_ep         address space specification of lb_ep
 * \param offset       	offset in lb_ep memory 
 * \param value      	value to write 
 * \param mem		allocated memory as a copy of LB_EP memory in SW
 * \param data_size	size of value to write
 *
 */
void
ics_write(cs_device_t *dev, cs_space_t *lb_ep, uint32_t offset, \
						uint32_t *value, uint32_t *mem, uint32_t data_size) {

	int i;
	int words = data_size / 4;

	MSG(CL_VERBOSE_BASIC, "%s : writing %d words into fpga mem", __func__, words);
	for(i = 0; i < words; i++) {
		MSG(CL_VERBOSE_BASIC, "%s : value: 0x%08x, offset: 0x%08x, word: %d", __func__, *(value + i), offset + i*4, i);
		cs_space_write_4(dev, lb_ep, offset + i*4, *(value + i));
	}

	/* probably causes strange kernel error */
/*        cs_space_write_multi_4(dev, lb_ep, offset, words, value);*/

	memcpy(mem + offset, value, data_size);

}


/**
 * \brief Clear whole LB_EP memory
 *
 * \param dev           device file
 * \param lb_ep         address space specification of lb_ep
 * \param lb_ep_mem_size        size of lb_ep memory
 *
 */
void
ics_clear_mem(cs_device_t *dev, cs_space_t *lb_ep, uint32_t lb_ep_mem_size) {

        uint32_t        i;

        for(i=0; i < lb_ep_mem_size; i+=4) {
		cs_space_write_4(dev, lb_ep, i, 0x0);
        }

}


/**
 * \brief Verification whether LB_EP memory correspond with corresponding 
 *	  memory in SW 
 *
 * \param dev          	device file
 * \param lb_ep        	address space specification of lb_ep
 * \param lb_ep_mem_size	size of lb_ep memory
 * \param mem           allocated memory as a copy of LB_EP memory in SW
 *
 * \return	0	OK<BR>
 *		-1	verification failed
 */
int
ics_test_lb_ep_mem(cs_device_t *dev, cs_space_t *lb_ep, \
			 	uint32_t lb_ep_mem_size, u_char *mem, uint32_t mem_offset) {
	int		ret = 0;
	uint32_t	i;
	u_char 		*tmp_fpga_mem = malloc(lb_ep_mem_size * sizeof(u_char));

	if(!tmp_fpga_mem)
		errx(2, "Can't allocate memory");

	/* read FPGA to tmp buffer */
	for(i=0; i < lb_ep_mem_size; i+=4) {
		*(tmp_fpga_mem + i) = cs_space_read_4(dev, lb_ep, mem_offset + i);
	}
	
	MSG(CL_VERBOSE_BASIC, "%s : diffing fpga mem and local copy of fpga mem", __func__);
	if(memcmp(tmp_fpga_mem, mem, lb_ep_mem_size)) {
		/* TODO offsets */
		MSG(CL_VERBOSE_BASIC, "diffing buffer 1 - fpga_mem, buffer 2 - local copy of fpga mem");
		diff_buffers(tmp_fpga_mem, mem, lb_ep_mem_size, 0, 0);
		ret = -1;
	} 

	free(tmp_fpga_mem);
	return ret;
}

int
/*! 
 * \brief Verification if global RAM corresponds with LB_EP memory copy in SW 
 * 
 * \param global 
 * \param lb_ep_mem_size 
 * \param mem 
 * \param mem_offset 
 */
ics_test_lb_ep_mem_global(u_char *global, uint32_t lb_ep_mem_size, u_char *mem, uint32_t mem_offset) {

	int		ret = 0;

	/* check content */
	MSG(CL_VERBOSE_BASIC, "%s : diffing RAM and local copy of FPGA mem", __func__);
	if(memcmp(global, mem + mem_offset, lb_ep_mem_size)) {
		/* TODO offsets */
		MSG(CL_VERBOSE_BASIC, "diffing buffer 1 - RAM, buffer 2 - local copy of fpga mem");
		diff_buffers(global, mem, lb_ep_mem_size, 0, 0);
		ret = -1;
	} 
	return ret;
}


int
rand_index() {
	return rand() % NUM_LB_EP;
}

uint32_t
rand_offset(int index) {
	if(index < BRAM_FROM_INDEX) {
		return 4 * (rand() % (LB_ENDPOINT_WIDTH/4) );
	} else {
		return 4 * (rand() % (LB_ENDPOINT_BRAM_WIDTH/4) );
	}
}

void rand_data(u_char *value, uint32_t val_len) {
	uint32_t i;

	for(i = 0; i < val_len; i = i + 4)
		*(uint32_t *)(value + i) += (uint32_t) rand();
}

/**
 * \brief Return memory size of LB_EP specified by index 
 *
 * \param index         index of LB_EP
 * \return 		memory size of LB_EP
 */
uint32_t
get_lb_ep_mem_size(int index){

                if(index < BRAM_FROM_INDEX) {
                	return LB_ENDPOINT_WIDTH;
                } else {
                	return LB_ENDPOINT_BRAM_WIDTH;
                }

}

/**
 * \brief Do busmaster operation - Global to local read
 *
 * \param dev           device file
 * \param mi32tobm   	address space specification of mi32tobm 
 * \param g_addr    	global address	
 * \param l_addr	local address 
 * \param length	length of data to operate with 	
 *
 */
void
ics_bm_g2lread(cs_device_t *dev, cs_space_t *mi32tobm, uint32_t g_addr, \
					uint32_t l_addr, uint32_t length){

	uint16_t tag = rand() % (1 << (sizeof(uint16_t) * 8));
	MSG(CL_VERBOSE_BASIC, "%s : g2lr component command", __func__);
	MSG(CL_VERBOSE_BASIC, "%s : %08x %08x", __func__, GLOBAL_ADDR_REG, g_addr);
	MSG(CL_VERBOSE_BASIC, "%s : %08x %08x", __func__, LOCAL_ADDR_REG, l_addr);
	MSG(CL_VERBOSE_BASIC, "%s : %08x %08x", __func__, LENGTH_REG, length);
	MSG(CL_VERBOSE_BASIC, "%s : %08x %08x", __func__, TAG_REG, tag);
	MSG(CL_VERBOSE_BASIC, "%s : %08x %08x", __func__, CONTROL_REG, G2L_READ | CMD_START);
	cs_space_write_4(dev, mi32tobm, GLOBAL_ADDR_REG, g_addr);
	cs_space_write_4(dev, mi32tobm, LOCAL_ADDR_REG, l_addr);
	cs_space_write_4(dev, mi32tobm, LENGTH_REG, length);
	cs_space_write_4(dev, mi32tobm, TAG_REG, (uint32_t)tag);
	cs_space_write_4(dev, mi32tobm, CONTROL_REG, G2L_READ | CMD_START);

}

/**
 * \brief Do busmaster operation - Local to global write 
 *
 * \param dev           device file
 * \param mi32tobm      address space specification of mi32tobm
 * \param g_addr        global address
 * \param l_addr        local address
 * \param length        length of data to operate with
 *
 */
void
ics_bm_l2gwrite(cs_device_t *dev, cs_space_t *mi32tobm, uint32_t g_addr, \
                                        uint32_t l_addr, uint32_t length){
	uint16_t tag = rand() % (1 << (sizeof(uint16_t) * 8));

	MSG(CL_VERBOSE_BASIC, "%s : l2gw component command", __func__);
	MSG(CL_VERBOSE_BASIC, "%s : %08x %08x", __func__, GLOBAL_ADDR_REG, g_addr);
	MSG(CL_VERBOSE_BASIC, "%s : %08x %08x", __func__, LOCAL_ADDR_REG, l_addr);
	MSG(CL_VERBOSE_BASIC, "%s : %08x %08x", __func__, LENGTH_REG, length);
	MSG(CL_VERBOSE_BASIC, "%s : %08x %08x", __func__, TAG_REG, tag);
	MSG(CL_VERBOSE_BASIC, "%s : %08x %08x", __func__, CONTROL_REG, L2G_WRITE | CMD_START);
        cs_space_write_4(dev, mi32tobm, GLOBAL_ADDR_REG, g_addr);
        cs_space_write_4(dev, mi32tobm, LOCAL_ADDR_REG, l_addr);
        cs_space_write_4(dev, mi32tobm, LENGTH_REG, length);
	cs_space_write_4(dev, mi32tobm, TAG_REG, (uint32_t)tag);
        cs_space_write_4(dev, mi32tobm, CONTROL_REG, L2G_WRITE | CMD_START);
}

/**
 * \brief Do busmaster operation - Local to local read
 *
 * \param dev           device file
 * \param mi32tobm      address space specification of mi32tobm
 * \param g_addr        global address
 * \param l_addr        local address
 * \param length        length of data to operate with
 *
 */
void
ics_bm_l2lread(cs_device_t *dev, cs_space_t *mi32tobm, uint32_t g_addr, \
                                        uint32_t l_addr, uint32_t length){

        cs_space_write_4(dev, mi32tobm, GLOBAL_ADDR_REG, g_addr);
        cs_space_write_4(dev, mi32tobm, LOCAL_ADDR_REG, l_addr);
        cs_space_write_4(dev, mi32tobm, LENGTH_REG, length);
        cs_space_write_4(dev, mi32tobm, CONTROL_REG, L2L_READ | CMD_START);

}

/**
 * \brief Do busmaster operation - Local to local write 
 *
 * \param dev           device file
 * \param mi32tobm      address space specification of mi32tobm
 * \param g_addr        global address
 * \param l_addr        local address
 * \param length        length of data to operate with
 *
 */
void
ics_bm_l2lwrite(cs_device_t *dev, cs_space_t *mi32tobm, uint32_t g_addr, \
                                        uint32_t l_addr, uint32_t length){

        cs_space_write_4(dev, mi32tobm, GLOBAL_ADDR_REG, g_addr);
        cs_space_write_4(dev, mi32tobm, LOCAL_ADDR_REG, l_addr);
        cs_space_write_4(dev, mi32tobm, LENGTH_REG, length);
        cs_space_write_4(dev, mi32tobm, CONTROL_REG, L2L_WRITE | CMD_START);
}

/**
 * \brief Did busmaster operation end and was succesfull??
 *
 * \param dev           device file
 * \param mi32tobm      address space specification of mi32tobm
 *
 * \return 	0	not ended or unsuccesfully<BR>
 *		1	ended succesfully	
 */
int
ics_is_bm_end(cs_device_t *dev, cs_space_t *mi32tobm){

	uint32_t	tmp;

	tmp = cs_space_read_4(dev, mi32tobm, CONTROL_REG);
	 printf("%08X\n", tmp); 

	return ( !(cs_space_read_4(dev, mi32tobm, CONTROL_REG) & 1));
}

/**
 * \brief Return physical address to PCI memory 
 *
 * \return	physical address<BR>
 */
uint32_t
get_phy_addr(void){

	int 		fd;
	uint32_t	addr;

	
	fd = open("/dev/space", 0);
	if(fd < 0) {
		fprintf(stderr, "Unable to open device\n");
		return 0;
	}

	addr = ioctl(fd, SPACE_IOC_GETPHYSADDR, 0);
	/* printf("%X\n", addr); */

	close(fd);

	return addr;
}


/**
 * \brief Write data from buffer of size specified by length to fyzical address
 *
 * \param buffer	buffer with data 
 * \param length        length of data in buffer to operate with
 *
 * \return	0	OK<BR>
 *		-1	error
 */
int
write_to_phy_addr(char *buffer, uint32_t length){

        t_transaction   t;
        int             fd, r;
        uint32_t        phy_addr;
	uint32_t i = 0;


        fd = open("/dev/space", 0);
        if(fd < 0) {
                fprintf(stderr, "Unable to open device\n");
                return -1;
        }

        phy_addr = ioctl(fd, SPACE_IOC_GETPHYSADDR, 0);
        /* printf("%X\n", phy_addr); */
	
	/* writing to memory */
	t.pos = 0;
	t.data = buffer;
	t.len = length;

	r = ioctl(fd, SPACE_IOC_WRITE, &t);
	if(r < 0) {
		fprintf(stderr, "Write error to phy addr: %08X\n", phy_addr);
		close(fd);
		return -1;
	}

	MSG(CL_VERBOSE_BASIC, "%s : written to RAM", __func__);
	for(i = 0; i < length; i++)
		MSG_NONL(CL_VERBOSE_BASIC, "%02x ", *(buffer + i));

	MSG_NONL(CL_VERBOSE_BASIC, "\n");

	close(fd);	

	return 0;
}

/**
 * \brief Read data of size specified by length from physical address and write
 *	  it to buffer
 *
 * \param buffer        buffer for data from physical address space
 * \param length        length of data in buffer to operate with
 *
 * \return      0       OK<BR>
 *              -1      error
 */
int
read_from_phy_addr(char *buffer, uint32_t length){

        t_transaction   t;
        int             fd, r;
        uint32_t        phy_addr, i;


        fd = open("/dev/space", 0);
        if(fd < 0) {
                fprintf(stderr, "Unable to open device\n");
                return -1;
        }

        phy_addr = ioctl(fd, SPACE_IOC_GETPHYSADDR, 0);
        /* printf("%X\n", phy_addr); */


        /* writing to memory */
        t.pos = 0;
        t.data = buffer;
        t.len = length;

        r = ioctl(fd, SPACE_IOC_READ, &t);
        if(r < 0) {
                fprintf(stderr, "Read error from phy addr: %08X\n", phy_addr);
		close(fd);
                return -1;
        }

	MSG(CL_VERBOSE_BASIC, "%s : read from RAM", __func__);
	for(i = 0; i < length; i++)
		MSG_NONL(CL_VERBOSE_BASIC, "%02x ", *(buffer + i));

	MSG_NONL(CL_VERBOSE_BASIC, "\n");

	close(fd);
	return 0;
}


void diff_buffers(u_char *buf1, u_char *buf2, unsigned int len, unsigned int offset1, unsigned int offset2) {
	int sequence;
	uint32_t i;

	/* TODO offsets */
	cl_dump_buffer(stdout, buf1, len, "buf1", 64, 8, offset1);
	cl_dump_buffer(stdout, buf2, len, "buf2", 64, 8, offset2);


	printf("Verification failed - wrong bytes\n");
	sequence = 0;

	for(i = 0; i < len; i++) {
		if(*(buf1 + i) != *(buf2 + i)) {
			if(sequence < 1)
				printf(", 0x%08x", i);
			sequence++;
		} else {
			if(sequence > 1)
				printf("-0x%08x", i - 1);

			sequence = 0;
		}
	}
	if(sequence > 1)
		printf("-0x%08x", i);

	printf("\n\n\n");
	fflush(stdout);
}

void cl_dump_buffer(FILE *out, u_char *buf, uint32_t len, char *prefix, uint32_t chars_per_line, uint32_t chars_per_word, uint32_t offset) {

	uint32_t i;

	for(i = 0; i < len; i++) {
		if(!(i % chars_per_line))
			fprintf(out, "\n%s  : %04x :  ", prefix, i + offset);
		else if(!(i % chars_per_word))
			fprintf(out, "   ");
		fprintf(out, "%02x ", buf[i]);
	}
	fprintf(out, "\n");
}
