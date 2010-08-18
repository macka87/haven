/*
 * ics.h: Specify function prototypes for ICS tests
 * Copyright (C) 2007 CESNET
 * Author: Petr Springl  <xsprin01@liberouter.org>
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
 * $Id: ics.h 4748 2008-08-13 13:28:28Z xhanka00 $
 *
 */

#ifndef __ICS_H__
#define __ICS_H__

#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdlib.h>
#include <netinet/in.h>

#include <combo.h>
#include <commlbr.h>

#include "space.h"

#include "icsreg.h"


void
ics_write(cs_device_t *dev, cs_space_t *lb_ep, uint32_t offset, \
						uint32_t *value, uint32_t *mem, uint32_t data_size);

void
ics_clear_mem(cs_device_t *dev, cs_space_t *lb_ep, uint32_t lb_ep_mem_size); 


int
ics_test_lb_ep_mem(cs_device_t *dev, cs_space_t *lb_ep, \
			 	uint32_t lb_ep_mem_size, u_char *mem, uint32_t mem_offset);

int
ics_test_lb_ep_mem_global(u_char *global, uint32_t lb_ep_mem_size, \
	u_char *mem, uint32_t mem_offset); 

uint32_t
get_lb_ep_mem_size(int index);


void
ics_bm_g2lread(cs_device_t *dev, cs_space_t *mi32tobm, uint32_t g_addr, \
                                        uint32_t l_addr, uint32_t length);


void
ics_bm_l2gwrite(cs_device_t *dev, cs_space_t *mi32tobm, uint32_t g_addr, \
                                        uint32_t l_addr, uint32_t length);

void
ics_bm_l2lread(cs_device_t *dev, cs_space_t *mi32tobm, uint32_t g_addr, \
                                        uint32_t l_addr, uint32_t length);


void
ics_bm_l2lwrite(cs_device_t *dev, cs_space_t *mi32tobm, uint32_t g_addr, \
                                        uint32_t l_addr, uint32_t length);

int
ics_is_bm_end(cs_device_t *dev, cs_space_t *mi32tobm);

uint32_t
get_phy_addr(void);

int
write_to_phy_addr(char *buffer, uint32_t length);

int
read_from_phy_addr(char *buffer, uint32_t length);

int
rand_index();

uint32_t
rand_offset(int index);

void rand_data(u_char *value, uint32_t val_len);

#endif

