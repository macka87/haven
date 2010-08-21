/**
 * \file 	ibuf_gmii.c
 * \brief 	Functions for controlling ibuf_gmii
 * \author 	Andrej Hank <xhanka00@liberouter.org>
 * \date 	2006
 *
 * Copyright (C) 2006 CESNET
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
 * $Id: ibuf_gmii.c 14 2007-07-31 06:44:05Z kosek $
 *
 */

#include <err.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <time.h>

#include <compat.h>
#include <combosix.h>

#include "ibuf_gmii.h"

__RCSID ("$Id: ibuf_gmii.c 14 2007-07-31 06:44:05Z kosek $");

/**
 *\brief 	Read IBUF counters
 *\param dev	Device
 *\param space	Space
 *\param addr	Single unit address
 *\return	Read data in ibuf_t structure
 */
ibuf_t
cs_read_ibuf (cs_device_t *dev, cs_space_t *space, u_int32_t addr)
{
	ibuf_t	data;

	cs_space_write_4(dev, space, addr + IBUF_CTRL, IBUFCMD_STROBE_COUNTERS);
	
	/* Read counters and registers */
	data.cnt_packets = cs_space_read_4(dev, space, addr + IBUF_CNT_PACKETS);
	data.cnt_recv    = cs_space_read_4(dev, space, addr + IBUF_CNT_RECV);
	data.cnt_error   = cs_space_read_4(dev, space, addr + IBUF_CNT_RECVERR);
	data.reg_en      = cs_space_read_4(dev, space, addr + IBUF_EN);
	data.err_mask    = cs_space_read_4(dev, space, addr + IBUF_ERRMASK);
	
	return data;
}

/**
 *\brief 	Enable or disable ibuf unit
 *\param dev	Device
 *\param space	Space
 *\param addr	Single unit address
 */
void
cs_enable_ibuf (cs_device_t *dev, cs_space_t *space, u_int32_t addr)
{
	u_int32_t	value;
	value = cs_space_read_4(dev, space, addr + IBUF_EN);
	/* disable */
	if(value & 1)
		cs_space_write_4(dev, space, addr + IBUF_EN, 0);
	/* enable */
	else
		cs_space_write_4(dev, space, addr + IBUF_EN, 1);
}
/**
 *\brief	Print IBUF counters
 *\param data	Data to print in ibuf_t structure
 */
void
cs_print_ibuf (ibuf_t data)
{
	printf("IBUF GMII Status -------------------------------\n");

	if (data.reg_en == 1)
		printf("Interface Enabled\n");
	else
		printf("Interface Disabled\n");
	
	printf("Packets         : %d \n", data.cnt_packets);
	printf("Received        : %d \n", data.cnt_recv);
	printf("Err packets     : %d \n", data.cnt_error);
	printf("Err mask        : %d \n", data.err_mask & 0x00000003);
}

