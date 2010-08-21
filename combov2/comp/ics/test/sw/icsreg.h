/*
 * icsreg.h:
 * Copyright (C) 2007 CESNET
 * Author: Petr  Springl <xsprin01@liberouter.org>
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
 * $Id: icsreg.h 4748 2008-08-13 13:28:28Z xhanka00 $
 *
 */

#ifndef __ICSREG__
#define __ICSREG__


#ifdef GICS /* GICS - new version of ICS (with only one memory) */
	#define LB_ENDPOINT_WIDTH       0x00004000
	#define LB_ENDPOINT_0_BASE      0x00100000
#else
	#define LB_ENDPOINT_WIDTH       0x0100
	#define LB_ENDPOINT_0_BASE      0x00040000
#endif

#define LB_ENDPOINT_1_BASE      0x00080000
#define LB_ENDPOINT_2_BASE      0x000C0000
#define LB_ENDPOINT_3_BASE      0x00100000
#define LB_ENDPOINT_4_BASE      0x00140000


#ifdef GICS
	#define LB_EP_MI32TOBM_BASE	0x00000000
#else
	#define LB_EP_MI32TOBM_BASE	0x00180000
#endif

#define LB_EP_MI32TOBM_WIDTH	0x100

#define LB_ENDPOINT_BRAM_WIDTH	0x0400

#define LB_ENDPOINT_5_BASE	0x00200000
#define LB_ENDPOINT_6_BASE      0x00400000
#define LB_ENDPOINT_7_BASE      0x00600000
#define LB_ENDPOINT_BM_BASE     0x00800000

#define BM_INDEX		8
#define BRAM_FROM_INDEX         5

#ifdef GICS
	#define NUM_LB_EP               1
#else
	#define NUM_LB_EP               9
#endif


/* Address space - MI32toBM */
#define GLOBAL_ADDR_REG		0x0000
#define LOCAL_ADDR_REG		0x0008
#define LENGTH_REG		0x000C
#define	TAG_REG			0x0000
#define CONTROL_REG		0x0014

/* BM transaction type */
#define G2L_READ		0x00
#define	L2G_WRITE		0x02
#define L2L_READ		0x04
#define L2L_WRITE		0x06
#define CMD_START		0x01


#endif
