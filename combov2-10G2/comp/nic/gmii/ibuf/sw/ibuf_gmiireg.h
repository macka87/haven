/**
 * \file 	ibuf_gmiireg.h
 * \brief 	Adress space for ibuf_gmii
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
 * $Id: ibuf_gmiireg.h 14 2007-07-31 06:44:05Z kosek $
 *
 */

#ifndef __IBUF_GMII_REG__
#define __IBUF_GMII_REG__

/* if not defined in global design - liberouter.h, define own base and width of
 * component */ 
#ifndef IBUF_GMII_BASE
	#define IBUF_GMII_BASE		0x0//TODO	
	#define IBUF_GMII_WIDTH		0x1000
#endif

/* single unit */
#define IBUF_CNT_PACKETS		0x0000
#define IBUF_CNT_RECV			0x0004
#define IBUF_CNT_RECVERR		0x0008
#define IBUF_EN				0x0020
#define IBUF_ERRMASK			0x0024
#define IBUF_STATUS			0x0028
#define IBUF_CTRL			0x002C

/* units */
#define IBUF0_BASE_ADDR			0x0000		
#define IBUF1_BASE_ADDR			0x0100
#define IBUF2_BASE_ADDR			0x0200
#define IBUF3_BASE_ADDR			0x0300

#endif
