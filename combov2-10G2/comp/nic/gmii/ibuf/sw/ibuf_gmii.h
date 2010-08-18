/**
 * \file 	ibuf_gmii.h
 * \brief 	Function prototypes for controlling ibuf_gmii
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
 * $Id: ibuf_gmii.h 14 2007-07-31 06:44:05Z kosek $
 *
 */

#ifndef __IBUF_GMII_H__
#define __IBUF_GMII_H__

#include <err.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <compat.h>
#include <combosix.h>

#include "ibuf_gmiireg.h"

/**
 * \def		IBUFCMD_STROBE_COUNTERS
 * \bfief	Constant for strobe counters command
 */
#define IBUFCMD_STROBE_COUNTERS		0x01

/*
 * Control verbosity - must be variable verbose in main().
 */
extern int verbose;

#ifndef VERBOSE
#define VERBOSE(format, args...)    if (verbose) printf (format,##args)
#endif

/**
 *\struct 	Ibuf data structure 
 */
typedef struct {
	uint32_t	cnt_packets;	/* CNT packets */
	uint32_t	cnt_recv;	/* CNT packets */
	uint32_t	cnt_error;	/* CNT errors */
	uint32_t	reg_en;		/* register enable */
	uint32_t	err_mask;	/* mask */
} ibuf_t;

/*
 *  Read IBUF counters
 */
ibuf_t cs_read_ibuf(cs_device_t *dev, cs_space_t *space, u_int32_t addr);

/*
 * Print IBUF counters
 */
void cs_print_ibuf(ibuf_t data);

/*
 * Enable/disable ibuf
 */
void
cs_enable_ibuf (cs_device_t *dev, cs_space_t *space, u_int32_t addr);

#endif
