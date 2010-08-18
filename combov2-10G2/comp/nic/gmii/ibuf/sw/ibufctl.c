/**
 * \file 	ibufctl.c
 * \brief 	Tool for controlling ibuf_gmii
 * \author 	Andrej Hank <xhanka00@liberouter.org>
 * \date 	2006
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
 * $Id: ibufctl.c 14 2007-07-31 06:44:05Z kosek $
 *
 */

#include <err.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <compat.h>
#include <combosix.h>

#include "ibuf_gmii.h"

__RCSID ("$Id: ibufctl.c 14 2007-07-31 06:44:05Z kosek $");

/**
 * \def 	VERSION
 * \brief	File version
 */
#define VERSION "$Id: ibufctl.c 14 2007-07-31 06:44:05Z kosek $"

/*
 * \var 	verbose
 * \bfief	Control verbosity
 */
int verbose;

/* \brief acceptable command line arguments */
#define ARGUMENTS	"b:d:i:m:ehvV"

/**
 * \brief 	Display usage of program
 */
void
usage ()
{
        printf ("Usage: %s [-ehvV] [-b base_addr] [-d path] [-i unit] [-m mask]\n", getprogname ());
	printf ("-b base_addr   Unit address (hex)\n");
        printf ("-d path        Path to device file to use\n");
        printf ("-i unit        Unit number 0|1|2|3 (default 0)\n");
        printf ("-m mask        Set error mask 0|1|2|3\n");
        printf ("-e             Enable/disable unit\n");
        printf ("-h             Show this text\n");
        printf ("-v             Verbose mode\n");
        printf ("-V             Show version\n");
}

/**
 * \brief 		Program main function.
 *
 * \param argc          number of arguments
 * \param *argv[]       array with the arguments
 *
 * \return      0       OK 
 *             -1       error
 */
int
main(int argc, char *argv[])
{

    	int 		c;
	cs_device_t 	*dev;
	cs_space_t 	*ibuf_gmii;
	char 		*file = CS_PATH_DEV(0);
    	int 		ifc = 0;
	ibuf_t		data;
	int		enable = 0;
	int		mask = -1;
	/* current unit address */
    	u_int32_t 	ibuf_base_addr;
	/* component address in design */
	u_int32_t	base_address = IBUF_GMII_BASE;

	/* Process command line arguments **************/
	while ((c = getopt(argc, argv, ARGUMENTS)) != -1) {
		switch (c) {
		case 'b':
			if ((sscanf (optarg, "%x", &base_address) == 0))
				errx (1, "Wrong base address.");
			break;
		case 'd':
			file = optarg;
			break;
		case 'i':
			ifc = atoi(optarg);
			if (ifc < 0 || ifc > 3)
				errx(1, "Wrong unit number %s", optarg);
			break;
		case 'm':
			if ((sscanf (optarg, "%d",&mask) == 0))
				errx (1, "Wrong mask.");
			if (mask < 0 || mask > 3)
				errx (1, "Wrong mask.");
			break;
		case 'e':
			enable = 1;
			break;
		case 'h':
			usage();
			return 0;
                case 'v':
                        verbose = 1;
                        break;
                case 'V':
                        printf ("%s\n", VERSION);
                        return 0;
		default:
			errx(1, "unknown argument -%c", optopt);
		}
	}
	argc -= optind;
	argv += optind;

	if (argc != 0)
		errx(1, "stray arguments");

	/* attach device & map address spaces */
	if (cs_attach_noex(&dev, file) != 0)
		err(1, "cs_attach_noex failed");

	switch(ifc){
		case 0:
			ibuf_base_addr = IBUF0_BASE_ADDR;
			break;
		case 1:
			ibuf_base_addr = IBUF1_BASE_ADDR;
			break;
		case 2:
			ibuf_base_addr = IBUF2_BASE_ADDR;
			break;
		case 3:
			ibuf_base_addr = IBUF3_BASE_ADDR;
			break;
		default:
			ibuf_base_addr = IBUF0_BASE_ADDR;
	}

        /* ------------ Component space mapping ------------ */
	VERBOSE ("mapping @ %08x\n", base_address);
        if (cs_space_map (dev, &ibuf_gmii, CS_SPACE_FPGA, CS_MAP_ALL,
                          base_address, 0) != 0)
                errx (1, "cs_space_map failed to map ibuf_gmii");

	/* ------------------------------------------------- */
	if (enable){
		cs_enable_ibuf(dev, ibuf_gmii, ibuf_base_addr);
		return 0;
	}

	if(mask != -1){
		VERBOSE ("Mask: %d\n", mask);
		cs_space_write_4(dev, ibuf_gmii, ibuf_base_addr + IBUF_ERRMASK, mask); 
		return 0;
	}
		
	data = cs_read_ibuf(dev, ibuf_gmii, ibuf_base_addr);
	cs_print_ibuf(data);

	return 0;
}
