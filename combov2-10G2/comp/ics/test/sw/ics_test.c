/*
 * ics_test.c:
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
 * $Id: ics_test.c 4749 2008-08-13 13:36:50Z xhanka00 $
 *
 */

#include <err.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>


#include <combo.h>
#include <commlbr.h>

#include "ics.h"


/* CVS ID tag for ident(1) program */
__RCSID("$Id: ics_test.c 4749 2008-08-13 13:36:50Z xhanka00 $");

/**<\def version of program */
#define VERSION "$Id: ics_test.c 4749 2008-08-13 13:36:50Z xhanka00 $"


/* Available commands */
#define NUM_CMD        	3

#define CMD_WRITE_IN	1 
#define CMD_G2LR       	2	
#define CMD_G2LR_DURING 3 
#define CMD_G2LR_BLOCK	4
#define CMD_L2GW	5	
#define CMD_L2GW_DURING	6	
#define CMD_L2LW	7
#define CMD_L2LR	8

#define LOOPS_MAX 	1000000
#define MAX_OFFSET	LB_ENDPOINT_WIDTH - 4
#define MAX_DATA_SIZE	4096

/**
 * \struct t_choice
 *
 * structre t_choice contains name of command, its id number and string with
 * help for the command
 */
struct t_choice{
    char *name;
    int  id;
    char *help;
};

/**
 * array contains structure t_choice for each command of the program
 */
struct t_choice c_commands[NUM_CMD] = {
    {"write",	CMD_WRITE_IN,	"many write-in operations"},
    {"g2lr", 	CMD_G2LR,   	"BM operations G2L READ"},
    {"l2gw",	CMD_L2GW,       "BM operations L2G WRITE"},
};


/**
 * \brief Decoding string from array of structures t_choice
 *
 * \param str           pointer to structures t_choice with commands of program
 * \param name          choosing string command
 * \param num           number of commands in array
 * \return      >=0     Command ID <BR>
 *              -1      Command not found
 */
int
decode_choice(struct t_choice *strs, const char *name, int num)
{
    int i;
    for(i=0; i<num;i++){
        if(strcmp(strs[i].name, name)==0)
            return strs[i].id;
    }
    return -1;
}


/* \brief acceptable command line arguments */
#define ARGUMENTS       "c:d:D:hf:l:o:s:"

/**
 * \brief Display usage of program
 *
 * \param strs_cmd      pointer to structures t_choice with commands of program
 */
void
usage(struct t_choice *strs_cmd) {

	int	i;

        printf("Usage: %s [-c cmd] [-d device] [-D level] [-f file] [-l count] [-o offset] [-s size]  [-h] \n", getprogname());
        printf("-d s            path to device file to use\n");
        printf("-D level        debug level\n");
	printf("-f file         file with data pattern\n");
        printf("-l count        how many times to perform operation\n");
        printf("-o offset       address for operation\n");
	printf("-s size         lenght of data for operation\n");
        printf("-h              show this text\n");
        printf("-c cmd\n");

        for(i=0;i<NUM_CMD;i++) {
                printf("\t%s\t - %s\n", strs_cmd[i].name, strs_cmd[i].help);
	}
}

/**
 * \brief Program main function.
 *
 * \param argc          number of arguments
 * \param *argv[]       array with the arguments
 *
 * \return      0       OK <BR>
 *              -1      error
 */
int
main(int argc, char *argv[]) {

        cs_device_t     *dev;
        char            *file = CS_PATH_DEV(0);
	cs_space_t	*lb_ep[NUM_LB_EP];
	cs_space_t	*mi32tobm;
	uint32_t	*lb_ep_mem[NUM_LB_EP];
	uint32_t	offset = 0;
	uint32_t	value[MAX_DATA_SIZE/4];
	bool		randomize_offset = true, randomize_data = true, randomize_index = true;
	int		c, index, mem_size, size;
	int		cmd = -1;
	char 		buffer[MAX_DATA_SIZE];
	uint32_t	phy_addr;
	uint32_t	lb_ep_base_addr[10];
	uint32_t	data;
        char            *command = NULL;

	long 		ltemp; /*!< getopt */
	uint32_t 	loops = 1, cycle;
	uint32_t 	data_size = 4;
	char 		*data_file = NULL;
	int		ret = 0;
	bool 		test_local, test_global;
	uint32_t	i;

	debug = -1;

	size = LB_ENDPOINT_WIDTH/4;
	for(i=0; i < NUM_LB_EP; i++){
		if(i >= BRAM_FROM_INDEX) {
			size = LB_ENDPOINT_BRAM_WIDTH/4;
		}

		lb_ep_mem[i] = (uint32_t *) malloc(sizeof(uint32_t) * size);
		if(lb_ep_mem[i] == 0){
			errx(1, "cannot allocate memory");
		}
		memset(lb_ep_mem[i], 0, sizeof(uint32_t) * size);
	}

        while ((c = getopt(argc, argv, ARGUMENTS)) != -1) {
                switch (c) {
                case 'd':       /* Set device file path */
                        file = optarg;
                        break;

                case 'c':       /* Decode command */
                        command = optarg;
                        break;
#ifdef DEBUG
		case 'D':	/* debug level */
                        if( (cl_strtol(optarg, &ltemp)) || (ltemp > 2) || (ltemp < 0) ) {
				errx(1, "wrong value of -D attribute");
                        }
			debug = ltemp;
			break;
#endif
                case 'f':       
			randomize_data = false;
                        data_file = optarg;
                        break;
               	case 'h':	/* program usage */
                        usage(c_commands);
                        return 0;

               	case 'l':
                        if( (cl_strtol(optarg,  &ltemp)) || (ltemp > LOOPS_MAX) || (ltemp < 1) ) {
				errx(1, "wrong value of -l attribute. Minimum is 1, maximum %d", LOOPS_MAX);
                        }
			loops = ltemp;
			break;
               	case 's':
                        if( (cl_strtol(optarg,  &ltemp)) || (ltemp > MAX_DATA_SIZE) || (ltemp < 1)) {
				errx(1, "wrong value of -s attribute. Minimum is 1, maximum %d", MAX_DATA_SIZE);
                        }
			data_size = ltemp;
			if(data_size % 4)
				errx(1, "Size not aligned to 4");
			break;
               	case 'o':
                        if( (cl_strtol(optarg,  &ltemp)) || (ltemp > MAX_OFFSET)) {
				errx(1, "wrong value of -o attribute. Minimum is 0, maximum %d", MAX_OFFSET);
                        }
			randomize_offset = false;
			offset = ltemp;
			if(offset % 4)
				warnx("offset not aligned to 4");
			break;
                default:
                        errx(1, "unknown argument -%c", optopt);
                }
        }
        argc -= optind;
        argv += optind;

        if (argc != 0) {
                errx(1, "stray arguments");
	}

	/* load data pattern */
	if(!cl_file_read_hex((char *)value, data_file, data_size))
		errx(1, "Can't load data from file");

	/* attach device */
	if (cs_attach_noex(&dev, file) != 0){
       		cs_detach(&dev);
             	errx(1, "cs_attach_noex failed");
	}

        /* ------------ Component space mapping ------------ */

                                /* LB_ENDPOINT */
	MSG(CL_VERBOSE_BASIC, "Mapping memory 0 at %08x", LB_ENDPOINT_0_BASE);
	if (cs_space_map(dev, &lb_ep[0], CS_SPACE_FPGA, LB_ENDPOINT_WIDTH, \
                        LB_ENDPOINT_0_BASE, 0) != 0) {
                errx(1, "cs_space_map failed to map LB_ENDPOINT_0");
	}
	lb_ep_base_addr[0] = LB_ENDPOINT_0_BASE;

#ifndef GICS
                                /* LB_ENDPOINT */
        if (cs_space_map(dev, &lb_ep[1], CS_SPACE_FPGA, LB_ENDPOINT_WIDTH, \
                        LB_ENDPOINT_1_BASE, 0) != 0) {
                errx(1, "cs_space_map failed to map LB_ENDPOINT_1");
        }
 	lb_ep_base_addr[1] = LB_ENDPOINT_1_BASE;

                                /* LB_ENDPOINT */
        if (cs_space_map(dev, &lb_ep[2], CS_SPACE_FPGA, LB_ENDPOINT_WIDTH, \
                        LB_ENDPOINT_2_BASE, 0) != 0) {
                errx(1, "cs_space_map failed to map LB_ENDPOINT_2");
        }
 	lb_ep_base_addr[2] = LB_ENDPOINT_2_BASE;

                                /* LB_ENDPOINT */
        if (cs_space_map(dev, &lb_ep[3], CS_SPACE_FPGA, LB_ENDPOINT_WIDTH, \
                        LB_ENDPOINT_3_BASE, 0) != 0) {
                errx(1, "cs_space_map failed to map LB_ENDPOINT_3");
        }
	lb_ep_base_addr[3] = LB_ENDPOINT_3_BASE;

                                /* LB_ENDPOINT */
        if (cs_space_map(dev, &lb_ep[4], CS_SPACE_FPGA, LB_ENDPOINT_WIDTH, \
                        LB_ENDPOINT_4_BASE, 0) != 0) {
                errx(1, "cs_space_map failed to map LB_ENDPOINT_4");
        }
	lb_ep_base_addr[4] = LB_ENDPOINT_4_BASE;

#endif

				/* MI32 TO BM */
	MSG(CL_VERBOSE_BASIC, "Mapping MI32 TO BM at %08x", LB_EP_MI32TOBM_BASE);
        if (cs_space_map(dev, &mi32tobm, CS_SPACE_FPGA, LB_EP_MI32TOBM_WIDTH, \
                        LB_EP_MI32TOBM_BASE, 0) != 0) {
                errx(1, "cs_space_map failed to map MI32TOBM");
        }


#ifndef GICS
                                /* LB_ENDPOINT */
        if (cs_space_map(dev, &lb_ep[5], CS_SPACE_FPGA, LB_ENDPOINT_BRAM_WIDTH,\
                        LB_ENDPOINT_5_BASE, 0) != 0) {
                errx(1, "cs_space_map failed to map LB_ENDPOINT_5");
        }
        lb_ep_base_addr[5] = LB_ENDPOINT_5_BASE;

                                /* LB_ENDPOINT */
        if (cs_space_map(dev, &lb_ep[6], CS_SPACE_FPGA, LB_ENDPOINT_BRAM_WIDTH,\
                        LB_ENDPOINT_6_BASE, 0) != 0) {
                errx(1, "cs_space_map failed to map LB_ENDPOINT_6");
        }
 	lb_ep_base_addr[6] = LB_ENDPOINT_6_BASE;

                                /* LB_ENDPOINT */
        if (cs_space_map(dev, &lb_ep[7], CS_SPACE_FPGA, LB_ENDPOINT_BRAM_WIDTH,\
                        LB_ENDPOINT_7_BASE, 0) != 0) {
                errx(1, "cs_space_map failed to map LB_ENDPOINT_7");
        }
	lb_ep_base_addr[7] = LB_ENDPOINT_7_BASE;

                                /* LB_ENDPOINT_BM */
	if (cs_space_map(dev, &lb_ep[8], CS_SPACE_FPGA, LB_ENDPOINT_BRAM_WIDTH,\
                        LB_ENDPOINT_BM_BASE, 0) != 0) {
                errx(1, "cs_space_map failed to map LB_ENDPOINT_BM");
        }
 	lb_ep_base_addr[8] = LB_ENDPOINT_BM_BASE;

#endif


        /* Clear all memory of all LB_EPs - zeros like in SW buffers */
        for(i=0; i<NUM_LB_EP; i++) {
		mem_size = get_lb_ep_mem_size(i);

		ics_clear_mem(dev,lb_ep[i], mem_size);
        }

	srand((unsigned int) clock());


        if (command != NULL){
                if( (cmd = decode_choice(c_commands, command, NUM_CMD)) == -1){
			MSG(CL_VERBOSE_BASIC, "Unknown command %s", command);
                        return -1;
                }
        }

	if(cmd == -1){
		usage(c_commands);
		return 0;	
	}

	for(cycle=0; cycle<loops; cycle++) {
		test_local = false;
		test_global = false;

		/* get needed data for operations */
		if(randomize_index)
			index = rand_index();

		if(randomize_offset)
			offset = rand_offset(index);

		if(randomize_data)
			rand_data((u_char *)value, data_size);

		MSG(CL_VERBOSE_BASIC, "index     %d", index);
		MSG(CL_VERBOSE_BASIC, "offset    0x%08x", offset);
		MSG(CL_VERBOSE_BASIC, "data_size 0x%08x", data_size);
		MSG(CL_VERBOSE_BASIC, "loops     %d", loops);
		MSG(CL_VERBOSE_BASIC, "data");

		for(i = 0; i < data_size; i++) {
			MSG_NONL(CL_VERBOSE_BASIC, "%02x ", *((u_char *)value + i));
		}
		MSG_NONL(CL_VERBOSE_BASIC, "\n");

		switch(cmd){
		case CMD_WRITE_IN:
			/* test write-in to LB_EPs */
			MSG(CL_VERBOSE_BASIC, "WRITE_IN");

			ics_write(dev, lb_ep[index], offset, value, \
					lb_ep_mem[index], data_size);

			test_local = true;
			break;
		case CMD_G2LR:
			/*************************************************************/
			/* BM - G2L READ - TEST */

			write_to_phy_addr((char *)value, data_size);

			/* written data to physical address - verification */
			read_from_phy_addr(buffer, data_size);

			/* store data from phy. mem to SW copy of LB_EP mems */
			memcpy(lb_ep_mem[index], buffer, data_size);

			/* get physical address - here was just written */
			if( (phy_addr = get_phy_addr()) == 0) {
				printf("Unable to get physical address to memory\n");
				exit(-1);
			}

		       /* BM operation - from physical address to unit */
			ics_bm_g2lread(dev, mi32tobm, phy_addr, \
						lb_ep_base_addr[index]+(offset), data_size);

			/* wait for operation to finish */
			usleep(1000);

			test_local = true;
			break;

		case CMD_L2GW:
			/************************************************************/
			/* BM - L2G WRITE - TEST*/
			if( (phy_addr = get_phy_addr()) == 0) {
				printf("Unable to get physical address to memory\n");
				exit(-1);
			}

			ics_write(dev, lb_ep[index], offset, value, \
					lb_ep_mem[index], data_size);

			ics_bm_l2gwrite(dev, mi32tobm, phy_addr, offset, data_size);

			/* wait till BM operation end */
			usleep(100);

			read_from_phy_addr(buffer, data_size);

			test_global = true;
			break;
		}

		if(test_local) { /* diff FPGA and lb_ep_mem */
			ret = ics_test_lb_ep_mem(dev, lb_ep[index], data_size, (u_char *)lb_ep_mem[index], offset);
		} else if(test_global) { /* global stored in buffer - diff buffer and lb_ep_mem */
			ret = ics_test_lb_ep_mem_global(buffer, data_size, (u_char *)lb_ep_mem[index], offset);
		}

		/* print results */
		if(!ret) {
			printf("memory verification for lb_ep %d was " \
				"successfull\n", index);
		} else {
			printf("memory verification for lb_ep %d failed!!\n", \
				index);
		}

	} /* FOR */

	cs_detach(&dev);

	return 0;
}


