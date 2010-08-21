//
// crctab.c: The CRC Table Generator
// Copyright (C) 2005 CESNET
// Author(s): Bidlo Michal <bidlom@fit.vutbr.cz>
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
// 3. Neither the name of the Company nor the names of its contributors
//    may be used to endorse or promote products derived from this
//    software without specific prior written permission.
//
// This software is provided ``as is'', and any express or implied
// warranties, including, but not limited to, the implied warranties of
// merchantability and fitness for a particular purpose are disclaimed.
// In no event shall the company or contributors be liable for any
// direct, indirect, incidental, special, exemplary, or consequential
// damages (including, but not limited to, procurement of substitute
// goods or services; loss of use, data, or profits; or business
// interruption) however caused and on any theory of liability, whether
// in contract, strict liability, or tort (including negligence or
// otherwise) arising in any way out of the use of this software, even
// if advised of the possibility of such damage.
//
// $Id: crctab.c 66 2007-08-03 10:06:14Z solanka $
//
// TODO:
//
//

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>
#include <string.h>

typedef unsigned long long int UINT64;

// the 64-bit CRC generator polynomial: 0x1006003C000F0D50B
const UINT64 gp64 = 0x006003C000F0D50BLL;
// the 32-bit CRC generator polynomial: 0x104C11DB7
const UINT64 gp32 = 0x04C11DB7LL;
// the 16-bit CRC generator polynomial: 0x18005
const UINT64 gp16 = 0x8005LL;

typedef unsigned char BYTE;
typedef enum { I, D } T_PART;
typedef enum { VHDL, CPP } T_FORMAT;
typedef struct
{
	T_PART part;
	BYTE index;
	BYTE stop;
} TERM;

T_FORMAT format = VHDL;
FILE *output = NULL;

/* ------------------------------------------------------------------------
 * write_gp()
 *
 *   poly		- generator polynomial
 *   width		- the number of bits of the CRC intended
 *
 */
void write_gp(UINT64 poly, int width)
{
    const int nibble = 4;
    char poly_str[width / nibble + 1];
    int i;

    poly_str[width / nibble] = '\0';
    for (i = 0; i < width / nibble; i++)
    {
        int lsn = (int) (poly & 0xF);
        poly_str[width / nibble - i - 1] = lsn > 9 ? 'A' + lsn - 10 : '0' + lsn;
        poly >>= nibble;
    }

    fprintf(output, "0x1%s", poly_str);
}

/* ------------------------------------------------------------------------
 * table_generator()
 *
 *   poly		- generator polynomial
 *   width		- the number of bits of the CRC intended
 *   bits		- the number of bits being processed in parallel
 *
 */
void table_generator(UINT64 poly, int width, int bits)
{
	// structures for storing tags for generating CRC equations
	TERM forms[bits][bits];
	TERM form0[bits];
	UINT64 polynomial;
	int i, j, k, l, m;

	if (format == VHDL)
    {
        fprintf(output, "-- %d-bit CRC equations processing %d"
		" bits in parallel (VHDL code)\n", width, bits);
        fprintf(output, "-- Generator polynomial: ");
        write_gp(poly, width);
        fprintf(output, "\n");
    }
	else
    {
        fprintf(output,"/* %d-bit CRC equations processing %d bits in parallel"
		" (C/C++ code) */\n", width, bits);
        fprintf(output, "/* Generator polynomial: ");
        write_gp(poly, width);
        fprintf(output, " */\n");
    }

	// initialize register bits
	for (i = 0; i < width; i++)
	{
		forms[0][i].part = I;
		forms[0][i].index = (BYTE) i;
		forms[0][i].stop = 0;
		forms[1][i].stop = 1;
	}

	// shift up to the number of bits processed in parallel
	for (i = 0; i < bits; i++)
	{
		// read operands belonging to the first register bit
		// to be XORed with data
		for (k = 0; !forms[k][0].stop; k++)
			form0[k] = forms[k][0];
		form0[k].part = D;
		form0[k].index = i;
		form0[k].stop = 0;
		form0[k + 1].stop = 1;

		// one-bit shift
		for (j = 0; j < width - 1; j++)
		{
			for (k = 0; !forms[k][j + 1].stop; k++)
				forms[k][j] = forms[k][j + 1];
			forms[k][j].stop = 1;
		}
		// assign operands XOR data to the most-significant register bit
		for (j = 0; !form0[j].stop; j++)
			forms[j][width - 1] = form0[j];
		forms[j][width - 1].stop = 1;

		// XOR with operands belonging to the least-significant register bit
		// according to the generator polynomial.
		// operands for the most-significnt register bit are already assigned
		polynomial = poly >> 1;
		for (j = width - 2; j >= 0; j--)
		{
			if (polynomial & 1)
			{
				// find end of the operand list for a given register bit
				for (k = 0; !forms[k][j].stop; k++)
					;
				// append operands belonging to this register bit
				for (l = 0; !form0[l].stop; l++)
				{
					// process Ti XOR Ti (= 0 => remove the existing term Ti)
					for (m = 0; !forms[m][j].stop &&
						(forms[m][j].part != form0[l].part ||
						  forms[m][j].index != form0[l].index); m++)
						;
					// the end of operand list is not reached => remove term
					if (!forms[m][j].stop)
					{
						do {
							forms[m][j] = forms[m + 1][j];
							m++;
						} while (!forms[m][j].stop);
						k--;
					}
					// else append the new term to the operand list belonging
					// to a given register bit
					else
					{
						forms[k][j] = form0[l];
						forms[k + 1][j].stop = 1;
						k++;
					}
				}
			}
			polynomial >>= 1;
		}
	}

	// generate equations according the tags
	for (i = 0; i < width; i++)
	{
		int w_xor = 0;
		int cc = 0;
		if (format == VHDL)
			fprintf(output, "   crc(%d) <= ", i);
		else
			fprintf(output, "   crc[%d] = ", i);
		for (j = 0; !forms[j][i].stop; j++)
		{
			if (forms[j][i].part == D && w_xor)
			{
				if (format == VHDL)
					fprintf(output, " XOR ");
				else
					fprintf(output, " ^ ");
			}
			switch (forms[j][i].part)
			{
				case I: cc++; break;
				case D: fprintf(output, "reg"); break;
				default: printf("error generating equation"); exit(1);
			}
			if (forms[j][i].part != I)
			{
				if (format == VHDL)
					fprintf(output, "(%d)", forms[j][i].index);
				else
					fprintf(output, "[%d]", forms[j][i].index);
			}
			if (forms[j][i].part == D)
				w_xor = 1;
		}
		fprintf(output, ";\n");
	}
	fprintf(output, "\n");
}

/* ------------------------------------------------------------------------
 * set_output()
 *
 *   filename		- file name for writing the generated output
 *
 */
void set_output(char *filename)
{
	output = fopen(filename, "w");
	if (output == NULL)
	{
		printf("Error: unable to open output file '%s'.\n", filename);
		printf("Exiting...\n");
		exit(0);
	}
}

/* ------------------------------------------------------------------------
 * enter_generator()
 *
 *   poly		- generator polynomial
 *   width		- the number of bits of the CRC intended
 *   manually	- manual entering generator polynomial indicator
 *
 */
void enter_generator(UINT64 *poly, int width, int manually)
{
	if (width > 64)
	{
		printf("Sorry, CRC > 64 bits is not supported for now.\n");
		exit(0);
	}
	else if (width == 64 && !manually)
		*poly = gp64;
	else if (width == 32 && !manually)
		*poly = gp32;
	else if (width == 16 && !manually)
		*poly = gp16;
	else
	{
		printf("Enter generator polynomial: 0x1");
		scanf("%llx", poly);
	}
}

void print_help()
{
	printf("Usage: crctab CRCBITS PARBITS [-poly] [FILENAME]\n");
	printf("   -h, nothing   show this help screen\n");
	printf("   CRCBITS       the number of bits of the CRC intended\n");
	printf("   PARBITS       the number of bits processed in parallel\n");
	printf("   -poly         enables manual entering generator polynomial\n");
	printf("   FILENAME      output file name or nothing for the standard output\n");
	exit(0);
}

int main(int argc, char *argv[])
{
	int crcbits, parbits;	// CRC width and the number of bits processed in parallel
	int manually = 0;	// manual entering generator polynomial indicator
	UINT64 generator;	// generator polynomial

	if (argc == 2 && strcmp(argv[1], "-h") == 0 || argc < 3) print_help();

	if ((crcbits = atoi(argv[1])) <= 0)
	{
		printf("Invalid value for CRCBITS (%d). Use -h for help.\n", crcbits);
		exit(0);
	}
	if ((parbits = atoi(argv[2])) <= 0)
	{
		printf("Invalid value for PARBITS (%d). Use -h for help.\n", parbits);
		exit(0);
	}
	if (argc > 3)
	{
		if (strncmp(argv[3], "-poly", 5) == 0) manually = 1;
		else if (argc > 4 || argv[3][0] == '-')
		{
			printf("Invalid parameter '%s'. Use -h for help.\n", argv[3]);
			exit(0);
		}
		else set_output(argv[3]);
	}
	if (argc > 4) set_output(argv[4]); else if (output == NULL) output = stdout;

	enter_generator(&generator, crcbits, manually);
	table_generator(generator, crcbits, parbits);	// generate VHDL code
	format = CPP;	// generate C/C++ code
	table_generator(generator, crcbits, parbits);

	if (output != stdout) fclose(output);
	return 0;
}
