#!/usr/bin/env python

import os
import sys

try:
    if bin(0): pass
except NameError, ne:
    def bin(x):
        """
        bin(number) -> string

        Stringifies an int or long in base 2.
        """
        if x < 0: return '-' + bin(-x)
        out = []
        while x > 0:
            out.append('01'[x & 1])
            x >>= 1
        if x == 0: out.append('0')
        try: return '0b' + ''.join(reversed(out))
        except NameError, ne2: out.reverse()
        return '0b' + ''.join(out)

def int2binPadded(number, size): 
    """The purpose of this function is to convert integer number to binary number 0-padded.""" 
    # convert int to bin 
    return bin(number)[2:].zfill(size)

for i in range(0,131072):
    print(int2binPadded(i,32))
