#! /bin/bash

RIO_GMII_BASE_ADDR=`echo "obase=16;ibase=16;0114000" | bc`

#echo
#echo "reg_errmask:"
#csbus $REG_ERRMASK_ADDR
#echo "Setting Error Mask..."
#csbus $REG_ERRMASK_ADDR FF
#echo "reg_errmask:"
#csbus $REG_ERRMASK_ADDR
#echo
#echo "reg_enable:"
#csbus $REG_ENABLE_ADDR
#echo "Enabling IBUF..."
#csbus $REG_ENABLE_ADDR 1
#echo "reg_enable:"
#csbus $REG_ENABLE_ADDR

echo "Reseting Bus Probe ..."
csbus `echo "obase=16;ibase=16;RIO_GMII_BASE_ADDR" | bc` 1

