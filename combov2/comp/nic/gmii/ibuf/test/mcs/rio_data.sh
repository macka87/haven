#! /bin/bash

IBUF_BASE_ADDR=`echo "obase=16;ibase=16;120000" | bc`
IBUF_TEST_BASE_ADDR=`echo "obase=16;ibase=16;114000" | bc`

CNT_PACKETS_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR}" | bc`
CNT_RECV_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 4" | bc`
CNT_RECVERR_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 8" | bc`
REG_ENABLE_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 20" | bc`
REG_ERRMASK_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 24" | bc`
REG_IBUF_STATUS_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 28" | bc`

BP_BASE_ADDR=`echo "obase=16;ibase=16;0124000" | bc`
BP_CONTROL=`echo "obase=16;ibase=16;${BP_BASE_ADDR} + 0000" | bc`
BP_COUNTER=`echo "obase=16;ibase=16;${BP_BASE_ADDR} + 0004" | bc`
BP_MEM=`echo "obase=16;ibase=16;${BP_BASE_ADDR} + 2000" | bc` 

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

echo "Enabling Bus Probe ..."
csbus `echo "obase=16;ibase=16;${BP_CONTROL}" | bc` 1

echo "Counter:"
csbus `echo "obase=16;ibase=16;${BP_COUNTER}" | bc`

echo "Data from Bus Probe ..."
csbus -c 2048 `echo "obase=16;ibase=16;${BP_MEM}" | bc`

