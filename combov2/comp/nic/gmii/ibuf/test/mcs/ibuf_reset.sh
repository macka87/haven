#! /bin/bash

IBUF_BASE_ADDR=`echo "obase=16;ibase=16;120000" | bc`
IBUF_TEST_BASE_ADDR=`echo "obase=16;ibase=16;114000" | bc`

CNT_PACKETS_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR}" | bc`
CNT_RECV_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 4" | bc`
CNT_RECVERR_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 8" | bc`
REG_ENABLE_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 20" | bc`
REG_ERRMASK_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 24" | bc`
REG_IBUF_STATUS_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 28" | bc`
REG_IBUF_CTRL_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 28 + 4" | bc`
REG_IBUF_TEST_FULL_ADDR=`echo "obase=16;ibase=16;${IBUF_TEST_BASE_ADDR} + 4" | bc`
REG_IBUF_TEST_CTRL_ADDR=`echo "obase=16;ibase=16;${IBUF_TEST_BASE_ADDR} + 8" | bc`
REG_IBUF_TEST_STAT_ADDR=`echo "obase=16;ibase=16;${IBUF_TEST_BASE_ADDR} + 8 + 4" | bc`

BP_BASE_ADDR=`echo "obase=16;ibase=16;0124000" | bc`
BP_CONTROL=`echo "obase=16;ibase=16;${BP_BASE_ADDR} + 0000" | bc`
BP_COUNTER=`echo "obase=16;ibase=16;${BP_BASE_ADDR} + 0004" | bc`
BP_MEM=`echo "obase=16;ibase=16;${BP_BASE_ADDR} + 20000" | bc` 

echo
echo "IBUF counters reset..."
csbus $REG_IBUF_CTRL_ADDR 2
