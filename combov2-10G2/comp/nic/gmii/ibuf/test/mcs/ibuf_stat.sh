#! /bin/bash

IBUF_BASE_ADDR=`echo "obase=16;ibase=16;120000" | bc`
IBUF_TEST_BASE_ADDR=`echo "obase=16;ibase=16;124000" | bc`

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

echo
csbus $REG_IBUF_CTRL_ADDR 1
echo "Received packets:"
csbus $CNT_PACKETS_ADDR
echo "Correct packets:"
csbus $CNT_RECV_ADDR
echo "Discarded packets:"
csbus $CNT_RECVERR_ADDR
echo "IBUF status:"
csbus $REG_IBUF_STATUS_ADDR
#echo "IBUF_TEST reg_fifo_full:"
#csbus $REG_IBUF_TEST_FULL_ADDR
#echo "IBUF_TEST reg_status:"
#csbus $REG_IBUF_TEST_STAT_ADDR

