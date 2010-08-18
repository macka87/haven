#! /bin/bash

OBUF_BASE_ADDR=`echo "obase=16;ibase=16;108000" | bc`

OBUF_CNT_PACKETS_ADDR=`echo "obase=16;ibase=16;${OBUF_BASE_ADDR}" | bc`
OBUF_CNT_SENT_ADDR=`echo "obase=16;ibase=16;${OBUF_BASE_ADDR} + 4" | bc`
OBUF_CNT_NOTSENT_ADDR=`echo "obase=16;ibase=16;${OBUF_BASE_ADDR} + 8" | bc`
OBUF_REG_ENABLE_ADDR=`echo "obase=16;ibase=16;${OBUF_BASE_ADDR} + 20" | bc`
OBUF_REG_MACL_ADDR=`echo "obase=16;ibase=16;${OBUF_BASE_ADDR} + 24" | bc`
OBUF_REG_MACH_ADDR=`echo "obase=16;ibase=16;${OBUF_BASE_ADDR} + 28" | bc`
OBUF_REG_CTRL_ADDR=`echo "obase=16;ibase=16;${OBUF_BASE_ADDR} + 28 + 4" | bc`

echo
echo "OBUF counters reset..."
csbus $OBUF_REG_CTRL_ADDR 2
