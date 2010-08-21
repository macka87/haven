#! /bin/bash

IBUF_BASE_ADDR=`echo "obase=16;ibase=16;120000" | bc`
OBUF_BASE_ADDR=`echo "obase=16;ibase=16;108000" | bc`
IBUF_TEST_BASE_ADDR=`echo "obase=16;ibase=16;114000" | bc`

CNT_PACKETS_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR}" | bc`
CNT_RECV_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 4" | bc`
CNT_RECVERR_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 8" | bc`
REG_ENABLE_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 20" | bc`
REG_ERRMASK_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 24" | bc`
REG_IBUF_STATUS_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 28" | bc`
REG_IBUF_CTRL_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 28 + 4" | bc`

OBUF_CNT_PACKETS_ADDR=`echo "obase=16;ibase=16;${OBUF_BASE_ADDR}" | bc`
OBUF_CNT_SENT_ADDR=`echo "obase=16;ibase=16;${OBUF_BASE_ADDR} + 4" | bc`
OBUF_CNT_NOTSENT_ADDR=`echo "obase=16;ibase=16;${OBUF_BASE_ADDR} + 8" | bc`
OBUF_REG_ENABLE_ADDR=`echo "obase=16;ibase=16;${OBUF_BASE_ADDR} + 20" | bc`
OBUF_REG_MACL_ADDR=`echo "obase=16;ibase=16;${OBUF_BASE_ADDR} + 24" | bc`
OBUF_REG_MACH_ADDR=`echo "obase=16;ibase=16;${OBUF_BASE_ADDR} + 28" | bc`
OBUF_REG_CTRL_ADDR=`echo "obase=16;ibase=16;${OBUF_BASE_ADDR} + 28 + 4" | bc`

BP_BASE_ADDR=`echo "obase=16;ibase=16;0124000" | bc`
BP_CONTROL=`echo "obase=16;ibase=16;${BP_BASE_ADDR} + 0000" | bc`
BP_COUNTER=`echo "obase=16;ibase=16;${BP_BASE_ADDR} + 0004" | bc`
BP_MEM=`echo "obase=16;ibase=16;${BP_BASE_ADDR} + 2000" | bc` 

MAC_MEM_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 80" | bc`

echo "=== INIT IBUF ==="
echo "reg_enable:"
csbus $REG_ENABLE_ADDR
echo "Disabling IBUF..."
csbus $REG_ENABLE_ADDR 0
echo "reg_enable:"
csbus $REG_ENABLE_ADDR
echo
echo "reg_errmask:"
csbus $REG_ERRMASK_ADDR
echo "Setting Error Mask..."
csbus $REG_ERRMASK_ADDR FF
echo "reg_errmask:"
csbus $REG_ERRMASK_ADDR
echo "Setting MAC check register..."
csbus $REG_MAC_CHECK_ADDR 1
echo "reg_mac_check:"
csbus $REG_MAC_CHECK_ADDR
echo "Setting MAC Address 1..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 00" | bc` 02491F8F
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 04" | bc` 00010013
echo "MAC Address 1:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 04" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 00" | bc`
echo "Setting MAC Address 2..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 08" | bc` B3A96551
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 0C" | bc` 00010002
echo "MAC Address 1:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 0C" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 08" | bc`
echo "Setting speed 100Mbps"
csbus $REG_IBUF_CTRL_ADDR 5
phyterctl -b 1000 -l 0 -s 100 -m full

echo
echo "=== INIT OBUF ==="
echo "reg_enable:"
csbus $OBUF_REG_ENABLE_ADDR
echo "Disabling OBUF..."
csbus $OBUF_REG_ENABLE_ADDR 0
echo "reg_enable:"
csbus $OBUF_REG_ENABLE_ADDR
echo "Setting speed 100Mbps"
csbus $OBUF_REG_CTRL_ADDR 5
echo "Setting MAC address..."
csbus $OBUF_REG_MACL_ADDR 12345678
csbus $OBUF_REG_MACH_ADDR 00000002
echo "MAC Address (low part):"
csbus $OBUF_REG_MACL_ADDR 
echo "MAC Address (high part):"
csbus $OBUF_REG_MACH_ADDR 

echo
echo "=== ENABLE DESIGN COMPONENTS ==="
echo "Enabling Bus Probe ..."
csbus `echo "obase=16;ibase=16;${BP_CONTROL}" | bc` 1
echo
echo "reg_enable:"
csbus $REG_ENABLE_ADDR
echo "Enabling IBUF..."
csbus $REG_ENABLE_ADDR 1
echo "reg_enable:"
csbus $REG_ENABLE_ADDR
echo
echo "reg_enable:"
csbus $OBUF_REG_ENABLE_ADDR
echo "Enabling OBUF..."
csbus $OBUF_REG_ENABLE_ADDR 1
echo "reg_enable:"
csbus $OBUF_REG_ENABLE_ADDR
