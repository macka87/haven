#! /bin/bash

IBUF_BASE_ADDR=`echo "obase=16;ibase=16;120000" | bc`
IBUF_TEST_BASE_ADDR=`echo "obase=16;ibase=16;114000" | bc`

CNT_PACKETS_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR}" | bc`
CNT_RECV_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 4" | bc`
CNT_RECVERR_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 8" | bc`
REG_ENABLE_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 20" | bc`
REG_ERRMASK_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 24" | bc`
REG_IBUF_STATUS_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 28" | bc`
REG_IBUF_TEST_FULL_ADDR=`echo "obase=16;ibase=16;${IBUF_TEST_BASE_ADDR} + 4" | bc`
REG_MIN_LEN_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 30" | bc`
REG_MTU_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 34" | bc`
REG_MAC_CHECK_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 38" | bc`
REG_IBUF_TEST_CTRL_ADDR=`echo "obase=16;ibase=16;${IBUF_TEST_BASE_ADDR} + 8" | bc`

MAC_MEM_ADDR=`echo "obase=16;ibase=16;${IBUF_BASE_ADDR} + 80" | bc`

BP_BASE_ADDR=`echo "obase=16;ibase=16;0124000" | bc`
BP_CONTROL=`echo "obase=16;ibase=16;${BP_BASE_ADDR} + 0000" | bc`
BP_COUNTER=`echo "obase=16;ibase=16;${BP_BASE_ADDR} + 0004" | bc`
BP_MEM=`echo "obase=16;ibase=16;${BP_BASE_ADDR} + 2000" | bc` 

echo
echo "Disabling IBUF..."
csbus $REG_ENABLE_ADDR 0
echo "reg_enable:"
csbus $REG_ENABLE_ADDR
echo
echo "Setting Error Mask..."
csbus $REG_ERRMASK_ADDR 03
echo "reg_errmask:"
csbus $REG_ERRMASK_ADDR
echo "Setting MAC check register..."
csbus $REG_MAC_CHECK_ADDR 3
echo "reg_mac_check:"
csbus $REG_MAC_CHECK_ADDR
echo "Setting MAC Address 1..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 00" | bc` 02491F8F
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 04" | bc` 00000013
echo "MAC Address 1:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 04" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 00" | bc`
echo "Setting MAC Address 2..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 08" | bc` 02491F90
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 0C" | bc` 00010013
echo "MAC Address 1:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 0C" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 08" | bc`
echo "Setting min_len..."
csbus $REG_MIN_LEN_ADDR 40
echo "reg_min_len:"
csbus $REG_MIN_LEN_ADDR
#echo "Setting MTU..."
#csbus $REG_MTU_ADDR 50
echo "reg_mtu:"
csbus $REG_MTU_ADDR
echo
echo "Enabling Bus Probe ..."
csbus `echo "obase=16;ibase=16;${BP_CONTROL}" | bc` 1
echo
echo "Enabling IBUF..."
csbus $REG_ENABLE_ADDR 1
echo "reg_enable:"
csbus $REG_ENABLE_ADDR
echo
echo "Setting IBUF_TEST to 'allways ready' mode..."
csbus $REG_IBUF_TEST_CTRL_ADDR 0
echo "TEST: reg_ctrl:"
csbus $REG_IBUF_TEST_CTRL_ADDR

