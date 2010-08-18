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
csbus $REG_ERRMASK_ADDR FF
echo "reg_errmask:"
csbus $REG_ERRMASK_ADDR
echo "Setting MAC check register..."
csbus $REG_MAC_CHECK_ADDR 3
echo "reg_mac_check:"
csbus $REG_MAC_CHECK_ADDR
echo "Setting MAC Address 1..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 00" | bc` 11223300
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 04" | bc` 0001aabb
echo "Setting MAC Address 2..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 08" | bc` 11223311
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 0C" | bc` 0001aabb
echo "Setting MAC Address 3..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 10" | bc` 11223322
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 14" | bc` 0001aabb
echo "Setting MAC Address 4..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 18" | bc` 11223333
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 1C" | bc` 0001aabb
echo "Setting MAC Address 5..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 20" | bc` 11223344
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 24" | bc` 0001aabb
echo "Setting MAC Address 6..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 28" | bc` 11223355
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 2C" | bc` 0001aabb
echo "Setting MAC Address 7..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 30" | bc` 11223366
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 34" | bc` 0001aabb
echo "Setting MAC Address 8..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 38" | bc` 11223377
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 3C" | bc` 0001aabb
echo "Setting MAC Address 9..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 40" | bc` 11223388
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 44" | bc` 0001aabb
echo "Setting MAC Address 10"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 48" | bc` 11223399
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 4C" | bc` 0001aabb
echo "Setting MAC Address 11..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 50" | bc` 112233aa
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 54" | bc` 0001aabb
echo "Setting MAC Address 12..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 58" | bc` 112233bb
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 5C" | bc` 0001aabb
echo "Setting MAC Address 13..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 60" | bc` 112233cc
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 64" | bc` 0001aabb
echo "Setting MAC Address 14..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 68" | bc` 112233dd
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 6C" | bc` 0001aabb
echo "Setting MAC Address 15..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 70" | bc` 112233ee
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 74" | bc` 0001aabb
echo "Setting MAC Address 16..."
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 78" | bc` 112233ff
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 7C" | bc` 0001aabb
echo "MAC Address 1:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 04" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 00" | bc`
echo "MAC Address 2:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 0C" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 08" | bc`
echo "MAC Address 3:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 14" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 10" | bc`
echo "MAC Address 4:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 1C" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 18" | bc`
echo "MAC Address 5:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 24" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 20" | bc`
echo "MAC Address 6:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 2C" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 28" | bc`
echo "MAC Address 7:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 34" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 30" | bc`
echo "MAC Address 8:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 3C" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 38" | bc`
echo "MAC Address 9:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 44" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 40" | bc`
echo "MAC Address 10:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 4C" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 48" | bc`
echo "MAC Address 11:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 54" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 50" | bc`
echo "MAC Address 12:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 5C" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 58" | bc`
echo "MAC Address 13:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 64" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 60" | bc`
echo "MAC Address 14:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 6C" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 68" | bc`
echo "MAC Address 15:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 74" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 70" | bc`
echo "MAC Address 16:"
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 7C" | bc`
csbus `echo "obase=16;ibase=16;${MAC_MEM_ADDR} + 78" | bc`
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

