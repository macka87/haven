#! /bin/bash

C6TXDATA="../../data/cmd_data1.txt"
SPTXDATA="../../data/cmd_data2.txt"

C6_BASE_ADDR=`echo "obase=16;ibase=16;1C000" | bc`
SP_BASE_ADDR=`echo "obase=16;ibase=16;11C000" | bc`

C6TXDATA_ADDR=`echo "obase=16;ibase=16;${C6_BASE_ADDR}" | bc`
C6RXDATA_ADDR=`echo "obase=16;ibase=16;${C6_BASE_ADDR} + 1000" | bc`
C6TX_ACTIVE=`echo "obase=16;ibase=16;${C6_BASE_ADDR} + 4000" | bc`
C6STATUS=`echo "obase=16;ibase=16;${C6_BASE_ADDR} + 4008" | bc`

SPTXDATA_ADDR=`echo "obase=16;ibase=16;${SP_BASE_ADDR}" | bc`
SPRXDATA_ADDR=`echo "obase=16;ibase=16;${SP_BASE_ADDR} + 1000" | bc`
SPTX_ACTIVE=`echo "obase=16;ibase=16;${SP_BASE_ADDR} + 4000" | bc`
SPSTATUS=`echo "obase=16;ibase=16;${SP_BASE_ADDR} + 4008" | bc`

echo
echo "Loading C6 TX DATA"
csbus $C6TXDATA_ADDR -W < $C6TXDATA
echo "C6_TX data:"
csbus -c 40 ${C6TXDATA_ADDR}
echo
echo "Loading SP TX DATA"
csbus $SPTXDATA_ADDR -W < $SPTXDATA
echo "SP_TX data:"
csbus -c 40 ${SPTXDATA_ADDR}
echo
echo "C6 Status:"
csbus $C6STATUS
echo "SP Status:"
csbus $SPSTATUS
echo
echo "Starting transmision"
csbus $C6TX_ACTIVE 1
csbus $SPTX_ACTIVE 1
echo "C6 active:"
csbus $C6TX_ACTIVE
echo "SP active:"
csbus $SPTX_ACTIVE
echo
echo "C6 Status:"
csbus $C6STATUS
echo "SP Status:"
csbus $SPSTATUS
echo

echo
echo "Recieved C6 data:"
csbus -c 400 ${C6RXDATA_ADDR}
echo
echo "Recieved SP data:"
csbus -c 400 ${SPRXDATA_ADDR}
echo
echo "C6 Status:"
csbus $C6STATUS
echo "SP Status:"
csbus $SPSTATUS

