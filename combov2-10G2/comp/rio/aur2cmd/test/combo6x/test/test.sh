#! /bin/bash

TXDATA="../../../data/cmd_data1.txt"

RIO_BASE_ADDR=`echo "obase=16;ibase=16;1C000" | bc`
TXDATA_ADDR=`echo "obase=16;ibase=16;${RIO_BASE_ADDR}" | bc`
RXDATA_ADDR=`echo "obase=16;ibase=16;${RIO_BASE_ADDR} + 1000" | bc`
TX_ACTIVE=`echo "obase=16;ibase=16;${RIO_BASE_ADDR} + 4000" | bc`
STATUS=`echo "obase=16;ibase=16;${RIO_BASE_ADDR} + 4008" | bc`

echo
echo "Loading TX DATA"
csbus $TXDATA_ADDR -W < $TXDATA
echo "TX data:"
csbus -c 40 ${TXDATA_ADDR}
echo
echo "Status:"
csbus $STATUS
echo
echo "Starting transmision"
csbus $TX_ACTIVE 1
echo "reg_tx_active:"
csbus $TX_ACTIVE
echo
echo "Status:"
csbus $STATUS
echo
echo "Recieved data:"
csbus -c 40 ${RXDATA_ADDR}
echo
echo "Status:"
csbus $STATUS
