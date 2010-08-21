#! /bin/bash

TXDATA="../data/rio_data1.txt"
CTRLDATA="../data/rio_data2.txt"

RIO_BASE_ADDR=`echo "obase=16;ibase=16;11C000" | bc`
TXDATA_ADDR=`echo "obase=16;ibase=16;${RIO_BASE_ADDR}" | bc`
CTRLDATA_ADDR=`echo "obase=16;ibase=16;${RIO_BASE_ADDR} + 1000" | bc`
ERRORDATA_ADDR=`echo "obase=16;ibase=16;${RIO_BASE_ADDR} + 2000" | bc`
CORRDATA_ADDR=`echo "obase=16;ibase=16;${RIO_BASE_ADDR} + 3000" | bc`
TX_ACTIVE=`echo "obase=16;ibase=16;${RIO_BASE_ADDR} + 4000" | bc`
CNT_ERR_ADDR=`echo "obase=16;ibase=16;${RIO_BASE_ADDR} + 4004" | bc`
STATUS=`echo "obase=16;ibase=16;${RIO_BASE_ADDR} + 4008" | bc`

echo
echo "Loading TX DATA"
csbus $TXDATA_ADDR -W < $TXDATA
echo "TX data:"
csbus -c 1024 ${TXDATA_ADDR}
echo
echo "Loading CONTROL DATA"
csbus $CTRLDATA_ADDR -W < $CTRLDATA
echo "CTRL data:"
csbus -c 1024 ${CTRLDATA_ADDR}
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

echo
echo "Test in progress..."
ERR_CNT=0
ERR_CNT=`echo "obase=10;ibase=10;${ERR_CNT}" | bc`
#while [ 1 ]
#do
    NEW_ERR_CNT=`csbus ${CNT_ERR_ADDR}`
    NEW_ERR_CNT=`echo ${NEW_ERR_CNT} | tr 'a-f' 'A-F' `
    NEW_ERR_CNT=`echo "obase=10;ibase=16;${NEW_ERR_CNT}" | bc`

    if [ NEW_ERR_CNT > ERR_CNT ]
    then
        ERR_CNT=${NEW_ERR_CNT}
        echo
        echo "New errors have occured! No of errors: ${NEW_ERR_CNT}"
        echo "Recieved data:"
        csbus -c ${NEW_ERR_CNT} ${ERRORDATA_ADDR}
        echo "Correct data:"
        csbus -c ${NEW_ERR_CNT} ${CORRDATA_ADDR}
    fi

#done
