#! /bin/bash

C6TXDATA="../../data/aurvc_data1.txt"

C6_BASE_ADDR=`echo "obase=16;ibase=16;1C000" | bc`
SP_BASE_ADDR=`echo "obase=16;ibase=16;120000" | bc`

TX_CHANNELS=4
RX_CHANNELS=4

C6TXDATA_ADDR=`echo "obase=16;ibase=16;${C6_BASE_ADDR}" | bc`
C6TX_ACTIVE=`echo "obase=16;ibase=16;${C6_BASE_ADDR} + 1000" | bc`
C6STATUS=`echo "obase=16;ibase=16;${C6_BASE_ADDR} + 1008" | bc`
C6BP_BASE_ADDR=`echo "obase=16;ibase=16;${C6_BASE_ADDR} + 2000" | bc`
C6BP_CONTROL=`echo "obase=16;ibase=16;${C6BP_BASE_ADDR} + 0000" | bc`
C6BP_COUNTER=`echo "obase=16;ibase=16;${C6BP_BASE_ADDR} + 0004" | bc`
C6BP_MEM=`echo "obase=16;ibase=16;${C6BP_BASE_ADDR} + 1000" | bc`

SPTXDATA_ADDR=`echo "obase=16;ibase=16;${SP_BASE_ADDR}" | bc`
SPTX_ACTIVE=`echo "obase=16;ibase=16;${SP_BASE_ADDR} + 1000" | bc`
SPSTATUS=`echo "obase=16;ibase=16;${C6_BASE_ADDR} + 1008" | bc`
SPBP_BASE_ADDR=`echo "obase=16;ibase=16;${SP_BASE_ADDR} + 2000" | bc`
SPBP_CONTROL=`echo "obase=16;ibase=16;${SPBP_BASE_ADDR} + 0000" | bc`
SPBP_COUNTER=`echo "obase=16;ibase=16;${SPBP_BASE_ADDR} + 0004" | bc`
SPBP_MEM=`echo "obase=16;ibase=16;${SPBP_BASE_ADDR} + 1000" | bc`


BP_NEXT=`echo "obase=16;ibase=16;2000" | bc`

echo
echo "Loading C6 TX DATA ..."
csbus $C6TXDATA_ADDR -W < $C6TXDATA
echo "C6_TX data:"
csbus -c 40 ${C6TXDATA_ADDR}
echo
echo "Loading SP TX DATA ..."
csbus $SPTXDATA_ADDR -W < $C6TXDATA
echo "SP_TX data:"
csbus -c 40 ${SPTXDATA_ADDR}
echo

COUNTER=0
echo "Enabling C6X Bus Probes ..."
while [ $COUNTER -lt ${RX_CHANNELS} ]; 
do
    csbus `echo "obase=16;ibase=16;${C6BP_CONTROL} + (${COUNTER} * ${BP_NEXT})" | bc` 1
    let COUNTER=COUNTER+1;
done

COUNTER=0
echo "Enabling SFPRO Bus Probes ..."
while [ $COUNTER -lt ${TX_CHANNELS} ]; 
do
    csbus `echo "obase=16;ibase=16;${SPBP_CONTROL} + (${COUNTER} * ${BP_NEXT})" | bc` 1
    let COUNTER=COUNTER+1;
done

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

COUNTER=0
echo "Data from C6X Bus Probes ..."
while [ $COUNTER -lt ${RX_CHANNELS} ]; 
do
    echo "Data from Bus Probe ${COUNTER}. Base Address: `echo "obase=16;ibase=16;${C6BP_MEM} + (${COUNTER} * ${BP_NEXT})" | bc`"
    echo "Counter:"
    csbus `echo "obase=16;ibase=16;${C6BP_COUNTER} + (${COUNTER} * ${BP_NEXT})" | bc`
    csbus -c 1024 `echo "obase=16;ibase=16;${C6BP_MEM} + (${COUNTER} * ${BP_NEXT})" | bc`
    let COUNTER=COUNTER+1;
done
echo
COUNTER=0
echo "Data from SFPRO Bus Probes ..."
while [ $COUNTER -lt ${TX_CHANNELS} ]; 
do
    echo "Data from Bus Probe ${COUNTER}. Base Address: `echo "obase=16;ibase=16;${SPBP_MEM} + (${COUNTER} * ${BP_NEXT})" | bc`"
    echo "Counter:"
    csbus `echo "obase=16;ibase=16;${SPBP_COUNTER} + (${COUNTER} * ${BP_NEXT})" | bc`
    csbus -c 1024 `echo "obase=16;ibase=16;${SPBP_MEM} + (${COUNTER} * ${BP_NEXT})" | bc`
    let COUNTER=COUNTER+1;
done
