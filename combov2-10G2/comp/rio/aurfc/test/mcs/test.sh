#! /bin/bash

C6TXDATA="../data/aurfc_test_data1.txt"
C6CTRLDATA="../data/aurfc_test_data2.txt"
SPTXDATA="../data/aurfc_test_data1.txt"
SPCTRLDATA="../data/aurfc_test_data2.txt"

C6_BASE_ADDR=`echo "obase=16;ibase=16;004000" | bc`
SP_BASE_ADDR=`echo "obase=16;ibase=16;104000" | bc`

C6TXDATA_ADDR=`echo "obase=16;ibase=16;${C6_BASE_ADDR}" | bc`
C6CTRLDATA_ADDR=`echo "obase=16;ibase=16;${C6_BASE_ADDR} + 2000" | bc`
C6ERRORDATA_ADDR=`echo "obase=16;ibase=16;${C6_BASE_ADDR} + 4000" | bc`
C6CORRDATA_ADDR=`echo "obase=16;ibase=16;${C6_BASE_ADDR} + 6000" | bc`
C6TX_ACTIVE=`echo "obase=16;ibase=16;${C6_BASE_ADDR} + 8000" | bc`
C6CNT_ERR_ADDR=`echo "obase=16;ibase=16;${C6_BASE_ADDR} + 8010" | bc`

SPTXDATA_ADDR=`echo "obase=16;ibase=16;${SP_BASE_ADDR}" | bc`
SPCTRLDATA_ADDR=`echo "obase=16;ibase=16;${SP_BASE_ADDR} + 2000" | bc`
SPERRORDATA_ADDR=`echo "obase=16;ibase=16;${SP_BASE_ADDR} + 4000" | bc`
SPCORRDATA_ADDR=`echo "obase=16;ibase=16;${SP_BASE_ADDR} + 6000" | bc`
SPTX_ACTIVE=`echo "obase=16;ibase=16;${SP_BASE_ADDR} + 8000" | bc`
SPCNT_ERR_ADDR=`echo "obase=16;ibase=16;${SP_BASE_ADDR} + 8010" | bc`

echo
echo "Loading C6 TX DATA"
csbus $C6TXDATA_ADDR -W < $C6TXDATA
echo "C6_TX data:"
csbus -c 1024 ${C6TXDATA_ADDR}
echo
echo "Loading SP TX DATA"
csbus $SPTXDATA_ADDR -W < $SPTXDATA
echo "SP_TX data:"
csbus -c 1024 ${SPTXDATA_ADDR}
echo
echo "Loading C6 CONTROL DATA"
csbus $C6CTRLDATA_ADDR -W < $C6CTRLDATA
echo "C6 CTRL data:"
csbus -c 1024 ${C6CTRLDATA_ADDR}
echo
echo "Loading SP CONTROL DATA"
csbus $SPCTRLDATA_ADDR -W < $SPCTRLDATA
echo "SP CTRL data:"
csbus -c 1024 ${SPCTRLDATA_ADDR}
echo
echo "Starting transmision"
csbus $C6TX_ACTIVE 1
csbus $SPTX_ACTIVE 1
echo "C6 active:"
csbus $C6TX_ACTIVE
csbus `echo "obase=16;ibase=16;${C6TX_ACTIVE} + 4" | bc`
echo "SP active:"
csbus $SPTX_ACTIVE
csbus `echo "obase=16;ibase=16;${SPTX_ACTIVE} + 4" | bc`
echo
echo "Test in progress..."
C6ERR_CNT=0
SPERR_CNT=0
C6ERR_CNT=`echo "obase=10;ibase=10;${C6ERR_CNT}" | bc`
SPERR_CNT=`echo "obase=10;ibase=10;${SPERR_CNT}" | bc`

C6NEW_ERR_CNT=`csbus ${C6CNT_ERR_ADDR}`
C6NEW_ERR_CNT=`echo ${C6NEW_ERR_CNT} | tr 'a-f' 'A-F' `
C6NEW_ERR_CNT=`echo "obase=10;ibase=16;${C6NEW_ERR_CNT}" | bc`

C6ERR_CNT=${C6NEW_ERR_CNT}
echo
echo "Checking if some errors occured... No of errors: ${C6NEW_ERR_CNT}"
echo "Recieved C6 data:"
csbus -c ${C6NEW_ERR_CNT} ${C6ERRORDATA_ADDR}
echo "Correct C6 data:"
csbus -c ${C6NEW_ERR_CNT} ${C6CORRDATA_ADDR}

SPNEW_ERR_CNT=`csbus ${SPCNT_ERR_ADDR}`
SPNEW_ERR_CNT=`echo ${SPNEW_ERR_CNT} | tr 'a-f' 'A-F' `
SPNEW_ERR_CNT=`echo "obase=10;ibase=16;${SPNEW_ERR_CNT}" | bc`

SPERR_CNT=${SPNEW_ERR_CNT}
echo
echo "Checking if some errors occured... No of errors: ${SPNEW_ERR_CNT}"
echo "Recieved SP data:"
csbus -c ${SPNEW_ERR_CNT} ${SPERRORDATA_ADDR}
echo "Correct SP data:"
csbus -c ${SPNEW_ERR_CNT} ${SPCORRDATA_ADDR}
echo
echo "C6 active:"
csbus $C6TX_ACTIVE
csbus `echo "obase=16;ibase=16;${C6TX_ACTIVE} + 4" | bc`
echo "SP active:"
csbus $SPTX_ACTIVE
csbus `echo "obase=16;ibase=16;${SPTX_ACTIVE} + 4" | bc`
