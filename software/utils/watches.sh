#!/bin/sh

RAW_VAL=$(csbus 00080018)
SRCDST=$(echo 'ibase=16;' $(echo ${RAW_VAL} | tr 'abcdef' 'ABCDEF') | bc)

echo ""
echo "Application core watches:"
echo "Control register:            " $(csbus 00080000)
echo ""
echo "Input interface:    frames:  " $(csbus 00080008) "    invalid frames: " $(csbus 00080010) "   DST_RDY_N: " $(echo ${SRCDST} '/ (2^ 0) % 2' | bc ) " SRC_RDY_N: " $(echo ${SRCDST} '/ (2^ 1) % 2' | bc )
echo "Output interface:   frames:  " $(csbus 0008000C) "    invalid frames: " $(csbus 00080014) "   DST_RDY_N: " $(echo ${SRCDST} '/ (2^ 2) % 2' | bc ) " SRC_RDY_N: " $(echo ${SRCDST} '/ (2^ 3) % 2' | bc )
echo ""
