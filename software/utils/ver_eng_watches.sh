#!/bin/sh

RAW_VAL=$(csbus 01F00038)
SRCDST=$(echo 'ibase=16;' $(echo ${RAW_VAL} | tr 'abcdef' 'ABCDEF') | bc)

echo "======================= HW FULL info ======================="
echo "Design type:"
echo "  * verification core 0:         " $(csbus 01000000) 
echo "  * verification core 1:         " $(csbus 01080000) 
echo ""
echo "Generator check:                 " $(csbus 01100000)
echo "FrameLink Adapter check:         " $(csbus 01101000)
echo "Command Unit check:              " $(csbus 01200000)
echo "Scoreboad check:                 " $(csbus 01300000)
echo ""
echo "Remaining transactions to send:  " $(csbus 01101004)
echo ""
echo "Received transactions:           " $(csbus 01300004)


echo ""
echo "Verification core watches:"
echo ""
echo "Control register:            " $(csbus 01F00000)
echo ""
echo "FORK RX:            frames:  " $(csbus 01F00008) "    invalid frames: " $(csbus 01F00020) "   SRC_RDY_N: " $(echo ${SRCDST} '/ (2^ 1) % 2' | bc ) " DST_RDY_N: " $(echo ${SRCDST} '/ (2^ 0) % 2' | bc )
echo "FORK TX0:           frames:  " $(csbus 01F0000C) "    invalid frames: " $(csbus 01F00024) "   SRC_RDY_N: " $(echo ${SRCDST} '/ (2^ 3) % 2' | bc ) " DST_RDY_N: " $(echo ${SRCDST} '/ (2^ 2) % 2' | bc )
echo "FORK TX1:           frames:  " $(csbus 01F00010) "    invalid frames: " $(csbus 01F00028) "   SRC_RDY_N: " $(echo ${SRCDST} '/ (2^ 5) % 2' | bc ) " DST_RDY_N: " $(echo ${SRCDST} '/ (2^ 4) % 2' | bc )
echo "VER CORE 0 TX:      frames:  " $(csbus 01F00014) "    invalid frames: " $(csbus 01F0002C) "   SRC_RDY_N: " $(echo ${SRCDST} '/ (2^ 7) % 2' | bc ) " DST_RDY_N: " $(echo ${SRCDST} '/ (2^ 6) % 2' | bc )
echo "VER CORE 1 TX:      frames:  " $(csbus 01F00018) "    invalid frames: " $(csbus 01F00030) "   SRC_RDY_N: " $(echo ${SRCDST} '/ (2^ 9) % 2' | bc ) " DST_RDY_N: " $(echo ${SRCDST} '/ (2^ 8) % 2' | bc )
echo "BINDER TX:          frames:  " $(csbus 01F0001C) "    invalid frames: " $(csbus 01F00034) "   SRC_RDY_N: " $(echo ${SRCDST} '/ (2^11) % 2' | bc ) " DST_RDY_N: " $(echo ${SRCDST} '/ (2^10) % 2' | bc )
echo ""
