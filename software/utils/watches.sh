#!/bin/sh

echo ""
echo "Application core watches:"
echo "Start/Stop register:            " $(csbus 00080000)
echo "Input interface frame counter:  " $(csbus 00080008)
echo "Output interface frame counter: " $(csbus 0008000C)
echo "Input invalid frame counter:    " $(csbus 00080010)
echo "Output invalid frame counter:   " $(csbus 00080014)
echo "Interface ready signals:        " $(csbus 00080018)
echo ""
