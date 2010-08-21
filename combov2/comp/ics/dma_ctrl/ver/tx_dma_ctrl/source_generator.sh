#!/bin/sh

TEST_PKG="tbench/test_pkg.sv"
TX_CTRL_SRC="tx_dma_ctrl_opt.hcc"

SEARCH_STRING=" *parameter *CTRL_DMA_DATA_WIDTH *="
COMMENTS="; *\/\/.*"

SUBS_STRING="#define *DMA_DATA_WIDTH"
REPLACEMENT_STRING="#define DMA_DATA_WIDTH "

TEMP_EXT="xxver"

MAKE_TARGET="tx_opt"

# parse the DMA DATA width from the test package
DMA_DATA_WIDTH=$(cat ${TEST_PKG} | grep "${SEARCH_STRING}" | \
                 sed "s/${SEARCH_STRING}//g" | sed "s/${COMMENTS}//g")

REPLACEMENT_STRING="${REPLACEMENT_STRING} ${DMA_DATA_WIDTH}"

# move to the source directory
cd ../..

# generate new Handel-C source file
cat ${TX_CTRL_SRC} | grep -v "${SUBS_STRING}" | sed \
"1i ${REPLACEMENT_STRING}" > ${TX_CTRL_SRC}.${TEMP_EXT}

mv ${TX_CTRL_SRC}.${TEMP_EXT} ${TX_CTRL_SRC}
make ${MAKE_TARGET}
