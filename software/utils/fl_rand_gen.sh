#!/bin/sh

CSBUS=csbus

if [ $# != 1 ] ; then
  echo "Usage: $0 TRANSACTION_COUNT"
  exit 1
fi


COUNT=$1

#########################################
# The address space
#########################################

# The random number generator
RND_GEN_RUN="    01100000"
RND_GEN_SEED="   01100004"

# The FrameLink adapter
FL_ADAPT_RUN="   01101000"
TRANS_COUNT="    01101004"

# The register with the range for the number of parts
NUM_PARTS_MASK=" 01101010"
NUM_PARTS_BASE=" 01101014"
NUM_PARTS_MAX="  01101018"

# The register with the range for the size of part 0
PART0_SIZE_MASK="01101080"
PART0_SIZE_BASE="01101084"
PART0_SIZE_MAX=" 01101088"

# The register with the range for the size of part 1
PART1_SIZE_MASK="01101090"
PART1_SIZE_BASE="01101094"
PART1_SIZE_MAX=" 01101098"

# The register with the range for the size of part 2
PART2_SIZE_MASK="011010A0"
PART2_SIZE_BASE="011010A4"
PART2_SIZE_MAX=" 011010A8"


#########################################
# The commands
#########################################

# set the seed of the random generator
${CSBUS}    ${RND_GEN_SEED}      "00011ACA"

# set the range of numbers of parts
${CSBUS}    ${NUM_PARTS_MASK}    "00"
${CSBUS}    ${NUM_PARTS_BASE}    "00"
${CSBUS}    ${NUM_PARTS_MAX}     "00"

# set the range of size of the part 0
${CSBUS}    ${PART0_SIZE_MASK}    "00"
${CSBUS}    ${PART0_SIZE_BASE}    "40"
${CSBUS}    ${PART0_SIZE_MAX}     "00"

# set the range of size of the part 1
${CSBUS}    ${PART1_SIZE_MASK}    "3F"
${CSBUS}    ${PART1_SIZE_BASE}    "01"
${CSBUS}    ${PART1_SIZE_MAX}     "20"

# set the range of size of the part 2
${CSBUS}    ${PART2_SIZE_MASK}    "3F"
${CSBUS}    ${PART2_SIZE_BASE}    "01"
${CSBUS}    ${PART2_SIZE_MAX}     "20"

# set the desired number of transactions
${CSBUS}    ${TRANS_COUNT}       ${COUNT}

# start the random number generator
${CSBUS}    ${RND_GEN_RUN}       "1"

# start the FrameLink adapter
${CSBUS}    ${FL_ADAPT_RUN}      "1"

