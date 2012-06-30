#!/bin/sh

CSBUS=csbus

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
${CSBUS}    ${PART0_SIZE_MASK}    "FF"
${CSBUS}    ${PART0_SIZE_BASE}    "00"
${CSBUS}    ${PART0_SIZE_MAX}     "FF"

# set the desired number of transactions
${CSBUS}    ${TRANS_COUNT}       "10"

# start the random number generator
${CSBUS}    ${RND_GEN_RUN}       "1"

# start the FrameLink adapter
${CSBUS}    ${FL_ADAPT_RUN}      "1"

