/*******************************************************************************
 *
 * Unified Coverage Database API
 *
 * Copyright 1991-2011 Mentor Graphics Corporation
 *
 * All Rights Reserved.
 *
 * THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
 * PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
 * LICENSE TERMS.
 *
 * $Id: //dvt/mti/rel/10.0c/src/vsim/ucdb.h#1 $
 *
 ******************************************************************************/
#ifndef UCDB_API_H
#define UCDB_API_H

#ifdef __cplusplus
extern "C" {
#endif


/******************************************************************************
* UCDB version
* This allows the API to determine with what version the user's code was
* compiled, as it may be different from that with which it is linked.  This is
* passed implicitly with all functions that open a UCDB file.
******************************************************************************/
#define UCDB_H_REVISION     43
#define UCDB_H_MINOR_NUMBER (0*10000)
#define UCDB_H_MAJOR_NUMBER (10*10000*100)
#define UCDB_H_RELEASE (UCDB_H_MAJOR_NUMBER+UCDB_H_MINOR_NUMBER)

#define UCDB_H_VERSION (UCDB_H_RELEASE+UCDB_H_REVISION)

/*******************************************************************************
* Unified Coverage Database Organization
*
* UCDB files are organized into two sections.
*
* The first section contains information about the test or set of tests that
* were used to generate the coverage data.  Multiple test records should be in
* the database when the file has been created from a merge of multiple
* databases.
*
* The second section contains the coverage data, organized in a hierarchy of
* scopes related to the design, testbench, and test plan.
*
*
* TEST
*
* When first writing to the database, define information about the test from
* which coverage data is acquired.  In addition to a fixed list of fields, any
* of which may be NULL or unused, there are user-defined attributes.
*
* -----------------------------------------------------------------
*  Name | SimTime | Units | CPUTime | Seed | TestArgs | Attrs
* -----------------------------------------------------------------
*  Str  | double  | Str   | Double  | Str  | Str      | Ptr
* -----------------------------------------------------------------
* ------------------------------------------------------------------
*  Date | SimArgs | User | Compulsory | Comment | Status | Filename
* ------------------------------------------------------------------
*  Str  | Str     | Str  | BOOLEAN    | Str     | Int    | Str
* ------------------------------------------------------------------
* Name:     Name of the coverage test
* SimTime:  Simulation time for completion of the test
* Units:    Units for simulation time ("fs", "ps", "ns", "us", "ms", "sec",
*           "min", "hr")
*           NOTE: in QuestaSim, the $Now TCL variable contains current
*           simulation time in a string of this form
* CPUTime:  CPU time for completion of the test.
*           NOTE: in QuestaSim, the "simstats" command can return CPU time.
* Seed:     Randomization seed for the test, should be the seed value provided
*           by the "-sv_seed" vsim option.
* TestArgs: Arguments used to run test, could be used to capture "knob settings"
*           for parameterizable tests, as well as name of test script.
*           Also known as "Command".
* Attrs:    Other user-defined attributes, see type definition below.
* Date:     time of the start of simulation -- if created by QuestaSim, it is a
*           string like "20060105160030" for 4:00:30 PM January 5, 2006: output
*           of strftime with format "%Y%m%d%H%M%S"
* SimArgs:  Simulator command line arguments, can be picked up automatically.
* User:     The user's ID who had run the test.
* Compulsory: Whether this should be considered a compulsory or "must run"
*           test.
* Comment:  String saved by user associated with test (description)
* Status:   Status of test: fatal error ($fatal was called), error ($error was
*           called), warning ($warning was called) or OK.
* Filename: This is the database filename that the test was originally written
*           to.
*
*
* NODES IN THE DATABASE
*
* The coverage database is a tree of nodes (called scopes) in general
* corresponding to design hierarchy.  All nodes except the root node have a
* pointer to their parent.  If design hierarchy is not relevant to coverage, it
* need not be represented in the UCDB.
*
* Nodes may have children, other scope nodes or coverage items.  Design units
* (e.g., Verilog module types or VHDL architectures) are represented as scopes,
* too.  This is because sometimes coverage is represented for the design unit,
* as a union of the coverage of all instances of the design unit.  As written
* by QuestaSim, only code coverage is represented underneath the design unit.
* Note that design units with a single instance in the design are not stored;
* only the instance is stored.
*
* Coverage items are always children of a particular scope.  Coverage items are
* only accessible through their parent scope; this allows optimizations related
* to efficiently storing a set of coverage items that always lie in a certain
* scope.
*
* Scope nodes may represent:
*   *   Design hierarchy: instances of modules, function scope, packages, etc.
*   *   Hierarchy for coverage counts: e.g., a scope to contain different
*       counts for expression rows in expression coverage; scopes to represent
*       SystemVerilog covergroups.  If there is no coverage hierarchy (e.g.,
*       with statement coverage) none is used.  See nesting rules below.
*   *   Test plan items.  These are optional, but are required for some use
*       models of test traceability analysis.  In particular, if you want the
*       UCDB to represent associations between test plan items and coverage
*       items using built-in "tags" -- see *Tag*() functions below -- then test
*       plan item scope should exist in the database.
*
* A coveritem is a single count or vector of bits, generally used to compute
* coverage, represented in the database.  In some coverage models -- e.g.,
* SystemVerilog covergroups -- these represent "bins", but have been expanded
* to represent more types of coverage data.
*
* A coveritem is always accessed through a handle to its parent scope, and an
* index uniquely identifying it within the scope.  One may always query of a
* scope how many coveritems it contains.
*
* NESTING RULES
*
* The UCDB does some light enforcement of HDL nesting rules.  Nesting rules
* are more strictly enforced for coverage scopes, coveritems, and testplan
* scopes. The "covergroup" scopes are for generic use; in fact, coverage
* hierarchy for the UCDB could have been built using "covergroup" scopes only
* -- COVERGROUP, COVERINSTANCE, COVERPOINT, and CROSS -- but for clarity
* different types of coverage (assertion, statement, FSM, etc.) are given their
* own coverage scopes.
*
* The following rules define what nesting rules are enforced by the UCDB:
*
* HDL SCOPE can contain any of:
*   HDL SCOPE, COVER SCOPE, STANDALONE COVERITEM
*
* HDL SCOPE is one of the scope types:
*   UCDB_INSTANCE, UCDB_PACKAGE, UCDB_PROGRAM, UCDB_PACKAGE, UCDB_INTERFACE,
*   UCDB_PROCESS, UCDB_GENERATE, UCDB_TASK, UCDB_FUNCTION, UCDB_FORKJOIN,
*   UCDB_BLOCK, UCDB_CLASS, UCDB_GENERIC
*
* UCDB_INSTANCE contains a "DU" (design unit) or "type" pointer to one of:
*   UCDB_DU_MODULE, UCDB_DU_ARCH
*
* UCDB_PACKAGE contains a "DU" (design unit) or "type" pointer to a:
*   UCDB_DU_PACKAGE
*
* UCDB_PROGRAM contains a "DU" (design unit) or "type" pointer to a:
*   UCDB_DU_PROGRAM
*
* UCDB_INTERFACE contains a "DU" (design unit) or "type" pointer to a:
*   UCDB_DU_INTERFACE
*
* DU SCOPES (UCDB_DU_*) may contain:
*   code coverage coveritems
*   (This can be enhanced to include other subscopes or other types of
*   coveritems, if the database is to be organized to include easily accessible
*   design-unit-based aggregation of data.)
*
* COVER SCOPE is one of the scope types:
*   UCDB_COVERGROUP, UCDB_COVERINSTANCE, UCDB_COVERPOINT, UCDB_CROSS,
*   UCDB_BRANCH, UCDB_EXPR, UCDB_COND, UCDB_TOGGLE, UCDB_FSM,
*   UCDB_ASSERT, UCDB_COVER
*
* STANDALONE COVERITEM is one of the coveritem types:
*   UCDB_STMTBIN, UCDB_USERBIN, UCDB_COUNT
*
* UCDB_TESTPLAN scope can contain only:
*   UCDB_TESTPLAN scope
*
* SystemVerilog covergroup, transaction coverage, user-defined, and
* miscellaneous coverage scope rules:
*
* UCDB_COVERGROUP scope can contain the scope types:
*   UCDB_COVERINSTANCE, UCDB_COVERPOINT, UCDB_CROSS
*
* UCDB_CROSS scope must refer to at least two scopes of type UCDB_COVERPOINT,
* which must have the same parent as the UCDB_CROSS.
*
* UCDB_COVERPOINT scope can contain only:
*   UCDB_CVGBIN coveritems
*   UCDB_ILLEGALBIN coveritems
*   UCDB_IGNOREBIN coveritems
*   UCDB_DEFAULT coveritems
*   Note: UCDB_DEFAULT may be ORed with each of the other bin types to indicate
*   a default bin of the given type.
*
* UCDB_CROSS scope can contain only:
*   UCDB_CVGBIN coveritems
*   UCDB_ILLEGALBIN coveritems
*   UCDB_IGNOREBIN coveritems
*   UCDB_DEFAULT coveritems
*
* UCDB_COVERINSTANCE can contain the scope types:
*   UCDB_COVERPOINT, UCDB_CROSS
*
* SystemVerilog assert and cover objects:
*
* UCDB_ASSERT scope must contain:
*   1 each of coveritems:
*   UCDB_ASSERTBIN
*   no more than 1 of these optional coveritems:
*   UCDB_VACUOUSBIN, UCDB_DISABLEDBIN, UCDB_ATTEMPTSBIN, UCDB_ACTIVEBIN,
*   UCDB_PEAKACTIVEBIN, UCDB_PASSBIN
*   (Note: UCDB_ASSERTBIN indicates assertion failures.  PASSBIN counts toward
*   aggregated coverage.)
*
* UCDB_COVER scope must contain:
*   1 each of coveritems:
*   UCDB_COVERBIN
*   (Note: UCDB_COVERBIN indicates non-vacuous coverage passes or successes.)
*
* Code coverage:
*
* UCDB_STMTBIN may appear in any HDL scope
*
* UCDB_BRANCH scope must contain only:
*   UCDB_BRANCHBIN coveritems
*
* UCDB_EXPR node is used in a 3-level hierarchy:
*   UCDB_EXPR top node contains name and source info
*       UCDB_EXPR second-level nodes are named "FEC" and "UDP" for different
*           representations of expression coverage
*           UCDB_EXPRBIN coveritems
*           Note: coveritem name is description of the expression truth table
*           row.
*
* UCDB_COND node is used in a 3-level hierarchy:
*   UCDB_COND top node contains name and source info
*       UCDB_COND second-level nodes are named "FEC" and "UDP" for different
*           representations of condition coverage
*           UCDB_CONDBIN coveritems
*           Note: coveritem name is description of the condition truth table
*           row.
*
* UCDB_TOGGLE scope must contain:
*   UCDB_TOGGLEBIN coveritems
*   Note: coveritem name is name of toggle transition
*   Note: for extended toggles, coveritems 0 and 1 are the lh, hl transitions,
*   and coveritems 2-5 are the z transitions.
*   Note: toggle nodes, because of their abundance, are lighter-weight
*   structures than all other types in the database, lacking some data that
*   other scopes have.  Exceptions are noted in comments below.
*
* UCDB_FSM scope must contain:
*   2 subscopes: UCDB_FSM_STATES, UCDB_FSM_TRANS
*
* UCDB_FSM_STATES, UCDB_FSM_TRANS scopes must contain:
*   UCDB_FSMBIN coveritems
*
*
*******************************************************************************/

/* Ensure that size-critical types are defined on all OS platforms. */
#if defined (_MSC_VER)
typedef unsigned __int64 uint64_t;
typedef unsigned __int32 uint32_t;
typedef unsigned __int16 uint16_t;
typedef unsigned __int8 uint8_t;
typedef signed __int64 int64_t;
typedef signed __int32 int32_t;
typedef signed __int16 int16_t;
typedef signed __int8 int8_t;
#elif defined(__MINGW32__)
#include <stdint.h>
#elif defined(__linux)
#include <inttypes.h>
#else
#include <sys/types.h>
#endif

#ifdef WIN32
#define INT64_LITERAL(val)     ((int64_t)val)
#define INT64_ZERO             ((int64_t)0)
#define INT64_ONE              ((int64_t)1)
#define INT64_NEG1             ((int64_t)-1)
#else
#define INT64_LITERAL(val)     (val##LL)
#define INT64_ZERO             (0LL)
#define INT64_ONE              (1LL)
#define INT64_NEG1             (-1LL)
#endif

typedef uint64_t ucdbCoverTypeT;           /* typedef for one of these: */
typedef uint64_t ucdbCoverMaskTypeT;       /* typedef for a set of these: */

/*****************************************************************************
 *  UCDB predefined attributes. The following attribute keys are predefined
 *  and can be used on specific type of objects as specified below.
 *  This is to provide a faster access mechanism for some frequently accessed
 *  attributes, as compared to other user defined attributes.
 *
 *  ===========================================================================
 *  Attributes common to all history nodes (i.e. ucdbHistoryNodeKindEnumT).
 *  Note: test data record nodes (i.e. ucdbTestT) are a subset of history nodes
 *  (i.e. ucdbHistoryNodeKindEnumT).
 *  ===========================================================================
 *
 *  FILENAME: string             [MANDATORY]
 *      - This is a filepath:
 *            UCDB_HISTORYNODE_MERGE    ==> the UCDB mergefile pathname
 *            UCDB_HISTORYNODE_TEST     ==> the UCDB file pathname
 *            UCDB_HISTORYNODE_TESTPLAN ==> the UCDB testplan file pathname
 *  CMDLINE: string              [MANDATORY]
 *      - The actual command line used to create resulting UCDB file
 *        associated with the FILENAME file.
 *  RUNCWD: string               [MANDATORY]
 *      - When this exists, it is working directory in which
 *        CMDLINE was executed.
 *  CPUTIME: double              [OPTIONAL]
 *      - This is the cpu time associated with the execution of CMDLINE.
 *  HISTCOMMENT: string          [OPTIONAL]
 *      - This is a general-purpose comment.
 *
 *  ===========================================================================
 *  Attributes for test data record (ucdbTestT).  See comment under "TEST"
 *  above.
 *  Note: test data record nodes (i.e. ucdbTestT) are a subset of history nodes
 *  (i.e. ucdbHistoryNodeKindEnumT).
 *  ===========================================================================
 *
 *  SIMTIME: double
 *      - This is the simulation time for test completion.
 *  TIMEUNIT: string
 *      - This is the time unit for the simulation run.
 *  CPUTIME: double  [see 'attributes common to all history nodes' above]
 *      - This is the cpu time for test completion.
 *  DATE: string
 *      - This is the time at which the simulation was initiated, a string as
 *        described above.
 *  VSIMARGS: string
 *      - Simulator command line arguments.
 *  USERNAME: string
 *      - This is the name of the user who ran the test.
 *  TESTSTATUS: int, enum value ucdbTestStatusT
 *      - This is the status of the simulation run.
 *  TESTNAME: string
 *      - This is the name of the test.
 *  FILENAME: string [see 'attributes common to all history nodes' above]
 *      - This is the database filename that the test was originally written to.
 *  SEED: string
 *      - This is 0 or the seed provided by the -sv_seed vsim option.
 *  CMDLINE: string [see 'attributes common to all history nodes' above]
 *      - This is a string intended for command line arguments.
 *  TESTCMD is deprecated and replaced by CMDLINE
 *  HISTCOMMENT: string  [see 'attributes common to all history nodes' above]
 *      - This is a general-purpose comment.
 *  TESTCOMMENT is deprecated and replaced by HISTCOMMENT.
 *  COMPULSORY: int (0|1)
 *      - This indicates if the test is compulsory.
 *  RUNCWD: string [see 'attributes common to all history nodes' above]
 *      - When this exists, it is working directory of the simulation
 *        from which the UCDB was saved.
 *  TESTDATA_MERGED: int: (2 or more)
 *        The number of times the same test has been merged.
 *      - During a merge, test data records with the same name are merged
 *        (i.e. collapsed into one testdata record). When this attribute
 *        exists, it holds the number of times same test has been merged.
 *      - When this attribute is missing, the count is assumed to be 1.
 *  HOSTNAME: string
 *      - This is the hostname on which the simulation is run and the DB is created
 *  HOSTOS: string
 *      - This is the hostname OS
 *  WLFNAME: string
 *  LOGNAME: string
 *  MEMUSAGE: string
 *
 *  ===============================================
 *  Attributes unique to UCDB_HISTORYNODE_TESTPLAN.
 *  ===============================================
 *
 *  PATH: string
 *      - Testplan path.
 *  XMLSOURCE: string
 *      - This is the XML file pathname
 *  SIGNATURE: string            [OPTIONAL]
 *      - Used to determine if the XMLSOURCE file is stale. Given a valid
 *        filepath, ucdb_CalculateHistorySignature() calculates a signature
 *        for that file. Recalculating this signature on the same file shall
 *        always produce the same results as long as the file contents remain
 *        unmodified. If ever the  file is changed/modified the resulting
 *        signature will also be changed. This allows for efficient checking
 *        if a file has become "dirty".
 *
 *  ============================================
 *  Attributes unique to UCDB_HISTORYNODE_MERGE.
 *  ============================================
 *  < none >
 *
 *  =====================================
 *  Attributes for code coverage objects.
 *  =====================================
 *
 *  SINDEX: int (>= 1)
 *      - This is the statement number of a statement or expression in a
 *        design unit, starting at 1.
 *  BCOUNT: int
 *      - Used on branch coverage scopes.
 *      - This is the total count of a branch scope. This is the sum of true
 *        counts of individual branch cover items plus the count of "else".
 *  BTYPE: int: 1 == case, 0 = if-else
 *      - Used on branch coverage scopes.
 *      - This flag specifies whether the branch is an IF-ELSE or CASE type:
 *        1 means the branch is a case statement; 0 means an if-else statement.
 *  BHASELSE: int: 1 == has else, 0 == no else
 *      - Used on branch coverage scopes.
 *      - This flag specifies whether the if branch an "else" clause or not.
 *  EHEADER: string:
 *      - Used on expression or condition scopes.
 *      - Header strings for each column of the table separated by ';'.
 *  FECOPTION: int:
 *      - Used on expression or condition scopes if -cover ec -fec  has been used.
 *  FECSTR: string:
 *      - Used on expression or condition scopes if -cover ec -fec  has been used.
 *      - Used to store vectors with each coverbin. May contain zero or more
 *        vectors.
 *  FSMID: string
 *      - Used with FSM coverage.
 *      - Symbolic name for an FSM state, usually derived from state variable
 *  FSTATEVAL: int
 *      - Used on fsm coverage state coveritems.
 *      - The value of an fsm state.
 *
 *  =========================================
 *  Attributes for SystemVerilog covergroups.
 *  =========================================
 *
 *  BINRHS: string
 *      - Used on SV coverpoint coveritems (bins).
 *      - This is the rhs value of a bin, a string that describes the sampled
 *        values that potentially could cause the particular bin to increment
 *  GOAL: int
 *      - Used on SV covergroup, coverpoint or cross scopes.
 *      - This is the option.goal or type_option.goal of the object.
 *  GOAL: float
 *      - Optionally used on other types of scopes, an arbitrary goal that can
 *        have an effect (as for TESTPLAN scopes) in GUIs or reports.
 *  ATLEAST: int
 *      - Used on SV covergroup, coverpoint or cross scopes.
 *      - This is the option.at_least or type_option.at_least of the object.
 *  COMMENT: string
 *      - Used on SV covergroup, coverpoint or cross scopes.
 *      - This is the option.comment or type_option.comment of the object.
 *  AUTOBINMAX: int
 *      - Used on SV covergroup or coverpoint scopes.
 *      - This is the option.auto_bin_max of the object.
 *  DETECTOVERLAP: int (0|1)
 *      - Used on SV covergroup or coverpoint scopes.
 *      - This is the option.detect_overlap of the object.
 *  PRINTMISSING: int
 *      - Used on SV covergroup or cross scopes.
 *      - This is the option.cross_num_print_missing of the object.
 *  STROBE: int (0|1)
 *      - Used on SV covergroup scopes.
 *      - This is the type_option.strobe of the object.
 *  CROSSERR: int (0|1)
 *      - Used on SV cross scopes.
 *      - When 1, indicates a cross type coverage calculation not supported by
 *        QuestaSim: namely, when crossed coverpoints are parameterized with
 *        different number of bins in different covergroup instances.
 *  DUSIGNATURE: string
 *      - MD5 signature string of a source design unit.
 *
 *  ==========================
 *  Attributes for assertions.
 *  ==========================
 *
 *  ACTION: int: 0 == continue, 1 == break, 2 == exit
 *      - Used on assertion objects.
 *      - This indicates the simulator action performed when an assertion
 *        fails.
 *  PROOFRADIUS: int: <negative> == none[blank], 0 >= radius value
 *      - Used on assertion objects.
 *      - This indicates the depth that formal proof went without errors
 *        before giving up.
 *
 *  ===================
 *  General attributes.
 *  ===================
 *
 *  T: binary: bit vector corresponding to tests
 *      - Used on bins and UCDB_TOGGLE coverage scope to indicate which tests
 *        caused an object to be covered.
 *      - Can also be accessed with ucdb_Get/SetBinTestMask().
 *
 *  MERGELEVEL: int: 1 == default, 2 == more info
 *      - Used with Questa merge files (note: merge algorithm not part of the
 *        UCDB API):
 *        1: default merge, test data is merged, the union of bins are merged,
 *           with integer counts incremented and vector counts ORed.
 *        2: tests are associated with most bins as a bit vector (see TESTS
 *           attribute above, and "Associating tests and bins" below)
 *           indicating what test caused them to be covered.  For vector bins,
 *           this means non-zero.  For UCDB_COVER scopes, this means cover
 *           count > at_least; for UCDB_ASSERT scopes, this means fail count >
 *           0; for UCDB_TOGGLE scopes, this means all bins covered (>0) except
 *           for UCDB_TOGGLE_ENUM types, where individual bins >0.
 *           Also: NUMSAMPLED attributes for UCDB_COVERGROUP and
 *           UCDB_COVERINSTANCE scopes are combined into a binary attribute
 *           called "SAMPLED" that is an array of as many integers as there are
 *           tests.
 *
 *  TAGCMD: string: UCDB_TESTPLAN scopes only, semicolon-separated arguments to
 *          Questa "coverage tag" command
 *      - This supports implicit tagging during merge, so as to associate test
 *        plans with coverage for test traceability
 *
 *  SECTION: string: UCDB_TESTPLAN scopes only, section number within test
 *           plan.
 *
 *  COV: float: any scope.  Used in some circumstances by coverage analysis to
 *       cache a computed total coverage number.
 *
 ****************************************************************************/

/*
 * The following macros are predefined keys for the attribute names above.
 */

/* history node attributes: */
#define UCDBKEY_FILENAME        "ORIGFILENAME"
#define UCDBKEY_CMDLINE         "TESTCMD"
#define UCDBKEY_RUNCWD          "RUNCWD"
#define UCDBKEY_CPUTIME         "CPUTIME"
#define UCDBKEY_HISTCOMMENT     "TESTCOMMENT"

/* unique test data attributes: */
#define UCDBKEY_SIMTIME         "SIMTIME"
#define UCDBKEY_TIMEUNIT        "TIMEUNIT"
#define UCDBKEY_DATE            "DATE"
#define UCDBKEY_SIMARGS         "VSIMARGS"
#define UCDBKEY_USERNAME        "USERNAME"
#define UCDBKEY_TESTSTATUS      "TESTSTATUS"
#define UCDBKEY_TESTNAME        "TESTNAME"
#define UCDBKEY_ACTFILENAME     UCDBKEY_FILENAME   /* backward compatibility */
#define UCDBKEY_SEED            "SEED"
/* The deprecated UCDBKEY_TESTCMD is replaced by UCDBKEY_CMDLINE */
#define UCDBKEY_TESTCMD         UCDBKEY_CMDLINE
/* The deprecated UCDBKEY_TESTCOMMENT is replaced by UCDBKEY_HISTCOMMENT */
#define UCDBKEY_TESTCOMMENT     UCDBKEY_HISTCOMMENT
#define UCDBKEY_COMPULSORY      "COMPULSORY"
#define UCDBKEY_HOSTNAME        "HOSTNAME"
#define UCDBKEY_HOSTOS          "HOSTOS"
#define UCDBKEY_WLFNAME         "WLFNAME"
#define UCDBKEY_LOGNAME         "LOGNAME"
#define UCDBKEY_MEMUSAGE        "MEMUSAGE"

/* unique test plan attributes: */
#define UCDBKEY_PATH            "PATH"
#define UCDBKEY_XMLSOURCE       "XMLSOURCE"
#define UCDBKEY_SIGNATURE       "SIGNATURE"

/* code coverage attributes: */
#define UCDBKEY_STATEMENT_INDEX "#SINDEX#"
#define UCDBKEY_START_LINENO    "#SLINENO#"
#define UCDBKEY_START_TOKNO     "#STOKNO#"
#define UCDBKEY_BRANCH_COUNT    "#BCOUNT#"
#define UCDBKEY_BRANCH_ISCASE   "#BTYPE#"
#define UCDBKEY_BRANCH_HASELSE  "#BHASELSE#"
#define UCDBKEY_EXPR_HEADERS    "#EHEADER#"
#define UCDBKEY_FSM_ID          "#FSMID#"
#define UCDBKEY_FSM_STATEVAL    "#FSTATEVAL#"
#define UCDBKEY_FSMCOND         "#FSMCOND#"
#define UCDBKEY_NUMFSMPROCESSES "#NFSMPROCS#"
#define UCDBKEY_FSMPROCESSES    "#FSMPROCS#"
#define UCDBKEY_FSMCLOCK        "#CLOCK#"

/*#define UCDBKEY_FECOPTION       "#FECOPTION#" */  /* deprecated */
#define UCDBKEY_FECSTR          "#FECSTR#"      /* deprecated */

/* covergroup attributes: */
#define UCDBKEY_BINRHSVALUE     "BINRHS"
#define UCDBKEY_GOAL            "#GOAL#"        /* used with other scopes */
#define UCDBKEY_ATLEAST         "ATLEAST"
#define UCDBKEY_COMMENT         "COMMENT"
#define UCDBKEY_AUTOBINMAX      "AUTOBINMAX"
#define UCDBKEY_DETECTOVERLAP   "DETECTOVERLAP"
#define UCDBKEY_NUMPRINTMISSING "PRINTMISSING"
#define UCDBKEY_STROBE          "STROBE"
#define UCDBKEY_PERINSTANCE     "PERINSTANCE"
#define UCDBKEY_GETINSTCOV      "GETINSTCOV"
#define UCDBKEY_MERGEINSTANCES  "MERGEINSTANCES"
#define UCDBKEY_CROSSERROR      "#CROSSERR#"
#define UCDBKEY_NUMSAMPLED      "NUMSAMPLED"    /* optional sample count for
                                                   covergroups */

/* cover and assertion directive memory profile attributes */
#define UCDBKEY_MEM_ASRTCURR   "MEM_ASSERT"         /* current memory */
#define UCDBKEY_MEM_ASRTPEAK   "PEAKMEM_ASRT"       /* peak memory */
#define UCDBKEY_CMLTTHREADS_ASRT "CMLTTHREADS_ASRT" /* cumulative threads */
#define UCDBKEY_MEM_PEAKTIME   "TIME_PEAKMEM"       /* time of peak */

/* assertion directive attributes */
#define UCDBKEY_ASSERT_ACTION   "#ACTION#"
#define UCDBKEY_ASSERT_PROOFRADIUS "PROOFRADIUS"
#define UCDBKEY_ASSERT_SEVERITY   "SEVERITY"

/* covergroup memory profile attributes */
#define UCDBKEY_MEM_CVGPERSIST  "PERSISTMEM_CVG"    /* persistent memory */
#define UCDBKEY_MEM_CVGTRANS    "TRANSMEM_CVG"      /* transient memory */
#define UCDBKEY_MEM_CVGTRANS_PEAK "TRANSPEAK_CVG"   /* transient peak */
#define UCDBKEY_MEM_CVGTRANS_PEAKTIME  UCDBKEY_MEM_PEAKTIME /* time of peak */

#define UCDBKEY_SAMPLES         "#SAMPLES#"     /* array of sample counts, for
                                                   level 2 merge */

/* miscellaneous: */
#define UCDBKEY_TESTVECTOR      "#"             /* used a lot, so concise */
#define UCDBKEY_MERGELEVEL      "MERGELEVEL"
#define UCDBKEY_TESTDATA_MERGED "MERGED"
#define UCDBKEY_TAGCMD          "TAGCMD"
#define UCDBKEY_SECTION         "#SECTION#"
#define UCDBKEY_DUSIGNATURE     "#DUSIGNATURE#"
#define UCDBKEY_MTICOVERAGE     "#COV#"
#define UCDBKEY_CLASSTYPE        "#CLASSTYPE#"    /* parameterized class
                                                         expanded name */

/*
 *  Some of the UCDB bin names are predefined to identify
 *  which count value is for a particular coveritem. These names
 *  will be the name of coveritems where they are applicable.
 */
#define UCDBBIN_BRANCH_T        "true_branch"   /* branch true bins */
#define UCDBBIN_BRANCH_IF       "if_branch"     /* branch if bins */
#define UCDBBIN_BRANCH_F        "false_branch"
#define UCDBBIN_BRANCH_E        "else_branch"   /* for "else" count */
#define UCDBBIN_BRANCH_AF       "all_false_branch" /* all false count,
                                                 when there is no "else" part */
#define UCDBBIN_TOGGLE_L        "toggle_low"    /* 2-state toggle bins */
#define UCDBBIN_TOGGLE_H        "toggle_high"
#define UCDBBIN_TOGGLE_EXT_H_L  "toggle_h_l"
#define UCDBBIN_TOGGLE_EXT_L_H  "toggle_l_h"    /* 3-state (extended) toggles */
#define UCDBBIN_TOGGLE_EXT_Z_L  "toggle_z_l"
#define UCDBBIN_TOGGLE_EXT_L_Z  "toggle_l_z"
#define UCDBBIN_TOGGLE_EXT_H_Z  "toggle_h_z"
#define UCDBBIN_TOGGLE_EXT_Z_H  "toggle_z_h"
#define UCDBBIN_EXPRCOND_UNKNOWN "unknown"      /* unknown value row */

/*
 *  Some of the UCDB scope names are hardcoded to distinguish between different
 *  natures of scopes.
 */
/*
 *  FEC vs. UDP expression/condition nodes:
 */
#define UCDBSCOPE_FEC           "FEC"           /* name of FEC scope */
#define UCDBSCOPE_UDP           "UDP"           /* name of UDP scope */


#ifndef DEFINE_UCDBT
#define DEFINE_UCDBT
typedef void* ucdbT;          /* generic handle to a UCDB */
#endif

typedef unsigned int ucdbSelectFlagsT;
/*
 * UCDB select flags:
 * The following flag values are to specify different objects types in various
 * routines, such as making clones, printing objects, etc.
 */
#define UCDB_SELECT_TAGS       0x0001 /* select scope tags */
#define UCDB_SELECT_ATTRS      0x0002 /* select user defined attributes */
#define UCDB_SELECT_COVERS     0x0004 /* select covers, does not work with copy
                                         in streaming modes */
#define UCDB_SELECT_FILETABS   0x0008 /* select file tables */
#define UCDB_SELECT_SOURCEINFO 0x0010 /* select source information: print only
                                       */


/* This flag can be used to select all flags above */
#define UCDB_SELECT_ALL      ((ucdbSelectFlagsT)(0xffffffff))


/*
 *  ucdb_Filename()
 *  Return file name from which UCDB was read, or most recent file name
 *  written.
 */
const char*
ucdb_Filename(
    ucdbT     db);

/*
 *  This is deprecated.
 */
typedef enum {
    UCDB_MODE_UDP,          /* default */
    UCDB_MODE_FEC
} ucdbExprCondModeT;

/*
 *  This function is deprecated
 */
void
ucdb_SetExprCondMode(
    ucdbExprCondModeT   mode);

/*
 *  This function is deprecated.
 */
ucdbExprCondModeT
ucdb_GetExprCondMode();

/*----------------------------------------------------------------------------
 *  Source File Information
 *
 *  Every UCDB object can potentially have a source file name stored with it.
 *  Different applications have different requirements for how these are
 *  stored, and the UCDB needs to be able to accommodate all of those.
 *  Consequently, the UCDB contains something called a "file handle".  This is
 *  a way of storing an indirect reference to the file name.
 *
 *  For individual coveritems, the UCDB never stores the file name itself, it
 *  stores a reference -- just a number, an offset into some table of file name
 *  strings that must reside elsewhere.  This is for space efficiency, while
 *  retaining the time efficiency of looking up file names.  The UCDB API is
 *  flexible enough that you can let the UCDB itself maintain a file name table
 *  for you -- or if you are exporting to a UCDB from an application that
 *  already has its own file name tables, you can efficiently transfer your own
 *  file name tables and your own offsets (file numbers) directly into the
 *  UCDB.
 *
 *
 *  Simple Use Models
 *
 *  If you don't care about file names and line numbers at all, you can create
 *  objects with NULL for the ucdbSourceInfoT argument, e.g.:
 *
 *      mycover = ucdb_CreateNextCover(db,parent,name,&coverdata,NULL);
 *
 *  If you care about file names but don't care how file names are stored, the
 *  simplest thing to do is create a file handle by name like so:
 *
 *      ucdbSourceInfoT sourceinfo;
 *      status = ucdb_CreateSrcFileHandleByName(db,
 *                                           &source_info.filehandle,
 *                                           NULL,
 *                                           filename,
 *                                           fileworkdir);
 *      source_info.line = myline;
 *      source_info.token = mytoken;
 *
 *      (void) ucdb_CreateNextCover(db,parent,name,&coverdata,&sourceinfo);
 *
 *  This will create a single global look-up table for file names within the
 *  UCDB.  File names will be stored efficiently for each object within the
 *  UCDB, and each unique file name string will be stored only once.
 *
 *  However file names are stored, you can always access the file name with
 *  code like this:
 *
 *      ucdbSourceInfoT sourceinfo;
 *      ucdb_GetCoverData(db,parent,i,&name,&coverdata,&sourceinfo);
 *
 *      if (ucdb_IsValidFileHandle(db,&sourceinfo.filehandle)) {
 *          printf("File name is %s\n",ucdb_GetFileName(db,
 *                                                   &sourceinfo.filehandle));
 *      }
 *
 *
 *  For Third-Party Applications with Existing File Name Tables
 *
 *  Some applications create their own tables of unique file names, and these
 *  tables may be associated with different objects in the design.  For
 *  example, there could be a file look-up table for each design unit.  In
 *  these cases, a UCDB user might like to assume that these tables are correct
 *  by design and transfer them directly into the UCDB through some
 *  corresponding UCDB object (e.g., a design unit scope.)  Then coverage
 *  objects would refer to a file name by the simple and efficient means of an
 *  integer offset in the associated file table.  Again, these would be assumed
 *  correct by construction and the integer values added to the UCDB directly.
 *
 *  In order to avoid complex look-up rules for what file table is valid in a
 *  particular context, the UCDB file handle concept makes the file table
 *  somewhat explicit: that is, the user must declare with which scope the file
 *  table is associated when creating a file handle.  This must be a scope
 *  which is accessible in read streaming or write streaming modes.  The rules
 *  are these:
 *
 *  -   The file table may be in the current scope.
 *  -   The file table may be in an ancestor of the current scope: that means
 *      parent (ucdb_ScopeParent), parent's parent, etc.
 *  -   The file table may be in a design unit.  The UCDB guarantees that file
 *      tables associated with design units are accessible in streaming modes.
 *
 *  By contrast, a sibling node
 *  (ucdb_NextSubScope(db,parent,myself,UCDB_ALL_SCOPES)) or child node
 *  (ucdb_NextSubScope(db,myself,NULL,UCDB_ALL_SCOPES)) would be illegal,
 *  because these nodes would not be available in streaming modes.  The same
 *  goes for "cousin" nodes or "nephew/niece" nodes, etc..
 *
 *  When an application has its own file tables, they must be transferred into
 *  the UCDB so it can know what file names are being used:
 *
 *      foreach entry in file name table:
 *          ucdb_SrcFileTableAppend(db,
 *                                  &new_file_handle,
 *                                  ucdb_scope_for_filetable,
 *                                  filename,
 *                                  fileworkdir);
 *
 *  If needed, file tables can be dumped with the ucdb_FileTableSize() and
 *  ucdb_FileTableName() functions.
 *
 *  To directly transfer file numbers into the UCDB, this technique can be
 *  used:
 *
 *      ucdbFileHandleT filehandle;
 *      ucdbSourceInfoT sourceinfo;
 *
 *      //
 *      // This filehandle retains a reference to the "current" file table.
 *      // Note that entry 0 is guaranteed to exist because file tables always
 *      // have at least 1 entry in them if they exist at all:
 *      //
 *      status = ucdb_CreateFileHandleByNum(db,
 *                                          &filehandle,
 *                                          scope_with_filetable,
 *                                          0);
 *
 *      //
 *      // Now you create a file handle with the file number (file table
 *      // offset) particular to the object being stored, while retaining the
 *      // previous reference to the "current" file table:
 *      //
 *      foreach coverage object:
 *          ucdb_CloneFileHandle(db,filehandle,
 *                               &sourceinfo.filehandle,
 *                               object.filenum);
 *          sourceinfo.line = object.linenum;
 *          sourceinfo.token = object.tokennum;
 *          ucdb_CreateNextCover(db,scope,name,&coverdata,&sourceinfo);
 *
 *  This scheme directly transfers file tables and file numbers (file table
 *  offsets) from the third-party tool into the UCDB.  It remains time
 *  efficient because no string-based look-up is ever done.  On retrieval, if
 *  you want access to the original file number, use ucdb_GetFileNum().  For
 *  access to the UCDB file table referenced by a file handle, use
 *  ucdb_GetFileTableScope().
 *
 *
 *  Note that because ucdbFileHandleT is defined as a struct, variables of type
 *  ucdbFileHandleT can be copied.  It is not recommended that the API user
 *  access the structure members directly, as the struct historys may change in
 *  the future for a yet more efficient implementation.  There are access
 *  functions for every type of operation to be done with file handles.
 *
 *---------------------------------------------------------------------------*/
typedef int ucdbFileTableT;
typedef void* ucdbScopeT;   /* scope handle */
typedef void* ucdbObjT;     /* either ucdbScopeT or ucdbHistoryNodeT */


/*
 *  Definition as a struct allows variables of this type to be copied and not
 *  require de-allocation, but exposes implementation.  NOTE this type
 *  definition may be changed in the future.
 */
typedef struct {
    ucdbFileTableT      table;      /* Cannot be used directly */
    int                 num;        /* Direct use is DISCOURAGED; see
                                       ucdb_GetFileNum() */
} ucdbFileHandleT;

/*
 *  Structure representing source information for database objects
 */
typedef struct {
    ucdbFileHandleT     filehandle;
    int                 line;
    int                 token;
} ucdbSourceInfoT;

/*
 *  ucdb_SrcFileTableAppend()
 *  Add a file name to a scope's file table or global file table and return a
 *  file handle corresponding to it.  Used for cases where the list of
 *  files is known to be unique.
 *  When the "filename" is absolute, "fileworkdir" is ignored.
 *  When the "filename" is relative, it is desirable to set "fileworkdir"
 *      to the directory path which it is relative to.
 *  Returns 0 for successful append, and -1 for error.
 *  NOTE: if you want to add files by name and check for duplicates, returning
 *  a file handle if the name already exists in the table, use
 *  ucdb_CreateSrcFileHandleByName().
 */
int
ucdb_SrcFileTableAppend(
    ucdbT               db,
    ucdbFileHandleT*    fileHandle,
    ucdbScopeT          scope,      /* NULL means global file table */
    const char*         filename,
    const char*         fileworkdir);

/*
 *  ucdb_FileTableAppend()  [DEPRECATED -- Please use ucdb_SrcFileTableAppend()]
 *  Add a file name to a scope's file table or global file table and return a
 *  file handle corresponding to it.  Used for cases where the list of files is
 *  known to be unique. Returns 0 for successful append, and -1 for error.
 *  NOTE: if you want to add files by name and check for duplicates, returning
 *  a file handle if the name already exists in the table, use
 *  ucdb_CreateSrcFileHandleByName().
 */
int
ucdb_FileTableAppend(
    ucdbT               db,
    ucdbFileHandleT*    filehandle,
    ucdbScopeT          scope,      /* NULL means global file table */
    const char*         filename);

/*
 *  ucdb_FileTableSize()
 *  Return number of files in the implied file table.
 */
int
ucdb_FileTableSize(
    ucdbT               db,
    ucdbScopeT          scope);     /* NULL means global file table */

/*
 *  ucdb_FileTableName()
 *  Return name of (index)th file in the file table.
 */
const char*
ucdb_FileTableName(
    ucdbT               db,
    ucdbScopeT          scope,      /* NULL means global file table */
    int                 index);

/*
 *  ucdb_CreateSrcFileHandleByName()
 *  Return a file handle given by file name, from the file table associated
 *  with the given scope.
 *  If filename is not found, it is added to the file table for the given
 *  scope. When the "filename" is absolute, "fileworkdir" is ignored.
 *  When the "filename" is relative, it is desirable to set "fileworkdir"
 *  to the directory path which it is relative to.
 *  ucdb_IsValidFileHandle(returnvalue) == 0 if error, e.g., if scope does not
 *  meet the criteria given in the block comments at the head of section.
 *  Returns 0 for when successful, and -1 if error.
 */
int
ucdb_CreateSrcFileHandleByName(
    ucdbT               db,
    ucdbFileHandleT*    filehandle,
    ucdbScopeT          scope,      /* NULL means global file table */
    const char*         filename,   /* File name to look up in table */
    const char*         fileworkdir);

/*
 *  ucdb_CreateFileHandleByName()
 *      [DEPRECATED -- Please use ucdb_CreateSrcFileHandleByName()]
 *  Return a file handle given by file name, from the file table associated
 *  with the given scope.
 *  If filename is not found, it is added to the file table for the given
 *  scope.
 *  ucdb_IsValidFileHandle(returnvalue) == 0 if error, e.g., if scope does not
 *  meet the criteria given in the block comments at the head of section.
 *  Returns 0 for when successful, and -1 if error.
 */
int
ucdb_CreateFileHandleByName(
    ucdbT               db,
    ucdbFileHandleT*    filehandle,
    ucdbScopeT          scope,      /* NULL means global file table */
    const char*         filename);  /* File name to look up in table */

/*
 *  ucdb_CreateFileHandleByNum()
 *  Return a file handle given by integer offset, from the file table
 *  associated with the given scope.
 *  If filenum is out of bounds or no file table exists, it returns -1, and
 *  ucdb_IsValidFileHandle(returnvalue) == 0 to indicate an error. Otherwise
 *  returns 0.
 */
int
ucdb_CreateFileHandleByNum(
    ucdbT               db,
    ucdbFileHandleT*    filehandle,
    ucdbScopeT          scope,      /* NULL means global file table */
    int                 filenum);

/*
 *  ucdb_CloneFileHandle()
 *  Return a file handle cloned from another, with a different file number.
 *  This must be used in cases where the file number is known to be in-bounds
 *  for the given file table. Returns 0 for success, -1 for error.
 */
int
ucdb_CloneFileHandle(
    ucdbT               db,
    ucdbFileHandleT*    newfilehandle,
    ucdbFileHandleT*    filehandle, /* uses file table implied by this one */
    int                 number);    /* new file number to use */

/*
 *  ucdb_CreateNullFileHandle()
 *  Create a new filehandle via the newfilehandle argument.
 *  Returns 0 for success, and -1 if error.
 *  ucdb_IsValidFileHandle(newfilehandle) == 0 always.
 */
int
ucdb_CreateNullFileHandle(
    ucdbFileHandleT* newfilehandle);


/*
 *  ucdb_IsValidFileHandle()
 *  Can be used to check the validity of a returned file handle, useful for
 *  non-callback-based error-checking.
 *  Return 1 if valid, 0 if not.
 */
int
ucdb_IsValidFileHandle(
    ucdbT               db,
    ucdbFileHandleT*    filehandle);

/*
 *  ucdb_GetFileName()
 *  Given a file handle, return the actual file name.
 *
 *  This follows a heuristic algorithm to try to reconstruct a valid file path
 *  from the file handle and the directory stored with it and with the UCDB.  A
 *  heuristic means it is not guaranteed to work, but it often does.  In the
 *  algorithm below, "filename" and "fileworkdir" refer to the accordingly
 *  named arguments given to either ucdb_CreateSrcFileHandleByName() or
 *  ucdb_SrcFileTableAppend().
 *
 *  if filename is an absolute path, that is returned.
 *  else (filename is a relative path):
 *      if filename exists at the relative path, return that.
 *      else if filename exists relative to fileworkdir, return that.
 *      else if filename exists relative to the value of the environment
 *          variable "MGC_WD" -- if used (commonly used with Questa) -- return
 *          that.
 *      else if filename exists relative to the directory from which the UCDB
 *          file was opened -- the directory extracted from the file given to
 *          ucdb_Open() or equivalent -- return that.
 *      else if filename exists relative to the directory extracted from the
 *          ORIGFILENAME attribute of the first test record -- representing the
 *          file into which the UCDB was originally saved -- return that.
 *      else return filename.
 *
 *  The assumption is that if the filename was originally created as an
 *  absolute path, it must be correct.  Note that Questa never creates a
 *  filename as an absolute path.  Otherwise only the last case indicates that
 *  the file was not found, and the original filename is returned for lack of
 *  anything better.
 *
 *  Note that if the deprecated functions ucdb_CreateFileHandleByName() or
 *  ucdb_FileTableAppend are used, the heuristic cannot work because
 *  fileworkdir is not specified.
 */
const char*
ucdb_GetFileName(
    ucdbT               db,
    ucdbFileHandleT*    filehandle);

/*
 *  ucdb_GetFileNum()
 *  Given a file handle, return the file number.
 *  While this can be accessed as file.num in the current implementation, this
 *  function is GUARANTEED to be supported in all future versions of the API.
 */
int
ucdb_GetFileNum(
    ucdbT               db,
    ucdbFileHandleT*    filehandle);

/*
 *  ucdb_GetFileTableScope()
 *  Return the scope whose file table is referenced by the file handle.  The
 *  file handle must be valid.
 *  If used on an invalid file handle, returns NULL and calls error handler if
 *  installed.
 *  Returns NULL for global file table, too -- so return value of NULL is not a
 *  guarantee of an error.
 */
ucdbScopeT
ucdb_GetFileTableScope(
    ucdbT               db,
    ucdbFileHandleT*    filehandle);

/*
 * ucdb_FileTableRemove()
 * This function removes an entry from the file table in the given
 * scope.
 * If filename is NULL then it removes the whole file table, if scope is
 * NULL then the filetable is global file table.
 * There is no effect of this function in streaming modes.
 * A successful operation will return 0, and -1 for error.
 */
int
ucdb_FileTableRemove(
    ucdbT               db,          /* database context */
    ucdbScopeT          scope,       /* scope or NULL */
    const char*         filename);   /* filename or NULL */

/*
 *  ucdb_FileInfoToString()
 *  Returns the file name for the file handle contained in the ucdbSourceInfoT
 *  argument.  This is equivalent to calling:
 *      ucdb_GetFileName(db,&source_info->filehandle)
 */
const char*
ucdb_FileInfoToString(
    ucdbT             db,
    ucdbSourceInfoT*  source_info);


/*------------------------------------------------------------------------------
 *  Error-handling
 *
 *  Most convenient error-handling mode is to use ucdb_RegisterErrorHandler()
 *  before any UCDB calls.  The user's error callback, a function pointer of
 *  type ucdb_ErrorHandler, is called for any errors produced by the system.
 *
 *  Alternatively, function return values can be checked.  In general,
 *  functions that return a handle will return NULL (or invalid handle) on
 *  error, the handle otherwise.  Functions that return an int will return
 *  non-zero on error, 0 otherwise.  This description is not repeated for every
 *  function below.
 *
 *----------------------------------------------------------------------------*/
typedef enum {
    UCDB_MSG_INFO,
    UCDB_MSG_WARNING,
    UCDB_MSG_ERROR
} ucdbMsgSeverityT;

typedef struct ucdbErr_s {
    int msgno;                   /* Message identifier */
    ucdbMsgSeverityT severity;   /* Message severity */
    const char* msgstr;          /* Raw message string */
} ucdbErrorT;

typedef void (*ucdb_ErrorHandler) (void* userdata, ucdbErrorT* errdata);

/*
 *  ucdb_RegisterErrorHandler()
 *  The registered function, if set, will be called for all API errors.
 */
void
ucdb_RegisterErrorHandler(
    ucdb_ErrorHandler errHandle,
    void*             userdata);

/*
 * ucdb_IsModified()
 * Indicates whether the database handle is modified after loading the database
 * in memory. Returns 1 if the database is modified, otherwise returns 0.
 */
int
ucdb_IsModified(
    ucdbT db);

/*
 * ucdb_ModifiedSinceSim()
 * Indicates whether the database has ever been modified since it was saved
 * from the simulation. In case of merging databases, if all the input
 * databases are unmodified then the merge output will be marked as unmodified,
 * otherwise if any one or more input files are modified then the output
 * database will be marked as modified. Returns 1 if the database is modified,
 * otherwise returns 0.
 */
int
ucdb_ModifiedSinceSim(
    ucdbT db);

/*
 * ucdb_SuppressModified()
 * Ignores marking database as modified for any change in database if this
 * function is called with the second argument yes=1 prior to the change.
 * Another call to this function with yes=0 will enable marking the modified
 * flag. It suppresses both the in-memory modified flag and the modified since
 * simulation flag, so both the functions ucdb_IsModified() and
 * ucdb_ModifiedSinceSim() will return 0 if the change is made in suppressed
 * mode.
 */
void
ucdb_SuppressModified(
    ucdbT db,
    int yes);

/* #########################################################################
 * ##### HISTORYNODE -- begin
 * ######################################################################### */

typedef void* ucdbHistoryNodeT;

/*
 * History node kinds.
 */
typedef enum {
    UCDB_HISTORYNODE_NONE        /* no node or error */
                                 = 0x00000000,
    UCDB_HISTORYNODE_MERGE       /* interior merge node */
                                 = (int)0xfeedbeef,
    UCDB_HISTORYNODE_TEST        /* test leaf node */
                                 = (int)0xdeaffeed,
    UCDB_HISTORYNODE_TESTPLAN    /* test plan leaf node */
                                 = (int)0xdeadbeef
} ucdbHistoryNodeKindEnumT;

/*
 *  ucdb_CreateHistoryNode()
 *  Create a HistoryNode handle of the indicated kind
 *  linked into the database db.
 *  Returns NULL for error or the history node already exists.
 *
 *  Attributes:
 *      This routine creates the node with
 *      default values for the following
 *      attributes common to all history nodes:
 *
 *          FILENAME:  path
 *          RUNCWD:    -the current execution directory-
 *
 *  Note:
 *    "path" must always be a valid pathname (i.e. never NULL).
 *    When ("kind" == UCDB_HISTORYNODE_MERGE)
 *        "path" should be the UCDB mergefile pathname.
 *    When ("kind" == UCDB_HISTORYNODE_TEST)
 *        "path" should be the UCDB file pathname.
 *    When ("kind" == UCDB_HISTORYNODE_TESTPLAN)
 *        "path" should be the UCDB file pathname.
 *
 *  Note:
 *      The returned value, a node, is owned by the routine
 *      and as such should never be freed by the caller.
 */
ucdbHistoryNodeT
ucdb_CreateHistoryNode(
    ucdbT                    db,
    char*                    path, /* never NULL */
    ucdbHistoryNodeKindEnumT kind);

/*
 *  ucdb_NextHistoryNode()
 *  If the input HistoryNode handle is NULL
 *    return the first HistoryNode handle
 *    whose kind is indicated by "kind".
 *  otherwise
 *    return the next HistoryNode handle
 *    whose kind is the same as "historynode".
 *  Returns NULL if there is no next HistoryNode.
 *
 *  Note:
 *      The returned value, a node, is owned by the routine
 *      and as such should never be freed by the caller.
 */
ucdbHistoryNodeT
ucdb_NextHistoryNode(
    ucdbT                    db,
    ucdbHistoryNodeT         historynode, /* NULL to get the first one */
    ucdbHistoryNodeKindEnumT kind);

/*
 *  ucdb_NextHistoryRoot()
 *  If the input HistoryNode handle is NULL
 *    return the first HistoryNode handle
 *    whose kind is indicated by "kind"
 *    and has no parent.
 *  otherwise
 *    return the next HistoryNode handle
 *    whose kind is the same as "historynode"
 *    and has no parent.
 *  Returns NULL if there is no next HistoryNode
 *    that has no parent.
 *
 *  Note:
 *    This routine assumes that there may be more that one history root
 *    (i.e. a collection of trees, subtree orphans).
 *
 *  Note:
 *      The returned value, a node, is owned by the routine
 *      and as such should never be freed by the caller.
 */
ucdbHistoryNodeT
ucdb_NextHistoryRoot(
    ucdbT                    db,
    ucdbHistoryNodeT         historyroot, /* NULL to get the first root */
    ucdbHistoryNodeKindEnumT kind);

/*
 *  ucdb_HistoryRoot()
 *
 *  Return the unique history node that has no parent
 *  (i.e. the unique history tree root).
 *  If an error occurs or there is more than one root, return NULL.
 *  This routine assumes that there is only one history root.
 *
 *  Note:
 *      The returned value, a node, is owned by the routine
 *      and as such should never be freed by the caller.
 */
ucdbHistoryNodeT
ucdb_HistoryRoot(ucdbT db);

/*
 *  ucdb_NextHistoryLookup()
 *  If the input HistoryNode handle is NULL
 *    return the first HistoryNode handle
 *    whose kind is indicated by "kind"
 *    and has an attribute with the indicated key and indicated value.
 *  otherwise
 *    return the next HistoryNode handle
 *    whose kind is the same as "historynode"
 *    and has an attribute with the indicated key and indicated value.
 *  Returns NULL if there is no next HistoryNode
 *    as indicated.
 *
 *  Note:
 *      The attribute must be a UCDB_ATTR_STRING attribute.
 *
 *  Note:
 *      The returned value, a node, is owned by the routine
 *      and as such should never be freed by the caller.
 */
ucdbHistoryNodeT
ucdb_NextHistoryLookup(
    ucdbT                    db,
    ucdbHistoryNodeT         historynode, /* NULL to get the first node */
    const char*              attrkey,
    const char*              attrvalue,
    ucdbHistoryNodeKindEnumT kind);

/*
 *  ucdb_GetHistoryNodeParent()
 *  Return the HistoryNode parent.
 *  Returns NULL when no parent (i.e. history tree root node).
 *
 *  Note:
 *      The returned value, a node, is owned by the routine
 *      and as such should never be freed by the caller.
 */
ucdbHistoryNodeT
ucdb_GetHistoryNodeParent(
    ucdbT                     db,
    ucdbHistoryNodeT          childnode);

/*
 *  ucdb_GetNextHistoryNodeChild()
 *  Return the next HistoryNode child.
 *  Returns NULL when no next child.
 *
 *  Note:
 *      The returned value, a node, is owned by the routine
 *      and as such should never be freed by the caller.
 */
ucdbHistoryNodeT
ucdb_GetNextHistoryNodeChild(
    ucdbT                     db,
    ucdbHistoryNodeT          parentnode, /* HistoryNode handle */
    ucdbHistoryNodeT          childnode); /* NULL to get the first one */

/*
 *  ucdb_AddHistoryNodeChild()
 *  Set HistoryNode child.
 *  Returns 0 with any error, non-zero with success.
 *
 *  Note: Every child node may have at most one parent.
 *        Once this routine assigns a parent to a child
 *        node, it may never be reassigned to a different
 *        parent. This is to say, any particular node
 *        may only be given to the ucdb_AddHistoryNodeChild
 *        routine as a childnode once, and only once.
 *
 *        Likewise, recursion is not allowed. A childnode
 *        may not be its own parent
 *        (neither, directly nor indirectly).
 *
 *        Simply put, any history node appears once, and only once,
 *        in the history trees.
 */
int
ucdb_AddHistoryNodeChild(
    ucdbT                    db,
    ucdbHistoryNodeT         parentnode, /* HistoryNode handle */
    ucdbHistoryNodeT         childnode); /* child node */

/*
 *  ucdb_CalculateHistorySignature()
 *
 *  Computes the history signature for the "file".
 *  Returns NULL if there is an error.
 *
 *  Given a valid filepath, this routine calculates a signature
 *  for that file. Recalculating this signature on the same file
 *  shall always produce the same results as long as the file
 *  contents remain unmodified. If ever the file is changed/modified
 *  the resulting signature will also be changed.
 *
 *  This allows for efficient checking if a file has become "dirty".
 *
 *  Note:
 *      The returned value, a string, is owned by the routine
 *      and as such should never be freed by the caller.
 */
char*
ucdb_CalculateHistorySignature(
    ucdbT                    db,
    char*                    file);

/*
 *  ucdb_CloneHistoryNode
 *
 *  This function creates an exact copy of the given history node.
 *  The attributes of the history node are also cloned.
 *  A successful operation will return the history node handle,
 *  and NULL for error or the history node already exists.
 */
ucdbHistoryNodeT
ucdb_CloneHistoryNode(
    ucdbT            targetdb,    /* database where the clone will be created */
    ucdbT            sourcedb,    /* database where the clone is copied from  */
    ucdbHistoryNodeT historynode);/* source history node */

/*
 *    ucdb_GetHistoryKind (alias ucdb_GetObjType)
 *
 *  Returns UCDB_SCOPE_ERROR if error.
 *  Returns UCDB_HISTORYNODE_TEST when obj is a test data record.
 *  Returns UCDB_HISTORYNODE_TESTPLAN when obj is a testplan record.
 *  Returns UCDB_HISTORYNODE_MERGE when obj is a merge record.
 *  Otherwise, returns the scope type ucdbScopeTypeT:
 *      [See ucdbScopeTypeT ucdb_GetScopeType(ucdbT db, ucdbScopeT scope)]
 *
 *    This is a polymorphic function for acquiring an object type.
 *    IMPORTANT NOTE: this may return multiple bits set (specifically
 *    for history data objects). The return value MUST NOT be used as a mask.
 */
#define ucdb_GetHistoryKind(db,obj) (ucdbHistoryNodeKindEnumT)ucdb_GetObjType(db,obj)

/* #########################################################################
 * ##### HISTORYNODE -- end
 * ######################################################################### */

/*------------------------------------------------------------------------------
 *  Test management
 *
 *  A UCDB may have a single test data record associated with it, if it was
 *  created as a result of a single run.  If created as a result of a merge,
 *  the UCDB should have multiple sets of test data.
 *
 *  The following routines allow creation of a set of test data.  Each test
 *  data record should be associated with the name of the UCDB file into which
 *  it was first stored.
 *
 *----------------------------------------------------------------------------*/
typedef ucdbHistoryNodeT ucdbTestT;
typedef enum {
    UCDB_TESTSTATUS_OK,
    UCDB_TESTSTATUS_WARNING,        /* test warning ($warning called) */
    UCDB_TESTSTATUS_ERROR,          /* test error ($error called) */
    UCDB_TESTSTATUS_FATAL,          /* fatal test error ($fatal called) */
    UCDB_TESTSTATUS_MISSING,        /* test not run yet */
    UCDB_TESTSTATUS_MERGE_ERROR     /* testdata record was merged with
                                       inconsistent data values */
} ucdbTestStatusT;

/*
 *  ucdb_AddTest()
 *  Add the given arguments to a test in the database.
 *  Returns the new test handle, or NULL with error.
 *  Note: to use reliably, "filename" must be the name of the file that will be
 *  later saved.  This is guaranteed when saved out of QuestaSim.  The filename
 *  is given explicitly to aid in copying test data records
 *  Note: in the comments, the corresponding attribute name is given for each
 *  parameter of this function.
 */
ucdbTestT
ucdb_AddTest(
    ucdbT           db,             /* database object */
    const char*     filename,       /* ORIGFILENAME: name of UCDB file to which
                                       the database was originally saved */
    const char*     testname,       /* TESTNAME: name of test, an identifier
                                       that must be unique for each distinct
                                       test run */
    ucdbTestStatusT test_status,    /* TESTSTATUS: test status */
    double          simtime,        /* SIMTIME: simulation time real number */
    const char*     simtime_units,  /* TIMEUNIT: "ns", "us", etc. */
    double          realtime,       /* CPUTIME: CPU time */
    const char*     seed,           /* SEED: randomization seed */
    const char*     command,        /* CMDLINE: arguments for test script */
    const char*     simargs,        /* VSIMARGS: arguments to simulator */
    const char*     comment,        /* HISTCOMMENT: comment for test */
    int             compulsory,     /* COMPULSORY: required test? 1 or 0 */
    const char*     date,           /* DATE: date as a string, see above */
    const char*     userid);        /* USERNAME: id of user who created file */

/*
 *  ucdb_AddPotentialTest()
 *
 *  This creates a test data record with a test name only.
 *  It returns "UCDB_TESTSTATUS_MISSING" for test_status.
 *  This kind of test record has invalid values for all other fields.
 *  Returns the new test handle, or NULL with error.
 *  Used to tag a test data record for tests not yet run.
 */
ucdbTestT
ucdb_AddPotentialTest(
    ucdbT           db,             /* database object */
    const char*     testname);      /* TESTNAME: name of test, see above */

/*
 *  ucdb_GetTestData()
 *  Given a handle, get data about the test.  Returns non-zero with error.
 *  Allocated values (strings, date, and attributes) must be copied if the user
 *  wants them to persist.
 *  See comments for ucdb_AddTest() for descriptions of arguments and
 *  corresponding attribute name.
 */
int
ucdb_GetTestData(
    ucdbT           db,
    ucdbTestT       test,
    const char**    filename,
    const char**    testname,
    ucdbTestStatusT*test_status,
    double*         simtime,
    const char**    simtime_units,
    double*         cputime,
    const char**    seed,
    const char**    command,
    const char**    simargs,
    const char**    comment,
    int*            compulsory,
    const char**    date,
    const char**    userid);

/*
 *  ucdb_GetTestName()
 *  Given a test handle, return the test name.
 *  Returns NULL with error.
 */
const char*
ucdb_GetTestName(
    ucdbT           db,
    ucdbTestT       test);

/*
 *  ucdb_NextTest
 *  Get the next test handle from the opened database. If the test is NULL then
 *  it returns the first test handle.
 *  Returns NULL with error.
 */
ucdbTestT
ucdb_NextTest(
    ucdbT           db,
    ucdbTestT       test);

/*
 *  ucdb_CloneTest()
 *  This function creates an exact copy of the given test record.
 *  There is no effect of this function when targetdb is in
 *  streaming mode.
 *  A successful operation will return the test handle, and NULL for error.
 */
ucdbTestT
ucdb_CloneTest(
    ucdbT           targetdb,     /* database where the clone will be created */
    ucdbTestT       test,         /* source test data */
    ucdbSelectFlagsT cloneflags); /* either UCDB_CLONE_ATTRS or 0 */

/*
 *  ucdb_RemoveTest()
 *  This function removes the given test from the database.
 *  There is no effect of this function in streaming modes.
 *  A successful operation will return 0, and -1 otherwise
 *  NOTE: This function should be used carefully if it is
 *  used during iteration of tests, otherwise the iteration
 *  may not be complete.
 */
int
ucdb_RemoveTest(
    ucdbT           db,
    ucdbTestT       test);  /* test to remove */

/*
 *  ucdb_NumTests()
 *  Return the number of tests that are associated with this database.
 *  Most reliable with "in-memory" mode; works in streaming modes, but only
 *  after all test records have been read or written.
 *  Returns -1 if value cannot be calculated yet in streaming modes, otherwise
 *  number of tests.
 */
int
ucdb_NumTests(
    ucdbT           db);


/*------------------------------------------------------------------------------
 *  Database creation and file management
 *
 *  The database exists in two forms potentially: an in-memory image accessible
 *  with a database handle, and a persistent form on the filesystem.  There are
 *  "read streaming" and "write streaming" modes that minimize the memory usage
 *  in the current process.  The streaming modes keep only a small "window" of
 *  data in memory, and once you have moved onward in reading or writing, you
 *  cannot revisit earlier parts of the database; random access is not
 *  possible.
 *
 *  Opening a file, creating an in-memory image
 *
 *  Reading from a persistent database and creating an in-memory image are
 *  combined in the same function: ucdb_Open(), which always creates a valid
 *  database handle.  If a filename is given to ucdb_Open(), the in-memory
 *  image is populated from the persistent database in the named file.
 *
 *  Note on constant-time access to summary statistics:
 *
 *  From Questa 6.3d onward, some parts of the data model can be accessed
 *  without fully populating the in-memory data image, if and only if no other
 *  calls have been made since ucdb_Open() that require accessing the in-memory
 *  image.  This allows some data to be accessed in constant time regardless of
 *  the size of the UCDB:
 *      * ucdb_CalcCoverageSummary with scope==NULL and test_mask==NULL
 *      * ucdb_GetCoverage
 *      * ucdb_GetStatistics
 *      * ucdb_GetMemoryStats
 *
 *  Writing to a file from an in-memory image
 *
 *  This may be done at any time with the ucdb_Write() function.  This
 *  transfers all of or a subset of the in-memory image to the named persistent
 *  database file, overwriting the file if it previously existed.
 *
 *  Deleting the in-memory image
 *
 *  This is done with the ucdb_Close() function.  After this, the database
 *  handle is no longer valid.
 *
 *  Using write streaming mode
 *
 *  If wanting to create a UCDB with minimal memory overhead, create a UCDB
 *  handle with ucdb_OpenWriteStream().  This creates a UCDB handle whose use
 *  is restricted.  In particular, there is a prescribed order in which objects
 *  must be created:
 *      * Create UCDB attributes first.
 *        Note: creation of UCDB attributes at the beginning of the file is not
 *        enforced; this allows the case of UCDB attributes created at the end
 *        of the output -- which might be necessary for attributes whose values
 *        must be computed as a result of traversing the data during write.
 *      * Create TestData.
 *      * Create scopes, creating DU scopes before corresponding instance
 *        scopes.
 *      * If a scope contains coverage items, create those first.
 *      * If a scope contains child scopes, create those after coveritems.
 *  There are other restrictions as well; see comments for individual
 *  functions, below.  For example, accessing immediate ancestors is OK, but
 *  accessing siblings is not (nor is it OK to access an ancestor's siblings.)
 *  Furthermore, the function ucdb_WriteStream() must be used -- and may only be
 *  used -- in write streaming mode to finish writing a particular object, and
 *  ucdb_WriteStreamScope() used to finish writing a scope and resume writing
 *  the parent scope.
 *  In write streaming mode, the ucdb_Close() function must be used to finish
 *  the file being written to and free any temporary memory used for the
 *  database handle.
 *
 *  Using read streaming mode
 *
 *  The read streaming mode operates with callbacks.  The persistent database
 *  is opened with the ucdb_OpenReadStream() call, and control is surrendered
 *  to the UCDB system which will initiate callbacks to the given callback
 *  function.  Along with each callback is given a "reason" (the data which is
 *  valid for this particular callback) and enough information to access the
 *  corresponding data.
 *
 *  Notes on read streaming callback order:
 *
 *      * INITDB is always the first callback.
 *        UCDB attributes created first in write streaming mode are available,
 *        as are UCDB attributes created with in-memory mode.
 *      * all TEST callbacks follow; after the next non-TEST callback
 *        there will be no more TEST callbacks.
 *      * DU callbacks must precede their first associated instance SCOPE
 *        callbacks, but need not immediately precede them.
 *      * SCOPE and DU and CVBIN callbacks can occur in any order
 *        (excepting the DU before first instance rule) -- though
 *        nesting level is implied by the order of callbacks.
 *      * ENDSCOPE callbacks correspond to SCOPE and DU callbacks and
 *        imply a "pop" in the nesting of scopes and design units.
 *      * ENDDB callbacks can be used to access UCDB attributes written at the
 *        end of the file, if created in write streaming modes.
 *
 *----------------------------------------------------------------------------*/

/*
 *  ucdb_Open()
 *  Create an in-memory database, optionally populating it from the given file.
 *  Returns a handle with success, NULL with failure.
 *
 *  Note on efficiency:
 *  Starting with Questa 6.3d,
 *
ucdbT
ucdb_Open(
    const char*     name        // file system path
);
 */
#define ucdb_Open(name) ucdb_OpenV(name,UCDB_H_VERSION)
ucdbT
ucdb_OpenV(
    const char*,int);


/*
 *  Opening UCDB in streaming mode to read data through callbacks without
 *  creating an in-memory database.
 *
 *  Use the ucdb_OpenReadStream() read API to open UCDB in stream mode with a
 *  callback function of type ucdb_CBFuncT along with user data (which can be
 *  NULL). The callback function will be called for all UCDB objects present in
 *  the database, with an object of type ucdbCBDataT, along with the user data.
 */

/* Enum type for different callback reasons */
typedef enum {
    UCDB_REASON_INITDB,      /* Start of the database, apply initial settings */
    UCDB_REASON_DU,          /* Start of a design unit scope */
    UCDB_REASON_TEST,        /* (DEPRECATED): Testdata history object */
    UCDB_REASON_SCOPE,       /* Start of a scope object */
    UCDB_REASON_CVBIN,       /* Cover item */
    UCDB_REASON_ENDSCOPE,    /* End of a scope, including design units */
    UCDB_REASON_ENDDB,       /* End of database (database handle still valid) */
    UCDB_REASON_PLANHISTORY, /* Testplan history object */
    UCDB_REASON_MERGEHISTORY /* Merge history object */
} ucdbCBReasonT;
#define UCDB_REASON_TESTHISTORY UCDB_REASON_TEST

/* Enum type for return type for of ucdb_CBFuncT function */
typedef enum {
    UCDB_SCAN_CONTINUE = -1,    /* Continue to scan ucdb file */
    UCDB_SCAN_STOP = -2,        /* Stop scanning ucdb file */
    UCDB_SCAN_PRUNE = -3        /* Prune the scanning of the ucdb file at this
                                 * node. Scanning continues but ignores
                                 * processing of this node's children.
                                 * NOTE: This enum value is currently
                                 *       disallowed in read streaming mode.
                                 */
} ucdbCBReturnT;

/* Data type for read callback */
typedef struct ucdbCBDataS {
    ucdbCBReasonT reason;       /* Reason for this callback */
    ucdbT         db;           /* Database handle, to use in APIs */
    ucdbObjT      obj;          /* ucdbScopeT or ucdbHistoryNodeT */
    int           coverindex;   /* if UCDB_REASON_CVBIN, index of coveritem */
} ucdbCBDataT;

/* Function type to use in the ucdb_OpenReadStream() read API */
typedef ucdbCBReturnT (*ucdb_CBFuncT) (void* userdata, ucdbCBDataT* cbdata);

/*
 *  ucdb_OpenReadStream()
 *  Open database for streaming read mode.
 *  Returns 0 with success, -1 with failure.
 *
int
ucdb_OpenReadStream(
    const char*  name,      // file system path
    ucdb_CBFuncT cbfunc,
    void*        userdata);
 */

#define ucdb_OpenReadStream(name,cbfunc,userdata) \
        ucdb_OpenReadStreamV(name,cbfunc,userdata,UCDB_H_VERSION)
int
ucdb_OpenReadStreamV(
    const char*,
    ucdb_CBFuncT,
    void*,
    int);


/*
 *  ucdb_OpenWriteStream()
 *  Open data in write streaming mode.  See comments in general discussion
 *  above about restrictions on write streaming mode.
 *  Note that file system path will be overwritten if it contains existing
 *  data; write permissions must exist.
 *  Returns a restricted database handle with success, NULL with error.
 *
ucdbT
ucdb_OpenWriteStream(
    const char* name);      // file system path
 */

#define ucdb_OpenWriteStream(name) ucdb_OpenWriteStreamV(name,UCDB_H_VERSION)
ucdbT
ucdb_OpenWriteStreamV(
    const char*,int);

/*
 *  ucdb_WriteStream()
 *  Finishes a write of current object to the persistent database file in
 *  write streaming mode.
 *  Note: this operation is like a "flush", just completing the write of
 *  whatever was most recently created in write streaming mode.  In particular,
 *  there is no harm in doing multiple ucdb_WriteStream() calls, because if the
 *  current object has already been written, it will not be written again.
 *  The database handle "db" must have been previously opened with
 *  ucdb_OpenWriteStream().
 *  UCDB_WRITESTREAMING mode. Returns 0 for success, and -1 for any error.
 */
int
ucdb_WriteStream(           /* Temp Note: was ucdb_EndCreate() */
    ucdbT       db);

/*
 *  ucdb_WriteStreamScope()
 *  Similar to ucdb_WriteStream, except that it finishes the current scope and
 *  "pops" the stream to the parent scope.  Objects created after this belong
 *  to the parent scope of the scope just ended.
 *  Note: this always performs the "pop", i.e., the termination of the current
 *  scope and reversion to its parent.  Otherwise it is also like the "flush"
 *  operation of ucdb_WriteStream().  The crucial difference is that
 *  ucdb_WriteStreamScope() cannot benignly be called multiple times; it will
 *  always cause a reversion to the parent scope.  This is the exact write
 *  streaming analogue of the UCDB_REASON_ENDSCOPE callback in read streaming
 *  mode.
 *  The database handle "db" must have been previously opened with
 *  ucdb_OpenWriteStream().
 *  Returns 0 for success, and -1 for any error.
 */
int
ucdb_WriteStreamScope(      /* Temp Note: was ucdb_WriteEndscope */
    ucdbT       db);

/*
 *  ucdb_Write()
 *  Copy in-memory database or a subset of the in-memory database to a
 *  persistent form stored in the given file name.
 *  Use the coverflags argument to select coverage types to be saved, use -1
 *  to save everything.
 *  Note that file system path will be overwritten if it contains existing
 *  data; write permissions must exist.
 *  The database handle "db" cannot have been opened for one of the streaming
 *  modes.
 *  Returns 0 for success, and -1 for any error.
 */
int
ucdb_Write(
    ucdbT       db,
    const char* file,
    ucdbScopeT  scope,      /* write objects under given scope, write all
                               objects if scope==NULL */
    int         recurse,    /* if true, recurse under given scope, ignored if
                               scope==NULL */
    /* ucdbCoverTypeT: */
    int         covertype); /* selects coverage types to save */

/*
 *  ucdb_Close()
 *  Invalidate the database handle.  Frees all memory associated with the
 *  database handle, including the in-memory image of the database if not in
 *  one of the streaming modes.  If opened with ucdb_OpenWriteStream(), this
 *  also has the side-effect of closing the output file.
 *  Returns 0 with success, non-zero with failure.
 */
int
ucdb_Close(
    ucdbT       db);

/*
 *  ucdb_DBVersion()
 *  Return version of API library, an integer.
 *  If the database handle was created from a file -- ucdb_Open() with non-NULL
 *  filename, or ucdb_OpenReadStream() -- this returns the version of the
 *  database file itself: that is, the version of the API that created the file
 *  originally.
 *  Otherwise -- ucdb_Open() with NULL filename, or ucdb_OpenWriteStream() --
 *  this is the same as ucdb_APIVersion().
 *  Negative value indicates an error condition.
 */
int
ucdb_DBVersion(
    ucdbT           db);

/*
 *  ucdb_APIVersion()
 *  Return version of API library.
 *  In general, ucdb_APIVersion() >= ucdb_GetVersion(db) in order for the file
 *  to be read.
 */
int
ucdb_APIVersion(void);

/*
 *  ucdb_SetPathSeparator()
 *  ucdb_GetPathSeparator()
 *  Set or get path separator used with the UCDB.  This has relevance for the
 *  following routines:
 *  -   ucdb_MatchScopeByPath
 *  -   ucdb_MatchCoverByPath
 *  -   ucdb_GetScopeHierName
 *  -   ucdb_MatchCallBack
 *  The path separator is associated with the database, different databases may
 *  have different path separators; the path separator is stored with the
 *  persistent form of the database.
 *  ucdb_SetPathSeparator routine returns -1 with error, and returns 0 if OK.
 *  ucdb_GetPathSeparator routine returns null character with error.
 */
int
ucdb_SetPathSeparator(
    ucdbT           db,
    char            separator);

char
ucdb_GetPathSeparator(
    ucdbT           db);

/* #########################################################################
 * ##### USER ATTRIBUTES -- begin
 * ######################################################################### */

/*-----------------------------------------------------------------------------
 *  User-defined attributes
 *
 *  This is a simple set of facilities for providing user-defined attributes
 *  associated with objects in the database -- scopes, coveritems, or tests --
 *  or with the database itself (global attributes).  User-defined attributes
 *  are key-value pairs that may be traversed or looked up by key.
 *
 *  Note on memory management: on reading or writing, values returned are always
 *  ownwd by the API.  They are good until the next call. The memory for keys
 *  is always good.
 *
 *  Note on index given to attribute access functions:
 *
 *  Coveritems are identified by a combination of the parent scope handle
 *  (pointer) and an integer index for the coveritem.  In order to use the
 *  attribute functions for a scope only, the integer index must be set to -1.
 *  For history node objects, the index must always be -1.
 *
 *  When the functions are given an attribute handle, if that handle is of type
 *  UCDB_ATTR_ARRAY, then the index must be a value from 0 to the array size -
 *  1.  The array size may be queried using the ucdb_AttrArraySize() function.
 *  
 *  If the attribute handle is of type UCDB_ATTR_HANDLE, then the index must be
 *  -1.
 *
 *  Deprecated functions:
 *
 *  ucdb_AttrMatch()        did not copy attribute values
 *  ucdb_AttrNext()         did not copy attribute values
 *  
 *  
 *  Example A.
 *  Create an attribute array:
 *  "NAMES",0    -> "bob"
 *  "NAMES",1    -> "fred"
 *
 *  // A1. Create an attribute array handle
 *  ucdbAttrValueT names_array;
 *  names_array.type = UCDB_ATTR_ARRAY;
 *  ucdb_AttrAdd(db,scope,-1,"NAMES",&names_array);
 *
 *  // A2. Use handle (set by API) to create string attribute 0
 *  ucdbAttrValueT name;
 *  name.type = UCDB_ATTR_STRING;
 *  name.u.svalue = "bob";
 *  ucdb_AttrAdd(db,names_array.u.attrhandle,0,NULL,&name);
 *  
 *  // A3. Use handle (set by API) to create string attribute 1
 *  name.type = UCDB_ATTR_STRING;
 *  name.u.svalue = "fred";
 *  ucdb_AttrAdd(db,names_array.u.attrhandle,1,NULL,&name);
 *
 *  // A4. Read attribute array
 *  ucdb_AttrGet(db,scope,-1,"NAMES",&names_array);
 *  if (names_array.type==UCDB_ATTR_ARRAY) {
 *      int i;
 *      for ( i=0; i<ucdb_AttrArraySize(db,names_array.u.attrhandle); i++ ) {
 *          // Note how key is NULL:
 *          ucdb_AttrGet(db,names_array.u.attrhandle,i,NULL,&name);
 *          printf("NAMES[%i] = %s\n",i,
 *                 name.u.svalue);
 *      }
 *  }
 *
 *
 *  Example B.
 *  Create a single attribute that has both an array and other data
 *  "MYDATA" -> "ADDRESS" -> "home"
 *           -> "NAMES",0 -> "bob"
 *           -> "NAMES",1 -> "fred"
 *
 *  // B1. Create attribute handle
 *  ucdbAttrValueT mydata;
 *  mydata.type = UCDB_ATTR_HANDLE;
 *  ucdb_AttrAdd(db,scope,-1,"MYDATA",&mydata);
 *
 *  // B2. Create "ADDRESS" attribute of attribute
 *  ucdbAttrValueT field;
 *  field.type = UCDB_ATTR_STRING;
 *  field.u.svalue = "home";
 *  ucdb_AttrAdd(db,mydata.u.attrhandle,-1,"ADDRESS",&field);
 *
 *  // B3. Create an attribute array handle: almost same as A1.
 *  names_array.type = UCDB_ATTR_ARRAY;
 *  ucdb_AttrAdd(db,mydata.u.attrhandle,-1,"NAMES",&names_array);
 *
 *  // B4. Same as A2. Use handle (set by API) to create string attribute 0
 *  name.type = UCDB_ATTR_STRING;
 *  name.u.svalue = "bob";
 *  ucdb_AttrAdd(db,names_array.u.attrhandle,0,NULL,&name);
 *  
 *  // B5. Same as A3. Use handle (set by API) to create string attribute 1
 *  name.type = UCDB_ATTR_STRING;
 *  name.u.svalue = "fred";
 *  ucdb_AttrAdd(db,names_array.u.attrhandle,1,NULL,&name);
 *
 *  // B6. Read attribute structure
 *  ucdb_AttrGet(db,scope,-1,"MYDATA",&mydata);
 *  if (mydata.type==UCDB_ATTR_HANDLE) {
 *      const char* key = NULL;
 *      while ((key = ucdb_AttrGetNext(db,mydata.u.attrhandle,-1,key,&field))){
 *          int i;
 *          switch(field.type) {
 *          case UCDB_ATTR_ARRAY:
 *              for ( i=0; i<ucdb_AttrArraySize(db,field.u.attrhandle); i++ ) {
 *                  // Note how key is NULL:
 *                  ucdb_AttrGet(db,field.u.attrhandle,i,NULL,&name);
 *                  printf("%s[%i] = %s\n",key,i,name.u.svalue);
 *              }
 *              break;
 *          case UCDB_ATTR_STRING:
 *              printf("%s = %s\n",key,field.u.svalue);
 *              break;
 *          }
 *      }
 *  }
 *
 *---------------------------------------------------------------------------*/

#define UCDB_ATTRIBUTE_HANDLE 0xcafeaaaa
#define UCDB_ATTRIBUTE_ARRAY  0xcafebbbb

typedef enum {
    UCDB_ATTR_INT,
    UCDB_ATTR_FLOAT,
    UCDB_ATTR_DOUBLE,
    UCDB_ATTR_STRING,
    UCDB_ATTR_MEMBLK,
    UCDB_ATTR_INT64,
    UCDB_ATTR_HANDLE,       /* Refers to other attributes: for nesting */
    UCDB_ATTR_ARRAY         /* Handle used to refer to an attribute array */
} ucdbAttrTypeT;

typedef void* ucdbAttrHandleT;

typedef struct {
    ucdbAttrTypeT type;     /* Value type */
    union {
        int64_t i64value;   /* 64-bit integer value */
        int ivalue;         /* Integer value */
        float fvalue;       /* Float value */
        double dvalue;      /* Double value */
        const char* svalue; /* String value */
        struct {
            int size;            /* Size of memory block, number of bytes */
            unsigned char* data; /* Starting address of memory block */
        } mvalue;
        ucdbAttrHandleT attrhandle; /* for HANDLE and ARRAY */
    } u;
} ucdbAttrValueT;

/*
 *  ucdb_AttrGetNext()
 *  Get the next attribute key and value from the given database object; if no
 *  object, global attributes for the database are returned.
 *  Use NULL key to start iteration.
 *  The system will return the next "key", NOT assign to the given
 *  "key" argument. There is no need to do free or strdup on keys.
 *  Key memory returned by ucdb_AttrGetNext() is owned by the API.
 *  Here is an example to traverse the list of attributes for a scope:
 *
 *  const char* key = NULL;
 *  ucdbAttrValueT value;
 *  while (key = ucdb_AttrGetNext(db,obj,-1,key,&value)) {
 *      printf("Attribute '%s' is ", key);
 *      print_attrvalue(&value);
 *  }
 */
const char*
ucdb_AttrGetNext(
    ucdbT           db,
    ucdbObjT        obj,        /* ucdbScopeT, ucdbHistoryNodeT, or NULL */
    int             coverindex, /* obj is ucdbScopeT: -1 for scope, valid index
                                   for coveritem */
    const char*     key,        /* NULL to get the first one */
    ucdbAttrValueT* value);

/*
 *  ucdb_AttrAdd()
 *  Add a new attribute on the given database object, or global attribute if
 *  the object is NULL. The attribute value will be copied to the system.
 *  Returns 0 for success and -1 otherwise.
 *  IMPORTANT NOTE: if value->type==UCDB_ATTR_HANDLE or UCDB_ATTR_ARRAY, then
 *  the API will *set* value->u.attrhandle to the created handle for further
 *  indirection.  See examples below.
 *  There is a maximum key length enforced by this function, see
 *  UCDBATTR_MAXKEYLENGTH.
 */
int
ucdb_AttrAdd(
    ucdbT           db,
    ucdbObjT        obj,        /* ucdbScopeT, ucdbHistoryNodeT, or NULL */
    int             coverindex, /* obj is ucdbScopeT: -1 for scope, valid index
                                   for coveritem */
    const char*     key,        /* New attribute key */
    ucdbAttrValueT* value);     /* New attribute value */

/*
 *  ucdb_AttrRemove()
 *
 *  Remove the attribute from the given database object, or global attribute if
 *  the object is NULL.
 *  Returns 0 for success, and -1 otherwise.
 */
int
ucdb_AttrRemove(
    ucdbT           db,
    ucdbObjT        obj,        /* ucdbScopeT, ucdbHistoryNodeT,
                                   ucdbAttrHandleT or NULL */
    int             coverindex, /* obj is ucdbScopeT: -1 for scope, valid index
                                   for coveritem
                                   obj is ucdbAttrHandleT:
                                       array index if type==UCDB_ATTR_ARRAY
                                       must be -1 if type==UCDB_ATTR_HANDLE
                                 */
    const char*     key);       /* NULL to get the first one */

/*
 *  ucdb_AttrGet()
 *
 *  Find attribute on the given database object, or global attribute if the
 *  object is NULL.
 *  The function returns 1 if a match is found, 0 otherwise.
 */
int
ucdb_AttrGet(
    ucdbT           db,
    ucdbObjT        obj,        /* ucdbScopeT, ucdbHistoryNodeT, or NULL */
    int             index,      /* obj is ucdbScopeT: -1 for scope, valid index
                                   for coveritem;
                                   obj is ucdbAttrHandleT:
                                       array index if type==UCDB_ATTR_ARRAY
                                       must be -1 if type==UCDB_ATTR_HANDLE
                                 */
    const char*     key,        /* Not necessary if obj is ucdbAttrHandleT and
                                   its type is UCDB_ATTR_ARRAY */
    ucdbAttrValueT* value);     /* Value set by function */

/*
 *  ucdb_AttrArraySize()
 *  Return size (maximum index plus 1) of attribute array.
 *  Returns size of array, -1 if type!=UCDB_ATTR_ARRAY.
 */
int
ucdb_AttrArraySize(
    ucdbT           db,
    ucdbAttrHandleT arrayhandle);


/* ================================================== */
/* ===== DEPRECATED USER ATTRIBUTE API ROUTINES ===== */
/* ================================================== */

/*
 *  ucdb_AttrNext()
 *  Get the next attribute key and value from the given database object; if no
 *  object, global attributes for the database are returned.
 *  Use NULL key to start iteration.
 *  The system will return the next "key", NOT assign to the given
 *  "key" argument. There is no need to do free or strdup on keys.
 *  To preserve the old key, just use another char* variable for it.
 *  Here is an example to traverse the list of attributes for a scope:
 *
 *  const char* key = NULL;
 *  ucdbAttrValueT* value;
 *  while (key = ucdb_AttrNext(db,obj,-1,key,&value)) {
 *          printf("Attribute '%s' is ", key);
 *          print_attrvalue(value);
 *  }
 */
const char*
ucdb_AttrNext(
    ucdbT           db,
    ucdbObjT        obj,        /* ucdbScopeT, ucdbHistoryNodeT, or NULL */
    int             coverindex, /* obj is ucdbScopeT: -1 for scope, valid index
                                   for coveritem */
    const char*     key,        /* NULL to get the first one */
    ucdbAttrValueT**value);

/*
 *  ucdb_AttrMatch()
 *  Find attribute on the given database object, or global attribute if the
 *  object is NULL.
 *  The value will be returned if a match is found, NULL otherwise.
 */
ucdbAttrValueT*
ucdb_AttrMatch(
    ucdbT           db,
    ucdbObjT        obj,        /* ucdbScopeT, ucdbHistoryNodeT, or NULL */
    int             coverindex, /* obj is ucdbScopeT: -1 for scope, valid index
                                   for coveritem */
    const char*     key);

/* #########################################################################
 * ##### USER ATTRIBUTES -- end
 * ######################################################################### */

/*------------------------------------------------------------------------------
 *  Managing scopes: design hierarchy and coverage scopes
 *
 *  The database is organized hierarchically, as per the design database: i.e.,
 *  there is a tree of module instances, each of a given module type.
 *
 *  Note on hierarchical identifiers:
 *
 *  If a scope type is Verilog or SystemVerilog, Verilog escaped identifiers
 *  syntax is assumed for a path within that scope.  If a scope type is VHDL,
 *  VHDL extended identifiers may be used.  The escaped identifier syntax
 *  is sensitive to the scope type so that escaped identifiers may appear in
 *  the user's accustomed syntax.
 *
 *  If a scope type is VHDL, entity, architecture, and library may be encoded
 *  in the name.
 *
 *  Note on attributes:
 *
 *  char* attributes may be omitted with a NULL value
 *  int attributes may be omitted with a negative value
 *
 *---------------------------------------------------------------------------*/

typedef uint64_t ucdbObjTypeT;             /* typedef for one of these: */
typedef ucdbObjTypeT ucdbScopeTypeT;       /* typedef for one of these: */
typedef uint64_t ucdbScopeMaskTypeT;       /* typedef for a set of these: */

#define UCDB_TOGGLE          /* cover scope- toggle coverage scope: */ \
                             INT64_LITERAL(0x0000000000000001)
#define UCDB_BRANCH          /* cover scope- branch coverage scope: */ \
                             INT64_LITERAL(0x0000000000000002)
#define UCDB_EXPR            /* cover scope- expression coverage scope: */ \
                             INT64_LITERAL(0x0000000000000004)
#define UCDB_COND            /* cover scope- condition coverage scope: */ \
                             INT64_LITERAL(0x0000000000000008)
#define UCDB_INSTANCE        /* HDL scope- Design hierarchy instance: */ \
                             INT64_LITERAL(0x0000000000000010)
#define UCDB_PROCESS         /* HDL scope- process: */ \
                             INT64_LITERAL(0x0000000000000020)
#define UCDB_BLOCK           /* HDL scope- vhdl block, vlog begin-end: */ \
                             INT64_LITERAL(0x0000000000000040)
#define UCDB_FUNCTION        /* HDL scope- function: */ \
                             INT64_LITERAL(0x0000000000000080)
#define UCDB_FORKJOIN        /* HDL scope- Verilog fork-join block: */ \
                             INT64_LITERAL(0x0000000000000100)
#define UCDB_GENERATE        /* HDL scope- generate block: */ \
                             INT64_LITERAL(0x0000000000000200)
#define UCDB_GENERIC         /* cover scope- generic scope type: */ \
                             INT64_LITERAL(0x0000000000000400)
#define UCDB_CLASS           /* HDL scope- class type scope: */ \
                             INT64_LITERAL(0x0000000000000800)
#define UCDB_COVERGROUP      /* cover scope- covergroup type scope: */ \
                             INT64_LITERAL(0x0000000000001000)
#define UCDB_COVERINSTANCE   /* cover scope- covergroup instance scope: */ \
                             INT64_LITERAL(0x0000000000002000)
#define UCDB_COVERPOINT      /* cover scope- coverpoint scope: */ \
                             INT64_LITERAL(0x0000000000004000)
#define UCDB_CROSS           /* cover scope- cross scope: */ \
                             INT64_LITERAL(0x0000000000008000)
#define UCDB_COVER           /* cover scope- directive(SVA/PSL) cover: */ \
                             INT64_LITERAL(0x0000000000010000)
#define UCDB_ASSERT          /* cover scope- directive(SVA/PSL) assert: */ \
                             INT64_LITERAL(0x0000000000020000)
#define UCDB_PROGRAM         /* HDL scope- SV program instance: */ \
                             INT64_LITERAL(0x0000000000040000)
#define UCDB_PACKAGE         /* HDL scope- package instance: */ \
                             INT64_LITERAL(0x0000000000080000)
#define UCDB_TASK            /* HDL scope- task: */ \
                             INT64_LITERAL(0x0000000000100000)
#define UCDB_INTERFACE       /* HDL scope- SV interface instance: */ \
                             INT64_LITERAL(0x0000000000200000)
#define UCDB_FSM             /* cover scope- FSM coverage scope: */ \
                             INT64_LITERAL(0x0000000000400000)
#define UCDB_TESTPLAN        /* test scope- for test plan item: */ \
                             INT64_LITERAL(0x0000000000800000)
#define UCDB_DU_MODULE       /* design unit- for instance type: */ \
                             INT64_LITERAL(0x0000000001000000)
#define UCDB_DU_ARCH         /* design unit- for instance type: */ \
                             INT64_LITERAL(0x0000000002000000)
#define UCDB_DU_PACKAGE      /* design unit- for instance type: */ \
                             INT64_LITERAL(0x0000000004000000)
#define UCDB_DU_PROGRAM      /* design unit- for instance type: */ \
                             INT64_LITERAL(0x0000000008000000)
#define UCDB_DU_INTERFACE    /* design unit- for instance type: */ \
                             INT64_LITERAL(0x0000000010000000)
#define UCDB_FSM_STATES      /* cover scope- FSM states coverage scope: */ \
                             INT64_LITERAL(0x0000000020000000)
#define UCDB_FSM_TRANS       /* cover scope- FSM transition coverage scope: */\
                             INT64_LITERAL(0x0000000040000000)
#define UCDB_GROUP           /* group scope: */\
                             INT64_LITERAL(0x0000000080000000)
#define UCDB_TRANSITION      /* cover scope- covergroup transition scope: */\
                             INT64_LITERAL(0x0000000100000000)
	                         
#define UCDB_RESERVEDSCOPE   INT64_LITERAL(0xFF00000000000000)
#define UCDB_SCOPE_ERROR     /* error return code: */ \
                             INT64_LITERAL(0x0000000000000000)

#define UCDB_FSM_SCOPE      ((ucdbScopeMaskTypeT)(UCDB_FSM |\
                                                  UCDB_FSM_STATES |\
                                                  UCDB_FSM_TRANS))

#define UCDB_CODE_COV_SCOPE ((ucdbScopeMaskTypeT)(UCDB_BRANCH |\
                                                  UCDB_EXPR |\
                                                  UCDB_COND |\
                                                  UCDB_TOGGLE |\
                                                  UCDB_FSM_SCOPE))

#define UCDB_DU_ANY ((ucdbScopeMaskTypeT)(UCDB_DU_MODULE |\
                                          UCDB_DU_ARCH |\
                                          UCDB_DU_PACKAGE |\
                                          UCDB_DU_PROGRAM |\
                                          UCDB_DU_INTERFACE))

#define UCDB_CVG_SCOPE      ((ucdbScopeMaskTypeT)(UCDB_COVERGROUP |\
                                                  UCDB_COVERINSTANCE |\
                                                  UCDB_COVERPOINT |\
                                                  UCDB_TRANSITION |\
                                                  UCDB_CROSS))

#define UCDB_FUNC_COV_SCOPE ((ucdbScopeMaskTypeT)(UCDB_CVG_SCOPE |\
                                                  UCDB_COVER))

#define UCDB_COV_SCOPE ((ucdbScopeMaskTypeT)(UCDB_CODE_COV_SCOPE |\
                                             UCDB_FUNC_COV_SCOPE))

#define UCDB_VERIF_SCOPE ((ucdbScopeMaskTypeT)(UCDB_COV_SCOPE |\
                                               UCDB_ASSERT |\
                                               UCDB_GENERIC))

#define UCDB_HDL_SUBSCOPE ((ucdbScopeMaskTypeT)(UCDB_PROCESS |\
                                                UCDB_BLOCK |\
                                                UCDB_FUNCTION |\
                                                UCDB_FORKJOIN |\
                                                UCDB_GENERATE |\
                                                UCDB_CLASS |\
                                                UCDB_TASK))

#define UCDB_HDL_INST_SCOPE ((ucdbScopeMaskTypeT)(UCDB_INSTANCE |\
                                                  UCDB_PROGRAM |\
                                                  UCDB_PACKAGE |\
                                                  UCDB_INTERFACE))

#define UCDB_HDL_DU_SCOPE ((ucdbScopeMaskTypeT)(UCDB_DU_ANY))

#define UCDB_HDL_SCOPE ((ucdbScopeMaskTypeT)(UCDB_HDL_SUBSCOPE |\
                                             UCDB_HDL_INST_SCOPE |\
                                             UCDB_HDL_DU_SCOPE))

#define UCDB_NONTESTPLAN_SCOPE ((ucdbScopeMaskTypeT)(~UCDB_TESTPLAN))

#define UCDB_NO_SCOPES  ((ucdbScopeMaskTypeT)INT64_ZERO)
#define UCDB_ALL_SCOPES ((ucdbScopeMaskTypeT)INT64_NEG1)

typedef unsigned int ucdbFlagsT;

/*
 *  Flags for scope data
 */

#define UCDB_INST_ONCE             0x00000001   /* An instance is instantiated only
                                                   once; code coverage is stored only in
                                                   the instance. */
/*
 *  These flags indicate whether the given scope was compiled with the
 *  corresponding type of code coverage enabled:
 */
#define UCDB_ENABLED_STMT          0x00000002   /* statement coverage */
#define UCDB_ENABLED_BRANCH        0x00000004   /* branch coverage */
#define UCDB_ENABLED_COND          0x00000008   /* condition coverage */
#define UCDB_ENABLED_EXPR          0x00000010   /* expression coverage */
#define UCDB_ENABLED_FSM           0x00000020   /* FSM coverage */
#define UCDB_ENABLED_TOGGLE        0x00000040   /* toggle coverage */
#define UCDB_ENABLED_TOGGLEEXT     0x00000080   /* extended (3-state) toggle */

#define UCDB_SCOPE_UNDER_DU        0x00000100   /* is scope under a design unit? */
#define UCDB_SCOPE_EXCLUDED        0x00000200
#define UCDB_SCOPE_PRAGMA_EXCLUDED 0x00000400
#define UCDB_SCOPE_PRAGMA_CLEARED  0x00000800
#define UCDB_SCOPE_GOAL_SPECIFIED  0x00001000

#define UCDB_IS_TOP_NODE           0x00008000   /* for top level toggle node */
#define UCDB_IS_IMMEDIATE_ASSERT   0x00010000   /* for SV immediate assertions */

/* Reuse the above two flag values for covergroup scopes */
#define UCDB_IS_E_PER_INST         0x00008000   /* for covergroup instance scopes */
#define UCDB_IS_E_PER_TYPE         0x00010000   /* for covergroup instance scopes */

/* For Zero Information in "flags" */
#define UCDB_SCOPE_IFF_EXISTS      0x00100000
#define UCDB_SCOPE_SAMPLE_TRUE     0x00200000   /* No bin under the scope is sampled */

/* 
 * Two bit Expression/Condition short circuit information flags applicable
 * to UCDB_EXPR and UCDB_COND scopes only.
 * Two bits are overloaded by re-using UCDB_SCOPE_IFF_EXISTS and
 * UCDB_SCOPE_SAMPLE_TRUE flags which are applicable to the covergroup
 * scopes only.
 * The two bits carry meaningful information only when used together.
 * The following informations are carried by those three bits:
 * 00: Short circuit enabled
 * 01: Short circuit partially enabled
 * 10: Short circuit disallowed
 * 11: Short circuit disabled (Same as flag UCDB_SCOPE_SAMPLE_TRUE)
 *
 * Note: The UCDB_SCOPE_SCKT_INFO flag defined below specifies whether the 
 * short circuit is enabled or disabled at the Design Unit level.
 */
#define UCDB_SCOPE_SCKT_PART_ENABLED 0x00100000
#define UCDB_SCOPE_SCKT_DISALLOWED 0x00200000
#define UCDB_SCOPE_SCKT_DISABLED   0x00300000

/* Flag for chceking if DU had short circuiting disabled for coverage */
#define UCDB_DISABLED_SHORTCKT     0x00400000

/* Flag for checking if a DU had UDP coverage enabled for expr/cond coverage */
#define UCDB_EXPRCOND_UDP        0x00800000
/*Flag for checking if it's PA coverage scope */
#define UCDB_PACOVERAGE          0x02000000

/* Flag used only on bimodal expressions to trigger Extended FEC Analysis */
#define UCDB_EXPRCOND_EXT_FEC         0x01000000

/* Flag set on last row of Extended FEC table */
#define UCDB_EXPRCOND_LAST_FEC_ROW   0x00080000

#define UCDB_SCOPEFLAG_MARK        0x08000000   /* flag for temporary mark */
#define UCDB_SCOPE_INTERNAL        0xF0000000   /* flags for internal use */

/*
 *  ucdbSourceT
 *  Enumerated type to encode the source type of a scope, if needed.  Note that
 *  scope type can have an effect on how the system regards escaped identifiers
 *  within design hierarchy.
 */
typedef enum {
    UCDB_VHDL,
    UCDB_VLOG,          /* Verilog */
    UCDB_SV,            /* SystemVerilog */
    UCDB_SYSTEMC,
    UCDB_PSL_VHDL,      /* assert/cover in PSL VHDL */
    UCDB_PSL_VLOG,      /* assert/cover in PSL Verilog */
    UCDB_PSL_SV,        /* assert/cover in PSL SystemVerilog */
    UCDB_PSL_SYSTEMC,   /* assert/cover in PSL SystemC */
    UCDB_E,
    UCDB_VERA,
    UCDB_NONE,          /* if not important */
    UCDB_OTHER,         /* to refer to user-defined attributes */
    UCDB_VLOG_AMS,      /* Verilog Analog Mixed Signal */
    UCDB_VHDL_AMS,      /* VHDL Analog Mixed Signal */
    UCDB_SPICE,
    UCDB_MATLAB,
    UCDB_C,
    UCDB_CPP,
    UCDB_SOURCE_ERROR = -1 /* for error cases */
}   ucdbSourceT;

/*
 *  ucdb_MatchScopeByName()
 *  Finds the scope specified by name in the given parent scope.
 *  Returns scope pointer or NULL if error.
 *
 *  IMPORTANT NOTE (DEPRECATED): this function is deprecated because it is not
 *  designed to handle scopes named the same with the same parent.  The best
 *  approach is a linear traversal of subscopes and name comparison with
 *  strcmp.  A future version of the API may have a more efficient and capable
 *  matching function.  However, this function can work well if you are
 *  confident there is 1 and only 1 match for the given name in the parent.
 */
ucdbScopeT
ucdb_MatchScopeByName(
    ucdbT               db,
    ucdbScopeT          parent,
    const char*         name);

/*
 *  ucdb_MatchScopeByPath()
 *  Finds the scope by path name using absolute path.
 *  The path separator is that currently in use by the database, see
 *  ucdb_SetPathSeparator(), ucdb_GetPathSeparator(). The pathname must start
 *  with this path separator.
 *  Returns scope pointer or NULL if error.
 *
 *  IMPORTANT NOTE (DEPRECATED): this function is deprecated because it is not
 *  designed to handle scopes named the same with the same parent.  Instead,
 *  use ucdb_PathCallBack() which has the added advantage of wildcard matching.
 *  However, this function can work well if you are confident there is 1 and
 *  only 1 object named as specified for every component of the path.
 */
ucdbScopeT
ucdb_MatchScopeByPath(
    ucdbT               db,
    const char*         pathname);

/*
 *  ucdb_CreateScope()
 *  Create the given scope underneath the given parent scope; if parent is
 *  NULL, create as root scope.
 *  Returns scope pointer or NULL if error.
 *  Note: use ucdb_CreateInstance() for UCDB_INSTANCE scopes.
 *  Note: in write streaming mode, "name" is not copied; it needs to be
 *  preserved unchanged until the next ucdb_WriteStream* call or the next
 *  ucdb_Create* call.
 */
ucdbScopeT
ucdb_CreateScope(
    ucdbT               db,
    ucdbScopeT          parent,
    const char*         name,
    ucdbSourceInfoT*    srcinfo,
    int                 weight,         /* negative for none */
    ucdbSourceT         source,
    ucdbScopeTypeT      type,           /* type of scope to create */
    int                 flags);

/*
 *  Utilities for parsing and composing design unit scope names.  These are of
 *  the form "library.primary(secondary)#instance_num", after the convention
 *  used by ModelSim and QuestaSim.
 *
 *  Note: these utilities each employ a static dynamic string (one for the
 *  "Compose" function, one for the "Parse" function).  That means that values
 *  are only valid until the next call to the respective function; if you need
 *  to hold the memory across separate calls you must copy it.
 */
const char*                             /* Return value is in temp storage */
ucdb_ComposeDUName(
    const char*         library_name,  /* input names */
    const char*         primary_name,
    const char*         secondary_name);

void
ucdb_ParseDUName(
    const char*         du_name,       /* input to function */
    const char**        library_name,  /* output names */
    const char**        primary_name,
    const char**        secondary_name);

/*
 *  ucdb_CreateInstance()
 *  Create the given instance scope of a given design unit type underneath the
 *  given parent.  If parent==NULL, create as a new root scope.
 *  Note that a previously created scope that is usually the design unit
 *  (UCDB_DU_* type) for the instance must be passed to this routine as
 *  du_scope.  If the instance is a UCDB_COVERINSTANCE, then the du_scope
 *  pointer must be of type UCDB_COVERGROUP to capture the instance -> type of
 *  instance relationship for the covergroup instance.
 *  Returns scope pointer or NULL if error.
 *  Note: not supported in streaming modes; use ucdb_CreateInstanceByName() in
 *  write streaming mode.
 *  Note: in write streaming mode, "name" is not copied; it needs to be
 *  preserved unchanged until the next ucdb_WriteStream* call or the next
 *  ucdb_Create* call.
 */
ucdbScopeT
ucdb_CreateInstance(
    ucdbT               db,
    ucdbScopeT          parent,
    const char*         name,
    ucdbSourceInfoT*    fileinfo,
    int                 weight,         /* negative for none */
    ucdbSourceT         source,
    ucdbScopeTypeT      type,           /* UCDB_INSTANCE, UCDB_COVERINSTANCE
                                           type of scope to create */
    ucdbScopeT          du_scope,       /* if type==UCDB_INSTANCE, this is a
                                           scope of type UCDB_DU_*; if
                                           type==UCDB_COVERINSTANCE, this is a
                                           scope of type UCDB_COVERGROUP */
    int                 flags);

/*
 *  ucdb_CreateInstanceByName()
 *  Create the given instance of a named design unit underneath the given
 *  parent scope.  The named design unit (du_name) must have been previously
 *  created.
 *  In WRITESTREAMING mode the parent scope should be NULL, and for other
 *  modes if the parent scope is NULL it creates a top scope.
 *  Returns scope pointer or NULL if error.
 *  Note: in write streaming mode, "name" and "du_name" are not copied; it
 *  needs to be preserved unchanged until the next ucdb_WriteStream* call
 *  or the next ucdb_Create* call.
 */
ucdbScopeT
ucdb_CreateInstanceByName(
    ucdbT               db,
    ucdbScopeT          parent,
    const char*         name,
    ucdbSourceInfoT*    fileinfo,
    int                 weight,
    ucdbSourceT         source,
    ucdbScopeTypeT      type,          /* UCDB_INSTANCE, UCDB_COVERINSTANCE
                                          type of scope to create */
    char*               du_name,       /* name for instance's design unit, or
                                          coverinstance's covergroup type */
    int                 flags);

/*
 *  ucdb_CreateCross()
 *  Create the given cross scope underneath the given parent, which must be of
 *  type UCDB_COVERGROUP or UCDB_COVERINSTANCE.
 *  Note: coverpoints named in the cross must already exist in the given
 *  parent.
 *  Note: in write streaming mode, "name" is not copied; it needs to be
 *  preserved unchanged until the next ucdb_WriteStream* call or the next
 *  ucdb_Create* call.
 *  Returns scope pointer or NULL if error.
 */
ucdbScopeT
ucdb_CreateCross(
    ucdbT               db,
    ucdbScopeT          parent,         /* covergroup or cover instance */
    const char*         name,
    ucdbSourceInfoT*    fileinfo,
    int                 weight,
    ucdbSourceT         source,
    int                 num_points,     /* number of crossed coverpoints */
    ucdbScopeT*         points);        /* array of coverpoint scopes */

/*
 *  ucdb_CreateCrossByName()
 *  Create the given cross scope underneath the given parent, which must be of
 *  type UCDB_COVERGROUP or UCDB_COVERINSTANCE.
 *  Note: coverpoints named in the cross must already exist in the given
 *  parent.
 *  Note: in write streaming mode, "name" is not copied; it needs to be
 *  preserved unchanged until the next ucdb_WriteStream* call or the next
 *  ucdb_Create* call.
 *  Returns scope pointer or NULL if error.
 */
ucdbScopeT
ucdb_CreateCrossByName(
    ucdbT               db,
    ucdbScopeT          parent,         /* covergroup or cover instance */
    const char*         name,
    ucdbSourceInfoT*    fileinfo,
    int                 weight,         /* does not apply to toggles */
    ucdbSourceT         source,
    int                 num_points,     /* number of crossed coverpoints */
    char**              point_names);   /* array of coverpoint names */

/*
 *  ucdb_CreateTransition()
 *  Create the given transition scope underneath the given parent, which must
 *  be of type UCDB_COVERGROUP or UCDB_COVERINSTANCE.
 *  Note: item named in the transition must already exist in the given
 *  parent.
 *  Note: in write streaming mode, "name" is not copied; it needs to be
 *  preserved unchanged until the next ucdb_WriteStream* call or the next
 *  ucdb_Create* call.
 *  Returns scope pointer or NULL if error.
 */
ucdbScopeT
ucdb_CreateTransition(
    ucdbT               db,
    ucdbScopeT          parent,         /* covergroup or cover instance */
    const char*         name,
    ucdbSourceInfoT*    fileinfo,
    int                 weight,
    ucdbSourceT         source,
    ucdbScopeT          item);        /* array of coverpoint scopes */

/*
 *  ucdb_CreateTransitionByName()
 *  Create the given transition scope underneath the given parent, which must
 *  be of type UCDB_COVERGROUP or UCDB_COVERINSTANCE.
 *  Note: item named in the cross must already exist in the given
 *  parent.
 *  Note: in write streaming mode, "name" is not copied; it needs to be
 *  preserved unchanged until the next ucdb_WriteStream* call or the next
 *  ucdb_Create* call.
 *  Returns scope pointer or NULL if error.
 */
ucdbScopeT
ucdb_CreateTransitionByName(
    ucdbT               db,
    ucdbScopeT          parent,         /* covergroup or cover instance */
    const char*         name,
    ucdbSourceInfoT*    fileinfo,
    int                 weight,         /* does not apply to toggles */
    ucdbSourceT         source,
    char*               item_name);

/*
 *  ucdb_InstanceSetDU()
 *  Set the given DU handle in the given instance. The instance and du_scope
 *  should be from the same database.
 *  Returns 0 for success, and -1 for any error.
 */
int
ucdb_InstanceSetDU(
    ucdbT               db,
    ucdbScopeT          instance,
    ucdbScopeT          du_scope);      /* if type==UCDB_INSTANCE, this is a
                                           scope of type UCDB_DU_*; if
                                           type==UCDB_COVERINSTANCE, this is a
                                           scope of type UCDB_COVERGROUP */

/*
 *  ucdb_CloneScope()
 *  This function creates an exact copy of the given scope into
 *  the targetparent. Predefined attributes will always be created
 *  by default. There is no effect of this function when targetdb is in
 *  streaming mode.
 *  If is_recursive is set (non-zero) then it creates clones for all the
 *  subscopes recursively.
 *  A successful operation will return the scope handle, and NULL for error.
 */
ucdbScopeT
ucdb_CloneScope(
    ucdbT               targetdb,     /* database context for clone */
    ucdbScopeT          targetparent, /* parent of clone */
    ucdbT               sourcedb,     /* source database */
    ucdbScopeT          scope,        /* source scope */
    ucdbSelectFlagsT    cloneflags,   /* flags to specify what to copy */
    int                 is_recursive);/* A non-zero means recursive */

/*
 *  ucdb_RemoveScope()
 *  This function removes the given scope from its parent
 *  along with all its subscopes and coveritems.
 *  There is no effect of this function in streaming modes.
 *  A successful operation will return 0, and -1 for error.
 *  Note: If a scope is removed then that scope handle will become invalid
 *  immediately along with all of its subscope handles, and those handles
 *  can't be used in any API routine.
 *  Also, this function should be used carefully if it is
 *  used during iteration of scopes using any scope iteration
 *  API, otherwise the iteration may not be complete.
 */
int
ucdb_RemoveScope(
    ucdbT               db,     /* database context */
    ucdbScopeT          scope); /* scope to remove */

/*
 *  ucdb_ScopeParent()
 *  Returns the parent scope handle of the given scope, or NULL if none
 *  or error.
 */
ucdbScopeT
ucdb_ScopeParent(
    ucdbT               db,
    ucdbScopeT          scope);

/*
 *  ucdb_ScopeGetTop()
 *  Returns the top-level scope (i.e., one with no parent) above the given
 *  scope.
 */
ucdbScopeT
ucdb_ScopeGetTop(
    ucdbT               db,
    ucdbScopeT          scope);

/*
 *  ucdb_GetScopeName()
 *  Get name of scope as a simple (non-hierarchical) string.
 *  Returns NULL with error.
 */
const char*
ucdb_GetScopeName(
    ucdbT               db,
    ucdbScopeT          scope);

/*
 *  ucdb_SetScopeName()
 *  Set name of scope.
 *  Returns -1 for error.
 */
int
ucdb_SetScopeName(
    ucdbT               db,
    ucdbScopeT          scope,
    const char*         name);

/*
 *  ucdb_GetScopeType()
 *  Get type of scope.
 *  Returns UCDB_SCOPE_ERROR if error.
 */
ucdbScopeTypeT
ucdb_GetScopeType(
    ucdbT               db,
    ucdbScopeT          scope);

/*
 *	ucdb_GetObjType (alias ucdb_GetHistoryKind)
 *
 *  Returns UCDB_SCOPE_ERROR if error.
 *  Returns UCDB_HISTORYNODE_TEST when obj is a test data record.
 *  Returns UCDB_HISTORYNODE_TESTPLAN when obj is a testplan record.
 *  Returns UCDB_HISTORYNODE_MERGE when obj is a merge record.
 *  Otherwise, returns the scope type ucdbScopeTypeT:
 *      [See ucdbScopeTypeT ucdb_GetScopeType(ucdbT db, ucdbScopeT scope)]
 *
 *	This is a polymorphic function for acquiring an object type.
 *	IMPORTANT NOTE: this may return multiple bits set (specifically
 *	for history data objects). The return value MUST NOT be used as a mask.
 */
ucdbObjTypeT
ucdb_GetObjType(
    ucdbT           db,
    ucdbObjT        obj);

/*
 *  ucdb_GetScopeSourceType()
 *  Get source type of scope.
 *  Returns UCDB_SOURCE_ERROR if error.
 */
ucdbSourceT
ucdb_GetScopeSourceType(
    ucdbT               db,
    ucdbScopeT          scope);



/*
 *  ucdb_GetScopeFlags()
 *  Get scope flags.
 */
ucdbFlagsT
ucdb_GetScopeFlags(
    ucdbT               db,
    ucdbScopeT          scope);

/*
 *  ucdb_SetScopeFlags()
 *  Set scope flags.
 */
void
ucdb_SetScopeFlags(
    ucdbT               db,
    ucdbScopeT          scope,
    ucdbFlagsT          flags);

/*
 *  ucdb_GetScopeFlag()
 *  Fancier interface for getting a single flag bit.
 *  Return 1 if specified scope's flag bit matches the given mask.
 */
int
ucdb_GetScopeFlag(
    ucdbT               db,
    ucdbScopeT          scope,
    ucdbFlagsT          mask);

/*
 *  ucdb_SetScopeFlag()
 *  Set bits in the scope's flag field with respect to the given mask --
 *  set all bits to 0 or 1.
 */
void
ucdb_SetScopeFlag(
    ucdbT               db,
    ucdbScopeT          scope,
    ucdbFlagsT          mask,
    int                 bitvalue);  /* 0 or 1 only */

/*
 *  ucdb_GetScopeSourceInfo()
 *  Gets source information (file/line/token) for the given scope.
 *  Note: string storage is maintained by the API; do not free.
 *  Returns 0 on success, non-zero on failure.
 */
int
ucdb_GetScopeSourceInfo(
    ucdbT               db,
    ucdbScopeT          scope,
    ucdbSourceInfoT*    sourceinfo);

/*
 *  ucdb_SetScopeFileHandle()
 *  Sets file handle for the given scope.
 *  Note: string storage is maintained by the API; do not free.
 *  Returns 0 on success, non-zero on failure.
 *  Note: does not apply to toggle nodes.
 */
int
ucdb_SetScopeFileHandle(
    ucdbT               db,
    ucdbScopeT          scope,
    ucdbFileHandleT*    filehandle);

/*
 *  ucdb_GetScopeWeight()
 *  Gets weight for the given scope.
 *  Note: toggles do not have a weight; this always returns 1.
 */
int
ucdb_GetScopeWeight(
    ucdbT               db,
    ucdbScopeT          scope);

/*
 *  ucdb_SetScopeWeight()
 *  Sets weight for the given scope.
 *  Returns 0 for success, -1 for error.
 *  Note: does not apply to toggle nodes.
 */
int
ucdb_SetScopeWeight(
    ucdbT               db,
    ucdbScopeT          scope,
    int                 weight);

/*
 *  Get goal for scope.  Returns 1 if found, 0 if not found.  Converts
 *  from integer for UCDB_CVG_SCOPE types, see note above.
 *  Note: does not apply to toggle nodes.
 */
int
ucdb_GetScopeGoal(
    ucdbT           db,
    ucdbScopeT      scope,
    float*          goal);

/*
 *  Set goal for given scope.  For UCDB_CVG_SCOPE types, this will convert
 *  to an integer value (as option.goal and type_option.goal are
 *  defined in the SystemVerilog LRM as integers.)
 *  Note: does not apply to toggle nodes.
 */
int
ucdb_SetScopeGoal(
    ucdbT           db,
    ucdbScopeT      scope,
    float           goal);

/*
 *  ucdb_SetScopeSourceInfo()
 *  Sets source information (file/line/token) for the given scope.
 *  Returns 0 on success, non-zero on failure.
 */
int
ucdb_SetScopeSourceInfo(
    ucdbT               db,
    ucdbScopeT          scope,
    ucdbSourceInfoT*    sourceinfo);

/*
 *  ucdb_GetScopeHierName()
 *  Get name of scope as a hierarchical string, with the path separator as set
 *  for the current database.  See ucdb_GetPathSeparator().
 *  Returns NULL with error.
 *  Note: Returns memory address from a static location of the database handle,
 *  so the next call overrides the previous value. The user must not modify or
 *  deallocate the memory address to avoid any unexpected result.
 */
const char*
ucdb_GetScopeHierName(
    ucdbT               db,
    ucdbScopeT          scope);

/*
 *  ucdb_GetInstanceDU()
 *  Get design unit scope of the given instance scope (ucdbScopeTypeT ==
 *  UCDB_INSTANCE);
 *  IMPORTANT NOTE: this can return the UCDB_COVERGROUP scope for a
 *  UCDB_COVERINSTANCE as well.
 *  Returns scope pointer or NULL if error.
 *  Note: Returns memory address from a static location of the database handle,
 *  so the next call overrides the previous value. The user must not modify or
 *  deallocate the memory address to avoid any unexpected result.
 */
ucdbScopeT
ucdb_GetInstanceDU(
    ucdbT               db,
    ucdbScopeT          scope);

/*
 *  ucdb_GetInstanceDUName()
 *  Get design unit scope name of given instance scope (ucdbScopeTypeT ==
 *  UCDB_INSTANCE);
 *  IMPORTANT NOTE: this can return the UCDB_COVERGROUP scope name for a
 *  UCDB_COVERINSTANCE as well.
 *  The pointer is not to be de-allocated; to be saved in streaming modes, it
 *  must be copied.  (It need not be copied in in-memory mode.)
 *  Returns NULL if error.
 */
char*
ucdb_GetInstanceDUName(
    ucdbT       db,
    ucdbScopeT  scope);

/*
 *  ucdb_GetNumCrossedCvps()
 *  Get the number of crossed coverpoints, if scope is a cross scope.
 *  Returns 0 if success, non-zero if error.
 */
int
ucdb_GetNumCrossedCvps(
    ucdbT               db,
    ucdbScopeT          scope,
    int*                num_points);

/*
 *  ucdb_GetIthCrossedCvp()
 *  Get crossed coverpoint of scope specified by the index, if scope is a
 *  cross scope.
 *  Returns 0 if success, non-zero if error.
 */
int
ucdb_GetIthCrossedCvp(
    ucdbT               db,
    ucdbScopeT          scope,
    int                 index,
    ucdbScopeT*         point_scope);

/*
 *  ucdb_GetIthCrossedCvpName()
 *  Get crossed coverpoint scope name specified by the index, if scope is a
 *  cross scope.
 *  Returns NULL if error.
 */
char*
ucdb_GetIthCrossedCvpName(
    ucdbT        db,
    ucdbScopeT   scope,
    int          index);

/*
 *  ucdb_GetTransitionItem()
 *  Get transition item scope, if scope is a transition scope.
 *  Returns NULL if error.
 */
ucdbScopeT
ucdb_GetTransitionItem(
    ucdbT        db,
    ucdbScopeT   scope);

/*
 *  ucdb_GetTransitionItemName()
 *  Get transition item scope name, if scope is a transition scope.
 *  Returns NULL if error.
 */
char*
ucdb_GetTransitionItemName(
    ucdbT        db,
    ucdbScopeT   scope);

/*
 *  ucdb_NextPackage()
 *  Given a package, get the next package in the database.
 *  To return the first, use package==NULL.
 *  Returns NULL at end of traversal.  Error set if error.
 */
ucdbScopeT
ucdb_NextPackage(
    ucdbT               db,
    ucdbScopeT          package);

/*
 *  ucdb_NextDU()
 *  Given a design unit, get the next design unit in the database.
 *  To return the first, use du==NULL.
 *  Returns NULL at end of traversal.  Error set if error.
 */
ucdbScopeT
ucdb_NextDU(
    ucdbT               db,
    ucdbScopeT          du);

/*
 *  ucdb_MatchDU()
 *  Given a design unit name, get the design unit scope in the database.
 *  Returns NULL if no match is found.
 */
ucdbScopeT
ucdb_MatchDU(
    ucdbT               db,
    const char*         name);

/*
 *  ucdb_NextSubScope()
 *  Iterate through child scopes of type specified by "scopemask", starting in
 *  the given parent scope.  If no parent scope is given, this can iterate
 *  through the top-level modules in the design.  Starts the traversal when
 *  scope==NULL.
 *  Returns NULL on last element or if error.
 */
ucdbScopeT
ucdb_NextSubScope(
    ucdbT               db,
    ucdbScopeT          parent,     /* NULL iterates top-level module(s) */
    ucdbScopeT          scope,      /* NULL starts traversal */
    ucdbScopeMaskTypeT  scopemask); /* mask for scope type */

/*
 *  ucdb_NextScopeInDB()
 *  Iterate through all the child scopes of type specified by "scopemask" in
 *  database, starting with the first top level scope.
 *  Starts the traversal when scope==NULL.
 *  Returns NULL on last element or if error.
 */
ucdbScopeT
ucdb_NextScopeInDB(
    ucdbT               db,
    ucdbScopeT          scope,      /* NULL starts traversal */
    ucdbScopeMaskTypeT  scopemask); /* mask for scope type */

/*
 *  ucdb_NextInstOfDU()
 *  Returning scopes of type UCDB_INSTANCE, this allows traversal of all
 *  instances of a given design unit (scopes of one of the types UCDB_DU_*).
 *  Returns NULL on last element or if error.
 */
ucdbScopeT
ucdb_NextInstOfDU(
    ucdbT               db,
    ucdbScopeT          instance,   /* NULL starts traversal */
    ucdbScopeT          du);        /* ScopeType==UCDB_DU_* */

/*
 *  ucdb_ScopeIsUnderDU()
 *  Returns 1 if scope is under a DU, 0 if not, -1 for error.
 *  Returns 1 if scope is among UCDB_HDL_DU_SCOPE types.
 *  IMPORTANT NOTE: this does not work for scopes underneath single-instance
 *  design units, because of the UCDB_INST_ONCE optimization (in which case the
 *  node is really under the instance.)  This will be corrected in a future
 *  architecture of the UCDB API, after the UCDB_INST_ONCE optimization is
 *  completely hidden.
 */
int
ucdb_ScopeIsUnderDU(
    ucdbT               db,
    ucdbScopeT          scope);

/*
 *  ucdb_ScopeIsUnderCoverInstance()
 *  Returns 1 if scope is under a UCDB_COVERINSTANCE scope.
 *  This can only be true for UCDB_COVERPOINT or UCDB_CROSS scopes.
 */
int
ucdb_ScopeIsUnderCoverInstance(
    ucdbT               db,
    ucdbScopeT          scope);

/*
 *  ucdb_CallBack()
 *  Visit that portion of the database rooted at and below the given starting
 *  scope. Issue calls to the callback function (cbfunc) along the way. When
 *  the starting scope (start) is NULL the entire database will be walked.
 *  Returns 0 with success, -1 with failure.
 *  In-memory mode only.
 */
int
ucdb_CallBack(
    ucdbT        db,
    ucdbScopeT   start,             /* NULL traverses entire database */
    ucdb_CBFuncT cbfunc,
    void*        userdata);

/*
 *  ucdb_PathCallBack()
 *  This is a more flexible callback mechanism that can implement wildcarded
 *  paths, filtering according to type, etc.
 *  In-memory mode only.
 *
 *  recurse     Recurse from matched du or scopes specified by path.  Note that
 *              scope_mask and cover_mask are applied AFTER recursion.
 *              Recursion proceeds from all scopes matching the (possibly
 *              wildcarded) path, after which callbacks are generated only for
 *              those scopes and covers -- including those specified by the
 *              path itself -- that share a bit with the scope or cover mask.
 *  path        If (du_name==NULL) it is treated as an absolute path.
 *              If (du_name!=NULL) it is treated as a path relative to
 *              design unit(s) matching du_name
 *              If equal to "/" it is treated as "*" (matches all roots or all
 *              paths under a design unit).
 *              Wildcards may be given to match multiple results (see below).
 *              Uses UCDB path separator, escaped identifier rules in a
 *              context-sensitive fashion.
 *  du_name     in format "lib.primary(secondary)", secondary matched for VHDL
 *              only.  Multiple matches possible if lib or secondary is absent
 *              (note this is even true of Verilog design units, if the
 *              simulator created an artificial secondary.)  If path is given
 *              also, then path is relative to all dus matching this
 *              specification.
 *  root_mask   Will only start matching from a root that satisfies 1 bit of
 *              this mask.  This applies at the top-level only, so will not
 *              apply when du_name is given.  Most likely set to UCDB_TESTPLAN
 *              or UCDB_NONTESTPLAN_SCOPE to choose a testplan tree or
 *              non-testplan tree.
 *  scope_mask  Will only match scopes satisfying 1 bit of this mask.
 *  cover_mask  Will only match coveritems satisfying 1 bit of this mask.
 *  cbfunc      User-supplied callback function.  Note that only these callback
 *              reasons (ucdbCBReasonT) are generated:
 *                  UCDB_REASON_DU, UCDB_REASON_SCOPE, UCDB_REASON_CVBIN
 *                  UCDB_REASON_ENDSCOPE
 *
 *
 *  Note on Test Plan Scopes
 *
 *  When recursing through a test plan scope, it is considered to have virtual
 *  children: the design or coverage scopes with which it is linked through
 *  common tags.  This reflects the reality that these scopes contribute to the
 *  test plan scope's coverage.  The same goes for matching "*" children of a
 *  test plan scope: that matches both real test plan children as well as
 *  scopes linked to the test plan scope with tags.
 *
 *  Return Value
 *
 *  -1 with use error, otherwise returns the number of matches (0 or more)
 *
 *  Wildcarding:
 *
 *  *                         matches any substring within a level of hierarchy
 *  ?                         preceding character is optional
 *  [<int>:<int>]             matches an integer index within the range
 *  (<int|*> to <int|*>)      matches an integer index within the range
 *  (<int|*> downto <int|*>)  matches an integer index within the range
 *
 *  More wildcarding characters may be supported in the future.  To match
 *  wildcard characters literally, the appropriate escaped identifier syntax
 *  must be used.
 *
 *  Examples:
 *
 *  ucdb_PathCallBack(db,0,"/top/a*",NULL,UCDB_NONTESTPLAN_SCOPE,
 *                    UCDB_HDL_INST_SCOPE,0,f,d);
 *
 *      Call back for all HDL instance scopes that start with "/top/a".
 *
 *  ucdb_PathCallBack(db,0,NULL,"duname",-1,-1,0,f,d);
 *
 *      Call back for all design units with name "duname".  This may match
 *      multiple architectures or library implementations of the design unit.
 *
 *  ucdb_PathCallBack(db,0,"myvec*","work.duname(myarch)",-1,UCDB_TOGGLE,0,f,d);
 *
 *      Within VHDL architecture "work.duname(myarch)", call back for all toggle
 *      scopes whose names start with "myvec".
 *
 *  ucdb_PathCallBack(db,1,"/top/a",NULL,UCDB_NONTESTPLAN_SCOPE,
 *                    UCDB_COVERGROUP|UCDB_COVERPOINT|UCDB_CROSS,0,f,d);
 *
 *      Call back for all covergroup, cross, and coverpoint scopes that lie
 *      underneath "/top/a".  Only if "/top/a" is a covergroup scope will
 *      "/top/a" itself be a callback.
 *
 *  ucdb_PathCallBack(db,1,"/top/a",NULL,UCDB_NONTESTPLAN_SCOPE,
 *                    UCDB_COVERGROUP|UCDB_COVERPOINT|UCDB_CROSS,UCDB_CVGBIN,
 *                    f,d);
 *
 *      Same callback as above, but includes bin callbacks as well.
 */
int
ucdb_PathCallBack(
    ucdbT           db,
    int             recurse,        /* see block comments, above */
    const char*     path,
    const char*     du_name,
    ucdbScopeMaskTypeT  root_mask,
    ucdbScopeMaskTypeT  scope_mask,
    ucdbCoverMaskTypeT  cover_mask,
    ucdb_CBFuncT    cbfunc,         /* user-supplied callback function */
    void*           userdata);      /* user-supplied data for callback */

/*
 *  ucdb_MatchTests()
 *  This function generates callbacks for tests whose "testname" attribute
 *  matches the pattern in the "testname" argument to this function.
 *  Note this generates UCDB_REASON_TEST callbacks only.
 *  Returns -1 for error, otherwise number of callbacks made.
 *  In-memory mode only.
 */
int
ucdb_MatchTests(
    ucdbT           db,
    const char*     testname,       /* can have wildcards, see Wildcarding in
                                       comments for ucdb_PathCallBack() */
    ucdb_CBFuncT    cbfunc,         /* user-supplied callback function */
    void*           userdata);      /* user-supplied data for callback */

/*
 *  ucdb_MatchCallBack()
 *  This function matches the given pattern for any name in the entire instance
 *  tree or within specified design unit(s).  Its operation is implicitly
 *  recursive, as it searches the entire subtree and generates callbacks for
 *  named objects matching the pattern.  As with PathCallBack, wildcards are
 *  allowed, and there are scope mask and cover mask type filters.
 *  Returns -1 with use error, otherwise returns the number of matches (0 or
 *  more).
 */
int
ucdb_MatchCallBack(
    ucdbT           db,
    const char*     pattern,        /* name pattern to match recursively */
    const char*     du_name,        /* see ucdb_PathCallBack */
    ucdbScopeMaskTypeT  root_mask,
    ucdbScopeMaskTypeT  scope_mask,
    ucdbCoverMaskTypeT  cover_mask,
    ucdb_CBFuncT    cbfunc,         /* user-supplied callback function */
    void*           userdata);      /* user-supplied data for callback */


/*------------------------------------------------------------------------------
 *  Summary coverage statistics.
 *
 *  This interface allows quick access to aggregated coverage and statistics
 *  for different kinds of coverage, and some overall statistics for the
 *  database.
 *----------------------------------------------------------------------------*/
/*
 *  *_DU coverage numbers accumulate per-design-unit aggregations: where
 *  coverage from all instances of a design unit are merged into and stored
 *  with the design unit itself.  The summaries are then computed by traversing
 *  design units, not design instances. In our UCDB, this occurs for code
 *  coverage only.
 *
 *  *_INST values accumulate all results from the entire instance tree: this
 *  means that design instances, not design units, are traversed.
 *
 *  Note that UCDB_CVG_INST coverage refers to covergroup instances, not design
 *  instances.  That is coverage for exactly those covergroup objects that have
 *  option.per_instance set to 1 in SystemVerilog source, weighted by
 *  option.weight.  If no such covergroup objects exist, there will be no
 *  UCDB_CVG_INST coverage.
 */

/* 
 * The following macros are defined for backward compatibility in enum
 * literal names.
 */
#define UCDB_EXPR_INST   UCDB_UDP_EXPR_INST
#define UCDB_EXPR_DU     UCDB_UDP_EXPR_DU
#define UCDB_COND_INST   UCDB_UDP_COND_INST
#define UCDB_COND_DU     UCDB_UDP_COND_DU

typedef enum {
    UCDB_CVG_TYPE,    /* 0 Covergroup type coverage == $get_coverage() value */
    UCDB_CVG_INST,    /* 1 Covergroup instances (option.per_instance==1) , if
                           any, weighted average */
    UCDB_COVER_INST,  /* 2 Cover directive, weighted average, per design
                           instance */
    UCDB_SC_INST,     /* 3 SystemC functional coverage, per design instance */
    UCDB_ZIN_INST,    /* 4 0-In checkerware coverage, per design instance */
    UCDB_STMT_INST,   /* 5 statement coverage, per design instance */
    UCDB_STMT_DU,     /* 6 statement coverage, per design unit */
    UCDB_BRANCH_INST, /* 7 branch coverage, per design instance */
    UCDB_BRANCH_DU,   /* 8 branch coverage, per design unit */
    UCDB_UDP_EXPR_INST,   /* 9 UDP expression coverage, per design instance */
    UCDB_UDP_EXPR_DU,     /* 10 UDP expression coverage, per design unit */
    UCDB_UDP_COND_INST,   /* 11 UDP condition coverage, per design instance */
    UCDB_UDP_COND_DU,     /* 12 UDP condition coverage,per design unit */
    UCDB_TOGGLE_INST, /* 13 toggle coverage, per design instance */
    UCDB_TOGGLE_DU,   /* 14 toggle coverage, per design unit */
    UCDB_FSM_ST_INST, /* 15 FSM state coverage, per design instance */
    UCDB_FSM_ST_DU,   /* 16 FSM state coverage, per design unit */
    UCDB_FSM_TR_INST, /* 17 FSM transition coverage, per design instance */
    UCDB_FSM_TR_DU,   /* 18 FSM transition coverage, per design unit */
    UCDB_USER_INST,   /* 19 user-defined coverage, per design instance */
    UCDB_ASSERT_PASS_INST,      /* 20 Assertion directive passes, per design
                                      instance */
    UCDB_ASSERT_FAIL_INST,      /* 21 Assertion directive failures, per design
                                      instance */
    UCDB_ASSERT_VPASS_INST,     /* 22 Assertion directive vacuous passes, per
                                      design instance */
    UCDB_ASSERT_DISABLED_INST,  /* 23 Assertion directive disabled, per design
                                      instance */
    UCDB_ASSERT_ATTEMPTED_INST, /* 24 Assertion directive attempted, per design
                                      instance */
    UCDB_ASSERT_ACTIVE_INST,    /* 25 Assertion directive active, per design
                                      instance */
    UCDB_CVP_INST,              /* 26 Coverpoint/cross weighted average, all
                                      coverpoint and cross declarations */
    UCDB_DIRECTED_TESTS,        /* 27 Test section links to test data records*/
    UCDB_FEC_EXPR_INST, /* 28 focused expression coverage, per design instance
                         */
    UCDB_FEC_EXPR_DU,   /* 29 focused expression coverage, per design unit */
    UCDB_FEC_COND_INST, /* 30 focused condition coverage, per design instance
                         */
    UCDB_FEC_COND_DU,   /* 31 focused condition coverage,per design unit */
    UCDB_ASSERT_SUCCESS_INST,   /* 32 Assertion directives that succeeded:
                                      never failed, passed at least once (if
                                      pass counts available.) */
    UCDB_EXPRESSION_INST,       /* 33 expression coverage, per design instance */
    UCDB_EXPRESSION_DU,         /* 34 expression coverage, per design unit */
    UCDB_CONDITION_INST,        /* 35 condition coverage, per design instance */
    UCDB_CONDITION_DU,          /* 36 condition coverage,per design unit */
    UCDB_FSM_INST,      /* 37 FSM state coverage, per design instance */
    UCDB_FSM_DU,        /* 38 FSM state coverage, per design unit */
    UCDB_N_SUMMARY_ENUM_T       /* 39 Can be used for array bounds */
} ucdbSummaryEnumT;

/*
 *  This structure stores values for a particular enumerator, above.
 *
 *  Note on "num_coveritems", the nature of the item counted depends on the
 *  type of coverage:
 *
 *  Enum:       Type:               Total number of:
 *  CVG*        SV covergroup       bins
 *  COVER       SVA or PSL cover    cover directives or statements
 *  STMT*       statement           statements
 *  BRANCH*     branch              branches (including implicit elses)
 *  EXPR*       expression          known-value truth table rows
 *  COND*       condition           known-value truth table rows
 *  TOGGLE*     toggle              toggles (scopes in UCDB)
 *  FSM_ST*     FSM state           FSM states
 *  FSM_TR*     FSM transition      FSM transitions
 *  ASSERT*     SVA or PSL assert   assert directives or statements
 *
 *  Notes on num_covered:
 *
 *  This value is almost always the number of coveritems covered, except for:
 *
 *  ASSERT_PASS*                    number of assertion passes
 *  ASSERT_FAIL*                    number of assertion failures
 *
 */
typedef struct {
    float   coverage_pct;   /* floating point coverage value, percentage */
    float   goal_pct;       /* floating point goal, percentage */
    int     num_coveritems; /* total number of coveritems (bins) */
    int     num_covered;    /* number of coveritems (bins) covered */
} ucdbCoverageT;

typedef enum {
    UCDB_SUMMARY_FLAG_none = 0,
    UCDB_SUMMARY_FLAG_is_merge_totals         = 1,  /* Bit 0 set implies
                                                       "merge -totals" file */
    UCDB_SUMMARY_FLAG_is_merge_testassociated = 2,  /* Bit 1 set implies
                                                       "merge -testassociated"
                                                       file */
    UCDB_SUMMARY_FLAG_is_merge = 3
} ucdbSummaryFlagsEnumT;

/*
 *  This structure stores all statistics returned by ucdb_GetCoverageSummary()
 */
typedef struct {
    int                   num_instances;  /* number of design instances */
    int                   num_coverpoints;/* number of SV coverpoint/cross
                                             types */
    int                   num_covergroups;/* number of SV covergroup types */
    int                   num_dus;        /* number of design units */
    ucdbSummaryFlagsEnumT flags;
    ucdbCoverageT   coverage[UCDB_N_SUMMARY_ENUM_T];
} ucdbCoverageSummaryT;

/*
 *  Goals for different types of coverage.  These are percentages, against
 *  which aggregated coverage is compared to determine whether the goal has
 *  been satisfied.
 */
/*
 *  ucdb_SetGoal()
 *  This will set the goal for the specified type of aggregated coverage.
 *  Returns 0 with success, non-zero with any error.
 */
int
ucdb_SetGoal(
    ucdbT               db,
    ucdbSummaryEnumT    type,
    float               percentage);

/*
 *  ucdb_GetGoal()
 *  This will return the goal for the specified type of aggregated coverage.
 *  The goal is a percentage, 0.0 to 100.0.
 *  Returns non-negative goal value for success, -1.0 for any error.
 */
float
ucdb_GetGoal(
    ucdbT               db,
    ucdbSummaryEnumT    type);

/*
 *  Weights for different types of coverage.  These are non-negative integers,
 *  used to compute total coverage numbers as in ucdb_GetTotalCoverage().
 */
/*
 *  ucdb_SetWeightPerType()
 *  This will set the weight for the specified type of aggregated coverage.
 *  Returns 0 with success, non-zero with any error.
 */
int
ucdb_SetWeightPerType(
    ucdbT               db,
    ucdbSummaryEnumT    type,
    int                 weight);

/*
 *  ucdb_GetWeightPerType()
 *  This will return the weight for the specified type of aggregated coverage.
 *  The weight is non-negative
 *  Returns non-negative weight value for success, -1 for any error.
 */
int
ucdb_GetWeightPerType(
    ucdbT               db,
    ucdbSummaryEnumT    type);

/*
 *  ucdb_GetCoverageSummary()
 *  This is an efficient read of coverage summary statistics.  The file is
 *  opened, seeked to the location of previously computed summary statistics,
 *  and immediately closed.
 *  See also: ucdb_CalcCoverageSummary for the "efficient read" option.
 *  Returns 0 with success, non-zero with any error.
 *
int
ucdb_GetCoverageSummary(
    const char*             name,       // file system path
    ucdbCoverageSummaryT*   data);
 */

#define ucdb_GetCoverageSummary(name,data) \
        ucdb_GetCoverageSummaryV(name,data,UCDB_H_VERSION)
int
ucdb_GetCoverageSummaryV(
    const char*,
    ucdbCoverageSummaryT*,
    int);

/*
 *  See also:
 *  ucdb_CalcCoverageSummary()
 *  ucdb_GetTotalCoverage()
 */

/*
 *  ucdb_GetCoverage()
 *  Return the specified type of aggregated coverage.
 *
 *  Notes on efficiency:
 *
 *  From Questa 6.3d onward, this call may be made on an open database handle
 *  without fully populating the in-memory data image, see "Note on
 *  constant-time access to summary statistics" above.
 *
 *  If any significant data has changed since the last call, this forces an
 *  expensive recalculation using the entire database.  The aggregated coverage
 *  is automatically recalculated with ucdb_Close if necessary.  If there have
 *  been no significant data changes since the file was opened or the last call
 *  to ucdb_GetCoverage, this remains a cheap operation -- it is maintained as
 *  summary data in the database, for fast retrieval.
 *
 *  Note that the returned value may not equal ( num_covered_bins /
 *  num_total_bins ) for cases where coveritems can be weighted differently,
 *  and for SystemVerilog covergroups, where coverage is not only weighted but
 *  calculated hierarchically.
 *
 *  Return values:
 *      -1.0 means not applicable (i.e., no coveritems of the implied type in
 *      the database, *num_total_bins==0).
 *      Other negative value means error.
 */
float
ucdb_GetCoverage(
    ucdbT               db,
    ucdbSummaryEnumT    type,
    int*                num_covered_bins,   /* set if non-NULL */
    int*                num_total_bins);    /* set if non-NULL */

/*
 *  ucdb_GetStatistics()
 *  Return overall statistics for the database.  Recalculation applies as
 *  above.
 *  From Questa 6.3d onward, this call may be made on an open database handle
 *  without fully populating the in-memory data image, see "Note on
 *  constant-time access to summary statistics" above.
 *  Returns -1 with error.
 */
int
ucdb_GetStatistics(
    ucdbT               db,
    int*                num_covergroups,    /* covergroup types */
    int*                num_coverpoints,    /* covergroup coverpoints */
    int*                num_instances,      /* design instances */
    int*                num_dus);           /* number of design units */

/*----------------------------------------------------------------------------
 *  Creating coveritems (bins, with an associated count.)
 *--------------------------------------------------------------------------*/
/* typedef uint64_t ucdbCoverTypeT;           typedef for one of these: */
/* typedef uint64_t ucdbCoverMaskTypeT;       typedef for a set of these: */

/* Bits for ucdbCoverTypeT: */
#define UCDB_CVGBIN          /* For SV Covergroups: */ \
                             INT64_LITERAL(0x0000000000000001)
#define UCDB_COVERBIN        /* For cover directives- pass: */ \
                             INT64_LITERAL(0x0000000000000002)
#define UCDB_ASSERTBIN       /* For assert directives- fail: */ \
                             INT64_LITERAL(0x0000000000000004)
#define UCDB_SCBIN           /* For SystemC transactions: */ \
                             INT64_LITERAL(0x0000000000000008)
#define UCDB_ZINBIN          /* For 0-in Checkerware: */ \
                             INT64_LITERAL(0x0000000000000010)
#define UCDB_STMTBIN         /* For Code coverage(Statement): */ \
                             INT64_LITERAL(0x0000000000000020)
#define UCDB_BRANCHBIN      /* For Code coverage(Branch): */ \
                             INT64_LITERAL(0x0000000000000040)
#define UCDB_EXPRBIN         /* For Code coverage(Expression): */ \
                             INT64_LITERAL(0x0000000000000080)
#define UCDB_CONDBIN         /* For Code coverage(Condition): */ \
                             INT64_LITERAL(0x0000000000000100)
#define UCDB_TOGGLEBIN       /* For Code coverage(Toggle): */ \
                             INT64_LITERAL(0x0000000000000200)
#define UCDB_PASSBIN         /* For assert directives- pass count: */ \
                             INT64_LITERAL(0x0000000000000400)
#define UCDB_FSMBIN          /* For FSM coverage: */ \
                             INT64_LITERAL(0x0000000000000800)
#define UCDB_USERBIN         /* User-defined coverage: */ \
                             INT64_LITERAL(0x0000000000001000)
#define UCDB_GENERICBIN      UCDB_USERBIN
#define UCDB_COUNT           /* user-defined count, not in coverage: */ \
                             INT64_LITERAL(0x0000000000002000)
#define UCDB_FAILBIN         /* For cover directives- fail count: */ \
                             INT64_LITERAL(0x0000000000004000)
#define UCDB_VACUOUSBIN      /* For assert- vacuous pass count: */ \
                             INT64_LITERAL(0x0000000000008000)
#define UCDB_DISABLEDBIN     /* For assert- disabled count: */ \
                             INT64_LITERAL(0x0000000000010000)
#define UCDB_ATTEMPTBIN      /* For assert- attempt count: */ \
                             INT64_LITERAL(0x0000000000020000)
#define UCDB_ACTIVEBIN       /* For assert- active thread count: */ \
                             INT64_LITERAL(0x0000000000040000)
#define UCDB_IGNOREBIN       /* For SV Covergroups: */ \
                             INT64_LITERAL(0x0000000000080000)
#define UCDB_ILLEGALBIN      /* For SV Covergroups: */ \
                             INT64_LITERAL(0x0000000000100000)
#define UCDB_DEFAULTBIN      /* For SV Covergroups: */ \
                             INT64_LITERAL(0x0000000000200000)
#define UCDB_PEAKACTIVEBIN   /* For assert- peak active thread count: */ \
                             INT64_LITERAL(0x0000000000400000)
#define UCDB_USERBITS        /* For user-defined coverage: */ \
                             INT64_LITERAL(0x00000000FF000000)
#define UCDB_RESERVEDBIN     INT64_LITERAL(0xFF00000000000000)

/* Coverage item types */

#define UCDB_COVERGROUPBINS \
            ((ucdbCoverMaskTypeT)(UCDB_CVGBIN | \
                                  UCDB_IGNOREBIN | \
                                  UCDB_ILLEGALBIN | \
                                  UCDB_DEFAULTBIN))

#define UCDB_FUNC_COV \
            ((ucdbCoverMaskTypeT)(UCDB_COVERGROUPBINS | \
                                  UCDB_COVERBIN | \
                                  UCDB_SCBIN))

#define UCDB_CODE_COV \
            ((ucdbCoverMaskTypeT)(UCDB_STMTBIN | \
                                  UCDB_BRANCHBIN | \
                                  UCDB_EXPRBIN | \
                                  UCDB_CONDBIN | \
                                  UCDB_TOGGLEBIN | \
                                  UCDB_FSMBIN))

#define UCDB_ASSERTIONBINS \
            ((ucdbCoverMaskTypeT)(UCDB_ASSERTBIN |\
                                  UCDB_PASSBIN |\
                                  UCDB_VACUOUSBIN |\
                                  UCDB_DISABLEDBIN |\
                                  UCDB_ATTEMPTBIN |\
                                  UCDB_ACTIVEBIN |\
                                  UCDB_PEAKACTIVEBIN))

#define UCDB_NO_BINS  ((ucdbCoverMaskTypeT)INT64_ZERO)
#define UCDB_ALL_BINS ((ucdbCoverMaskTypeT)INT64_NEG1)

/*------------------------------------------------------------------------------
 *  Creating and manipulating coveritems
 *----------------------------------------------------------------------------*/

/*
 *  Flags for coveritem data
 */
#define UCDB_IS_32BIT        0x00000001  /* data is 32 bits */
#define UCDB_IS_64BIT        0x00000002  /* data is 64 bits */
#define UCDB_IS_VECTOR       0x00000004  /* data is actually a vector */
#define UCDB_HAS_GOAL        0x00000008  /* goal included */
#define UCDB_HAS_WEIGHT      0x00000010  /* weight included */
#define UCDB_EXCLUDE_PRAGMA  0x00000020  /* excluded by pragma  */
#define UCDB_EXCLUDE_FILE    0x00000040  /* excluded by file; does not
                                            count in total coverage */
#define UCDB_LOG_ON          0x00000080  /* for cover/assert directives:
                                            controls simulator output */
#define UCDB_ENABLED         0x00000100  /* generic enabled flag; if disabled,
                                            still counts in total coverage */
#define UCDB_HAS_LIMIT       0x00000200  /* for limiting counts */
#define UCDB_HAS_ACTION      0x00000400  /* for assert directives, refer to
                                           "ACTION" in attributes */
#define UCDB_IS_FSM_RESET    0x00000400  /* For fsm reset states */
#define UCDB_IS_ASSERT_DEBUG 0x00000800  /* for assert directives, if true, has
                                            4 counts */
#define UCDB_IS_TLW_ENABLED  0x00001000  /* for assert directives, future use
                                            in QuestaSim  */
#define UCDB_IS_FSM_TRAN     0x00002000  /* for FSM coveritems, is a transition
                                            bin */
#define UCDB_IS_BR_ELSE      0x00004000  /* for branch ELSE coveritems */
#define UCDB_CLEAR_PRAGMA    0x00008000
#define UCDB_IS_EOS_NOTE     0x00010000  /* for directives active at end of simulation */
#define UCDB_EXCLUDE_INST    0x00020000  /* for instance-specific exclusions */
#define UCDB_EXCLUDE_AUTO    0x00040000  /* for automatic exclusions */


/* For Zero Information in "flags" */
#define UCDB_BIN_IFF_EXISTS  0x00100000  /* covergroup bin has no iff */
#define UCDB_BIN_SAMPLE_TRUE 0x00200000  /* covergroup bin is not sampled */

#define UCDB_IS_CROSSAUTO    0x00400000  /* covergroup auto cross bin */

#define UCDB_COVERFLAG_MARK  0x00800000  /* flag for temporary mark */
#define UCDB_USERFLAGS       0xFF000000  /* reserved for user flags */

#define UCDB_FLAG_MASK       0xFFFFFFFF

#define UCDB_EXCLUDED        (UCDB_EXCLUDE_FILE | UCDB_EXCLUDE_PRAGMA | UCDB_EXCLUDE_INST | UCDB_EXCLUDE_AUTO)

/*
 *  Type representing coveritem data.
 */
typedef union {
    uint64_t            int64;      /* if UCDB_IS_64BIT */
    uint32_t            int32;      /* if UCDB_IS_32BIT */
    unsigned char*      bytevector; /* if UCDB_IS_VECTOR */
} ucdbCoverDataValueT;

typedef struct {
    ucdbCoverTypeT      type;       /* type of coveritem */
    ucdbFlagsT          flags;      /* as above, validity of fields below */
    ucdbCoverDataValueT data;
    /*
     *  This "goal" value is used to determine whether an individual bin is
     *  covered; it corresponds to "at_least" in a covergroup:
     */
    int                 goal;       /* if UCDB_HAS_GOAL */
    int                 weight;     /* if UCDB_HAS_WEIGHT */
    int                 limit;      /* if UCDB_HAS_LIMIT */
    int                 bitlen;     /* length of data.bytevector in bits,
                                     * extra bits are lower order bits of the
                                     * last byte in the byte vector
                                     */
} ucdbCoverDataT;

/*
 *  ucdb_CreateNextCover()
 *  Create the next coveritem in the given scope.
 *  Returns the index number of the created coveritem, -1 if error.
 *  Note: in write streaming mode, "name" is not copied; it needs to be
 *  preserved unchanged until the next ucdb_WriteStream* call or the next
 *  ucdb_Create* call.
 */
int
ucdb_CreateNextCover(
    ucdbT               db,
    ucdbScopeT          parent,     /* coveritem will be created in this scope */
    const char*         name,       /* name of coveritem, can be NULL */
    ucdbCoverDataT*     data,       /* associated data for coverage */
    ucdbSourceInfoT*    sourceinfo);

/*
 *  ucdb_CloneCover()
 *  This function creates an exact copy of the given coveritem into
 *  the targetparent. Predefined attributes will always be created by default.
 *  There is no effect of this function when targetdb is in streaming mode.
 *  A successful operation will return the coverindex, and -1 for error.
 */
int
ucdb_CloneCover(
    ucdbT               targetdb,     /* database context for clone */
    ucdbScopeT          targetparent, /* parent of clone */
    ucdbT               sourcedb,     /* source database */
    ucdbScopeT          sourceparent, /* source scope */
    int                 coverindex,   /* source coverindex */
    ucdbSelectFlagsT    cloneflags);  /* either UCDB_CLONE_ATTRS or 0 */

/*
 *  ucdb_RemoveCover()
 *  This function removes the given cover from its parent.
 *  There is no effect of this function in streaming modes.
 *  A successful operation will return 0, and -1 for error.
 *  Note: Coveritems can not be removed from scopes of type UCDB_ASSERT,
 *  need to remove the whole scope instead.
 *  Similarly, coveritems from scopes of type UCDB_TOGGLE which has toggle kind
 *  UCDB_TOGGLE_SCALAR, or UCDB_TOGGLE_SCALAR_EXT, or UCDB_TOGGLE_REG_SCALAR,
 *  or UCDB_TOGGLE_REG_SCALAR_EXT cannot be removed. The scope needs to be
 *  removed in this case too.
 *  Also, this function should be used carefully if it is
 *  used during iteration of coveritems using any coveritem
 *  iteration API, otherwise the iteration may not be complete.
 */
int
ucdb_RemoveCover(
    ucdbT               db,
    ucdbScopeT          parent,
    int                 coverindex);

/*
 *  ucdb_MatchCoverInScope()
 *  Get coverage item from database if it exists in given scope.
 *  Returns coveritem index or -1 if error.
 */
int
ucdb_MatchCoverInScope(
    ucdbT               db,
    ucdbScopeT          parent,     /* parent of coveritem */
    const char*         name);

/*
 *  ucdb_MatchCoverByPath()
 *  Get coverage item from database if it exists as named, uses path separator
 *  set in database.  See ucdb_GetPathSeparator().
 *  Returns 1 if found, 0 if not found.
 *
 *  IMPORTANT NOTE (DEPRECATED): this function is deprecated because it is not
 *  designed to handle scopes named the same with the same parent.  Instead,
 *  use ucdb_PathCallBack() which has the added advantage of wildcard matching.
 *  However, this function can work well if you are confident there is 1 and
 *  only 1 object named as specified for every component of the path.
 */
int
ucdb_MatchCoverByPath(
    ucdbT               db,
    const char*         pathname,
    ucdbScopeT*         parent,         /* parent scope if found */
    int*                coverindex);    /* cover index within scope if found */


/*
 *  ucdb_IncrementCover()
 *  Increment the data count for a coverage data item, if not a vector item.
 */
int
ucdb_IncrementCover(
    ucdbT               db,
    ucdbScopeT          parent,     /* parent scope of coveritem */
    int                 coverindex, /* index of coveritem in parent */
    int64_t             increment); /* added to current count */

/*
 *  ucdb_GetCoverFlags()
 *  Get coveritem's flag.
 */
ucdbFlagsT
ucdb_GetCoverFlags(
    ucdbT               db,
    ucdbScopeT          parent,      /* parent scope of coveritem */
    int                 coverindex); /* index of coveritem in parent */

/*
 *  ucdb_GetCoverFlag()
 *  Return 1 if specified coveritem's flag bit matches the given mask.
 */
int
ucdb_GetCoverFlag(
    ucdbT               db,
    ucdbScopeT          parent,     /* parent scope of coveritem */
    int                 coverindex, /* index of coveritem in parent */
    ucdbFlagsT          mask);

/*
 *  ucdb_SetCoverFlag()
 *  Set bits in the coveritem's flag field with respect to the given mask --
 *  set all bits to 0 or 1.
 */
void
ucdb_SetCoverFlag(
    ucdbT               db,
    ucdbScopeT          parent,     /* parent scope of coveritem */
    int                 coverindex, /* index of coveritem in parent */
    ucdbFlagsT          mask,
    int                 bitvalue);  /* 0 or 1 only */

/*
 *  ucdb_GetCoverType()
 *  Get the cover type of the coveritem.
 */
ucdbCoverTypeT
ucdb_GetCoverType(
    ucdbT               db,
    ucdbScopeT          parent,     /* parent scope of coveritem */
    int                 coverindex);/* index of coveritem in parent */

/*
 *  ucdb_GetCoverData()
 *  Get all the data for a coverage item, returns 0 for success, and non-zero
 *  for any error.  It is the user's responsibility to save the returned data,
 *  the next call to this function will invalidate the returned data.
 *  Note: any of the data arguments may be NULL, in which case data is not
 *  retrieved.
 */
int
ucdb_GetCoverData(
    ucdbT               db,
    ucdbScopeT          parent,     /* parent scope of coveritem */
    int                 coverindex, /* index of coveritem in parent */
    char**              name,
    ucdbCoverDataT*     data,
    ucdbSourceInfoT*    sourceinfo);

/*
 *  ucdb_SetCoverData()
 *  Set the data for a coverage item, returns 0 for success, and non-zero
 *  for any error.  It is the user's responsibility to make all the data
 *  fields valid.
 */
int
ucdb_SetCoverData(
    ucdbT               db,
    ucdbScopeT          parent,     /* parent scope of coveritem */
    int                 coverindex, /* index of coveritem in parent */
    ucdbCoverDataT*     data);

/*
 *  ucdb_SetCoverCount()
 *  Set the count for a coverage item, returns 0 for success, and non-zero
 *  for any error.
 */
int
ucdb_SetCoverCount(
    ucdbT               db,
    ucdbScopeT          parent,     /* parent scope of coveritem */
    int                 coverindex, /* index of coveritem in parent */
    int64_t             count);

/*
 *  ucdb_SetCoverGoal()
 *  Set the goal for a coverage item, returns 0 for success, and non-zero
 *  for any error.
 */
int
ucdb_SetCoverGoal(
    ucdbT               db,
    ucdbScopeT          parent,     /* parent scope of coveritem */
    int                 coverindex, /* index of coveritem in parent */
    int                 goal);

/*
 *  ucdb_SetCoverLimit()
 *  Set the limit for a coverage item, returns 0 for success, and non-zero
 *  for any error.
 */
int
ucdb_SetCoverLimit(
    ucdbT               db,
    ucdbScopeT          parent,     /* parent scope of coveritem */
    int                 coverindex, /* index of coveritem in parent */
    int                 limit);

/*
 *  ucdb_SetCoverWeight()
 *  Set the weight for a coverage item, returns 0 for success, and non-zero
 *  for any error.
 */
int
ucdb_SetCoverWeight(
    ucdbT               db,
    ucdbScopeT          parent,     /* parent scope of coveritem */
    int                 coverindex, /* index of coveritem in parent */
    int                 weight);

/*
 *  ucdb_GetScopeNumCovers()
 *  Get the number of coveritems in the given scope.  May return 0.
 *  Returns -1 if error.
 */
int
ucdb_GetScopeNumCovers(
    ucdbT               db,
    ucdbScopeT          scope);

/*
 *  ucdb_GetECCoverNumHeaders()
 *  Returns the number of UDP header columns for Condition and
 *  Expression coverage.
 *
 *  To get all the header columns, do:
 *  num_columns = ucdb_GetECCoverNumHeaders(db, cvitem);
 *  for (i = 0; i < num_columns; i++) {
 *      char* header;
 *      status = ucdb_GetECCoverHeader(db, cvitem, i, &header);
 *  }
 */
int
ucdb_GetECCoverNumHeaders(
    ucdbT               db,
    ucdbScopeT          scope);

/*
 *  ucdb_GetECCoverHeader()
 *  Returns the indexed UDP header string of Condition and Expression coverage.
 */
int
ucdb_GetECCoverHeader(
    ucdbT               db,
    ucdbScopeT          scope,
    int                 index,
    char**              header);


/*-----------------------------------------------------------------------------
 *  Toggle functions
 *
 *  Toggles have a specific interface in the API because:
 *  -   Toggles are by far the most common type of object in a typical code
 *      coverage database; they can be optimized with a restricted API.
 *  -   Net toggles may be duplicated throughout the database through port
 *      connections and need to be reported once rather than in as many
 *      different local scopes as they appear; this requires a net id.
 *
 *---------------------------------------------------------------------------*/
typedef enum {
    UCDB_TOGGLE_ENUM,           /* Enum type object */
    UCDB_TOGGLE_INT,            /* Integer type object */
    UCDB_TOGGLE_REG_SCALAR=4,   /* Scalar, one bit reg */
    UCDB_TOGGLE_REG_SCALAR_EXT, /* Extended toggle of scalar reg */
    UCDB_TOGGLE_SCALAR,         /* Scalar net, or std_logic_bit */
    UCDB_TOGGLE_SCALAR_EXT,     /* Ext toggle of scalar net or std_logic_bit*/
    UCDB_TOGGLE_REAL            /* Real type object */
} ucdbToggleTypeT;

typedef enum {
    UCDB_TOGGLE_INTERNAL,       /* non-port: internal wire or variable */
    UCDB_TOGGLE_IN,             /* input port */
    UCDB_TOGGLE_OUT,            /* output port */
    UCDB_TOGGLE_INOUT           /* inout port */
} ucdbToggleDirT;

/*
 *  ucdb_CreateToggle()
 *  Create the given toggle scope underneath the given parent scope.
 *  The "canonical_name" identifies unique toggles; toggles with the same
 *  canonical_name must count once when traversed for a report or coverage
 *  summary. Can be NULL for unconnected nets, enum, int, and reg type toggles.
 *  Returns handle to created scope, of type UCDB_TOGGLE.
 *  NOTE: Set UCDB_IS_TOP_NODE in flags if the node is a canonical node and
 *  the type is UCDB_TOGGLE_SCALAR or UCDB_TOGGLE_SCALAR_EXT.
 *  Note: in write streaming mode, "name" and "canonical_name" are not copied;
 *  it needs to be preserved unchanged until the next ucdb_WriteStream* call
 *  or the next ucdb_Create* call.
 */
ucdbScopeT
ucdb_CreateToggle(
    ucdbT               db,
    ucdbScopeT          parent,     /* toggle will be created in this scope */
    const char*         name,       /* name of toggle object */
    const char*         canonical_name, /* canonical_name of toggle object */
    ucdbFlagsT          flags,      /* for exclusion flags only */
    ucdbToggleTypeT     toggle_type,
    ucdbToggleDirT      toggle_dir);

/*
 *  ucdb_GetToggleInfo()
 *  Returns toggle-specific information associated with a toggle scope. The
 *  memory for canonical_name is allocated by the system and must not be
 *  de-allocated by the user. The canonical_name may be NULL for some cases:
 *  unconnected nets, enum, int, and reg type toggles.
 *  Return 0 with success, -1 any error.
 */
int
ucdb_GetToggleInfo(
    ucdbT               db,
    ucdbScopeT          toggle,
    const char**        canonical_name,
    ucdbToggleTypeT*    toggle_type,
    ucdbToggleDirT*     toggle_dir);

/*
 *  ucdb_GetToggleCovered()
 *  Returns 1 if the given toggle is covered, 0 if not, -1 if error.
 *  In-memory mode only.
 */
int
ucdb_GetToggleCovered(
    ucdbT               db,
    ucdbScopeT          toggle);

/*
 *  ucdb_GetBCoverInfo()
 *  If the branch is a CASE then returns 1, otherwise(for IF) returns 0.
 */
int
ucdb_GetBCoverInfo(
    ucdbT               db,
    ucdbScopeT          coveritem,
    int*                has_else,
    int*                iscase,
    int*                num_elmts);   /* Returns value 1 for case branch */


/* #########################################################################
 * ##### TAGS -- begin
 * ######################################################################### */

/*
 * Enum type for different object kinds.
 * This is a bit mask for the different
 * kinds of objects which may be tagged.
 * Mask values may be and'ed and or'ed
 * together.
 */
typedef enum {
    UCDB_OBJ_ERROR = 0,    /* Start of the database, apply initial settings */
    UCDB_OBJ_TESTDATA = 1, /* Testdata object */
    UCDB_OBJ_SCOPE = 2,    /* Scope object */
    UCDB_OBJ_COVER = 4,    /* Cover object */
    UCDB_OBJ_ANY = -1      /* ucdbScopeT or ucdbHistoryNodeT */
} ucdbObjMaskT;

/*------------------------------------------------------------------------------
 *  Tags
 *
 *  For grouping, objs may have associated tags.  Things that share the same
 *  tag are associated together.  When UCDB_TESTPLAN objs share tags with
 *  coverage objs that contain coveritems, the association may be used to do
 *  test traceability analysis.
 *
 *  In general, a tag is just a number of strings associated with the obj.
 *
 *  Here is an example of traversing all non-testplan objs that share a tag
 *  with a given testplan obj:
 *
 *  if (ucdb_ObjKind(db,obj)==UCDB_OBJ_SCOPE
 *      && ucdb_GetScopeType(db,(ucdbScopeT)obj)==UCDB_TESTPLAN) {
 *      int t, numtags = ucdb_GetObjNumTags(db,obj);
 *      const char* tagname;
 *      for ( t=0; t<numtags; t++ ) {
 *          int found;
 *          ucdbObjT taggedobj;
 *          ucdb_GetObjIthTag(db,obj,t,&tagname);
 *          for ( found=ucdb_BeginTaggedObj(db,tagname,&taggedobj);
 *                found; found=ucdb_NextTaggedObj(db,&taggedobj) ) {
 *              if (ucdb_ObjKind(db,taggedobj)==UCDB_OBJ_SCOPE
 *                  && ucdb_GetScopeType(db,(ucdbScopeT)taggedobj)
 *                     ==UCDB_TESTPLAN)
 *                  continue;
 *
 *              // Now taggedobj is a non-testplan obj sharing a tag with
 *              // obj -- put your code here
 *          }
 *      }
 *  }
 *
 *----------------------------------------------------------------------------*/

/*
 *  ucdb_ObjKind()
 *  Given 'obj' return the kind of object that it is.
 *  (i.e. Either ucdbScopeT or ucdbHistoryNodeT)
 */
ucdbObjMaskT
ucdb_ObjKind(ucdbT db, ucdbObjT obj);

/*
 *  ucdb_AddObjTag()
 *  Add a tag to a given obj.
 *  Returns 0 with success, non-zero with error.
 *  Error includes null tag or tag with '\n' character.
 */
int
ucdb_AddObjTag(
    ucdbT               db,
    ucdbObjT            obj, /* ucdbScopeT or ucdbHistoryNodeT */
    const char*         tag);

/*
 *  ucdb_RemoveObjTag()
 *  Remove the given tag from the obj.
 *  Returns 0 with success, non-zero with error.
 */
int
ucdb_RemoveObjTag(
    ucdbT               db,
    ucdbObjT            obj, /* ucdbScopeT or ucdbHistoryNodeT */
    const char*         tag);

/*
 *  ucdb_GetObjNumTags()
 *  Get the number of tags from a given obj.
 *  Returns number of tags, 0 with error or no tags.
 */
int
ucdb_GetObjNumTags(
    ucdbT               db,
    ucdbObjT            obj);  /* ucdbScopeT or ucdbHistoryNodeT */

/*
 *  ucdb_GetObjIthTag()
 *  Get indexed tag from a given obj.
 *  Returns 0 with success, non-zero with error.
 */
int
ucdb_GetObjIthTag(
    ucdbT               db,
    ucdbObjT            obj,  /* ucdbScopeT or ucdbHistoryNodeT */
    int                 index,
    const char**        tag);

/*
 *  ucdb_SetObjTags()
 *  Set all tags for a given a obj.  This replaces previous tags; if
 *  numtags==0, clears all tags.
 *  Returns 0 with success, non-zero with error.
 */
int
ucdb_SetObjTags(
    ucdbT               db,
    ucdbObjT            obj,        /* ucdbScopeT or ucdbHistoryNodeT */
    int                 numtags,    /* size of tag_array, 0 to clear */
    const char**        tag_array); /* array of string pointers */

/*
 *  ucdb_BeginTaggedObj()
 *  Returns the first obj that exists with the given tag.
 *  Returns 1 if the tag exists in the database, 0 otherwise.
 *  When it returns 1, *p_obj will be non-NULL.
 *  In-memory mode only.
 */
int
ucdb_BeginTaggedObj(
    ucdbT               db,
    const char*         tagname,
    ucdbObjT*           p_obj);     /* ucdbScopeT or ucdbHistoryNodeT */

/*
 *  ucdb_NextTaggedObj()
 *  Must be called immediately after ucdb_BeginTaggedObj, re-uses tag from
 *  previous call.
 *  Returns the next obj that exists with the given tag.
 *  Returns 1 if the next object exists in the database, otherwise 0.
 *  When it returns 1, *p_obj will be non-NULL.
 *  In-memory mode only.
 */
int
ucdb_NextTaggedObj(
    ucdbT               db,
    ucdbObjT*           p_obj);    /* ucdbScopeT or ucdbHistoryNodeT */

/*
 *  ucdb_AddScopeTag() -- [DEPRECATED: Use ucdb_AddObjTag()]
 *  Add a tag to a given scope.
 *  Returns 0 with success, non-zero with error.
 *  Error includes null tag or tag with '\n' character.
 */
int
ucdb_AddScopeTag(
    ucdbT               db,
    ucdbScopeT          scope,
    const char*         tag);

/*
 *  ucdb_RemoveScopeTag() -- [DEPRECATED: Use ucdb_RemoveObjTag()]
 *  Remove the given tag from the scope.
 *  Returns 0 with success, non-zero with error.
 */
int
ucdb_RemoveScopeTag(
    ucdbT               db,
    ucdbScopeT          scope,
    const char*         tag);

/*
 *  ucdb_GetScopeNumTags() -- [DEPRECATED: Use ucdb_GetObjNumTags()]
 *  Get the number of tags from a given scope.
 *  Returns number of tags, 0 with error or no tags.
 */
int
ucdb_GetScopeNumTags(
    ucdbT               db,
    ucdbScopeT          scope);

/*
 *  ucdb_GetScopeIthTag() --  [DEPRECATED: Use ucdb_GetObjIthTag()]
 *  Get indexed tag from a given scope.
 *  Returns 0 with success, non-zero with error.
 */
int
ucdb_GetScopeIthTag(
    ucdbT               db,
    ucdbScopeT          scope,
    int                 index,
    const char**        tag);

/*
 *  ucdb_SetScopeTags() -- [DEPRECATED: Use ucdb_SetOBJTags()]
 *  Set all tags for a given a scope.  This replaces previous tags; if
 *  numtags==0, clears all tags.
 *  Returns 0 with success, non-zero with error.
 */
int
ucdb_SetScopeTags(
    ucdbT               db,
    ucdbScopeT          scope,
    int                 numtags,    /* size of tag_array, 0 to clear */
    const char**        tag_array); /* array of string pointers */

/*
 *  ucdb_BeginTagged() -- [DEPRECATED: Use ucdb_BeginTaggedObj()]
 *  Returns the first scope that exists with the given tag.
 *  Returns 1 if the tag exists in the database, 0 otherwise.
 *  When it returns 1, *p_scope will be non-NULL.
 *  In-memory mode only.
 */
int
ucdb_BeginTagged(
    ucdbT               db,
    const char*         tagname,
    ucdbScopeT*         p_scope);

/*
 *  ucdb_NextTagged() -- [DEPRECATED: Use ucdb_NextTaggedObj()]
 *  Must be called immediately after ucdb_BeginTagged, re-uses tag from
 *  previous call.
 *  Returns the next scope that exists with the given tag.
 *  Returns 1 if the next object exists in the database, otherwise 0.
 *  When it returns 1, *p_scope will be non-NULL.
 *  In-memory mode only.
 */
int
ucdb_NextTagged(
    ucdbT               db,
    ucdbScopeT*         p_scope);

/*
 *  ucdb_NextTag()
 *  This is an iterator for returning the set of all tags in the UCDB file.
 *  In-memory mode only.  Returns NULL when traversal is done or with error.
 *
 *  Here is an example of traversing all scopes for all tags in a UCDB file:
 *
 *      ucdbT db = ucdb_Open(filename);
 *      const char* tagname = NULL;
 *      while (tagname = ucdb_NextTag(db,tagname)) {
 *          int found;
 *          ucdbScopeT scope;
 *          for ( found=ucdb_BeginTagged(db,tagname,&scope); found;
 *                found=ucdb_NextTagged(db,&scope) ) {
 *              // Put your code here //
 *          }
 *      }
 *
 *  IMPORTANT NOTE: this traversal can't nest; code inside this loop can't
 *  re-use the same set of functions.
 */
const char*
ucdb_NextTag(
    ucdbT               db,
    const char*         tagname);

/* #########################################################################
 * ##### TAGS -- end
 * ######################################################################### */

/******************************************************************************
 *  Test Traceability Support
 *
 *  Associating tests and coverage objects.
 *
 *  Coveritems or scopes may be associated with one of the ucdbTestT records
 *  in the database through this API.
 *
 *  IMPORTANT NOTE on the tests and coverage object association:
 *
 *  For compactness, this is implemented as a bit vector associated with each
 *  coverage object, where each bit corresponds to a test in the list of test
 *  data records in the database.  Consequently, this is dependent on the
 *  ordering of test data records being stable.  If test data records are
 *  removed (with ucdb_RemoveTest()), all test-coverage associations can be
 *  invalidated.
 *
 *****************************************************************************/

/*
 *  ucdb_AssocCoverTest()
 *  Associate a scope or coveritem with the given test data record.  This may
 *  be done for any purpose, but is most logically done to indicate that the
 *  given test incremented or covered the bin; in-memory mode only.
 *  Returns 0 for success, -1 for failure (e.g., coverindex out-of-bounds.)
 *
 *  Note this is not supported for the scope only (coverindex==(-1)).
 */
int
ucdb_AssocCoverTest(
    ucdbT               db,
    ucdbTestT           testdata,
    ucdbScopeT          scope,
    int                 coverindex);    /* -1 not supported */

/*
 *  ucdb_NextCoverTest()
 *  Get next test record associated with the given scope or coveritem.
 *  Returns first with NULL as input, returns NULL when list is exhausted.
 *  This is in-memory mode only.
 *
 *  Note this is not supported for the scope only (coverindex==(-1)).
 */
ucdbTestT
ucdb_NextCoverTest(
    ucdbT               db,
    ucdbScopeT          scope,
    int                 coverindex,     /* -1 not supported */
    ucdbTestT           test);

/*
 *  Get a vector whose bits correspond to the test data records in the
 *  database.  This can be used for efficient implementation.  When using
 *  ucdb_SetCoverTestMask() or other functions reading the bit vector,
 *  bitlength takes priority over bytelength, either will be ignored if set to
 *  -1.  Both may not be set to -1.  Setting length to 0 will erase the
 *  attribute.
 */
typedef struct {
    unsigned char*      bitvector;      /* LSBs are filled first */
    int                 bitlength;      /* length in bits */
    int                 bytelength;     /* length in bytes */
} ucdbBitVectorT;

/*
 *  These are optional but may be convenient, they enforce the
 *  conventions for bitlength vs. bytelength in the ucdbBitVectorT:
 */
#define ucdb_SetBitVectorLengthBits(bitvector,numbits) \
        { (bitvector).bitlength = (numbits); \
          (bitvector).bytelength = ((((bitvector).bitlength)/8) \
                                   + ((((bitvector).bitlength)%8) ? 1 : 0)); }

#define ucdb_SetBitVectorLengthBytes(bitvector,numbytes) \
        { (bitvector).bytelength = (numbytes); \
          (bitvector).bitlength = ((bitvector).bytelength) * 8; }

#define ucdb_GetBitVectorLengthBytes(bitvector) \
        ((bitvector).bitlength >= 0 ? \
            (((bitvector).bitlength/8) + (((bitvector).bitlength%8) ? 1 : 0)) \
            : (bitvector).bytelength)

#define ucdb_GetBitVectorLengthBits(bitvector) \
        ((bitvector).bitlength >= 0 ? \
            (bitvector).bitlength : (bitvector).bytelength * 8)

/*
 *  ucdb_GetCoverTestMask()
 *  Returns a bit vector whose bits correspond to the associated test data
 *  records in the database.  First bit (mask.bitvector[0]&0x01) corresponds to
 *  first test retrieved by ucdb_NextTest(), subsequent bits correspond in
 *  order to subsequent test data records.  If tests are saved in an array,
 *  this allows quick retrieval of all associated tests in a single call.
 *  Note: bitvector storage is not to be de-allocated by the user.
 *  Returns 0 for success, -1 for error.  mask.bitvector == NULL if none,
 *  lengths == 0.
 *
 *  Note this always sets both bitlength and bytelength on the bitvector.
 *
 *  Note this is not supported for the scope only (coverindex==(-1)).
 */
int
ucdb_GetCoverTestMask(
    ucdbT               db,
    ucdbScopeT          scope,
    int                 coverindex,     /* -1 not supported */
    ucdbBitVectorT*     mask);

/*
 *  ucdb_SetCoverTestMask()
 *  Write a bit vector whose bits correspond to the associated test data
 *  records in the database.  This is for write-streaming versions of the API
 *  and not as foolproof as ucdb_AssocCoverTest().  See details for read
 *  function above.  When initializing mask, be careful with the rules for
 *  setting bitlength and bytelength, see above.
 *  Note: bitvector storage is copied by this routine.
 *  Returns 0 for success, -1 for error.
 *
 *  Note this is not supported for the scope only (coverindex==(-1)).
 */
int
ucdb_SetCoverTestMask(
    ucdbT               db,
    ucdbScopeT          scope,
    int                 coverindex,     /* -1 not supported */
    ucdbBitVectorT*     mask);

/*
 *  ucdb_OrCoverTestMask()
 *  This ORs the required bit for the given test data record.
 *  Returns 0 for success, non-zero for error.
 */
int
ucdb_OrCoverTestMask(
    ucdbT               db,
    ucdbBitVectorT*     mask,
    ucdbTestT           test);

/*
 *  ucdb_CalcCoverageSummary()
 *  This calculates coverage summary statistics, the same data as above, on a
 *  subset of an opened database.
 *  In-memory mode only.
 *
 *  Note on efficiency:
 *
 *  From Questa 6.3d onward, if called with a NULL scope and NULL test_mask,
 *  this call may be made on an open database handle without fully populating
 *  the in-memory data image, see "Note on constant-time access to summary
 *  statistics" above.
 *
 *  Note: when called on an instance, it will report by-du coverage only for
 *  the case where UCDB_INST_ONCE is set for the instance; then by-du coverage
 *  and instance coverage will be identical.  When called on the entire
 *  database, coverage from all DUs and all instances will be counted.
 *
 *  Note: when "test_mask" is set, the database must have been created with all
 *  coveritems containing a cover test mask.  (This could be as a result of
 *  running a "test-associated merge".)  If so, only coveritems matching the
 *  test_mask will be considered covered in the calculation; this is prone to
 *  some possible error and can be improved with additional data in the future.
 *  Setting test_mask to NULL will calculate coverage based on current bin
 *  values only.
 *
 *  Note on "recurse_instances":
 *  For non-testplan scopes, this flag causes a recursion into subscopes of
 *  types matching the mask UCDB_HDL_INST_SCOPE.
 *  For testplan scopes, this causes recursion into scopes of type
 *  UCDB_TESTPLAN.  One type of recursion always occurs with testplan scopes:
 *  following non-testplan scopes that share a tag with the "scope" given to
 *  this routine.
 */
int
ucdb_CalcCoverageSummary(
    ucdbT                   db,
    ucdbScopeT              scope,      /* NULL implies entire database */
    int                     recurse_instances,  /* see note above */
    ucdbCoverageSummaryT*   data,
    ucdbBitVectorT*         test_mask); /* optional test mask, see above */

/*
 *  ucdb_GetTotalCoverage()
 *  This calculates a single coverage number (as a percentage, 0.0-100.0) for a
 *  scope in the database.
 *
 *  The following are the rules:
 *  -   For a coverage scope, this is the total coverage calculated in a way
 *      similar to ucdb_CalcCoverageSummary().
 *  -   The mode set with ucdb_SetExprCondMode() will choose whether focused
 *      expressions/conditions or UDP expression/conditions contribute to the
 *      total coverage.
 *  -   For a design instance, this is the weighted average of coverage per
 *      type, for all types found in the design subtree rooted at that
 *      instance.
 *      NOTE: "weighted average of coverage per type" uses weights as set from
 *      ucdb_SetWeightPerType() and retrieved by ucdb_GetWeightPerType().
 *  -   For a leaf testplan scope, coverage is the weighted average of all
 *      design instance or coverage scopes sharing the same tag.
 *  -   For a non-leaf testplan scope, coverage is the weighted average of
 *      coverage of all children.  If the non-leaf testplan scope shares a tag
 *      with design or coverage scopes, those collectively are equally weighted
 *      as one child testplan instance -- as if there were a virtual child
 *      testplan scope that shared a tag with all the other design and coverage
 *      scopes.
 *  -   Assertion results are included in the form of "% non-vacuously passed",
 *      that is, the percentage of assertions that non-vacuously passed at
 *      least once (non-zero non-vacuous pass count).
 *  -   Test data records with status attribute values UCDB_TESTSTATUS_OK and
 *      UCDB_TESTSTATUS_WARNING count as 100%; other test data records count as
 *      0%.
 *
 *  Returns 1 if the scope had any coverage data.  Returns 0 if none was found
 *  (also sets total_coverage to -1.0.)
 *  Return -1 for error.
 *
 *  Note: when "test_mask" is set, the database must have been created with all
 *  coveritems containing a cover test mask.  (This could be as a result of
 *  running a "test-associated merge".)  If so, only coveritems matching the
 *  test_mask will be considered covered in the calculation; this is prone to
 *  some possible error and can be improved with additional data in the future.
 *  Setting test_mask to NULL will calculate coverage based on current bin
 *  values only.
 *
 *  TBD: need to provide weights per-type & try to anticipate test plan weight
 *  overrides.
 */
int
ucdb_GetTotalCoverage(
    ucdbT                   db,
    ucdbObjT                obj,        /* ucdbScopeT or ucdbHistoryNodeT, NULL
                                           implies all roots */
    float*                  total_coverage,
    ucdbBitVectorT*         test_mask); /* optional test mask, see above */


/*------------------------------------------------------------------------------
 *  Iterators for coveritems.
 *----------------------------------------------------------------------------*/
/*
 *  ucdb_NextCoverInScope
 *  Given a coveritem, get the next coveritem from the scope, according to the
 *  given cover type mask.
 *  Start with coverindex==(-1) to return the first coveritem in the scope.
 *  Returns 0 at end of traversal, -1 if error.
 */
int
ucdb_NextCoverInScope(
    ucdbT               db,
    ucdbScopeT          parent,     /* parent scope of coveritem */
    int*                coverindex, /* index of coveritem in parent */
    ucdbCoverMaskTypeT  covermask); /* mask for type of coveritem */

/*
 *  ucdb_NextCoverInDB
 *  Given a coveritem, get the next coveritem from the database, according to
 *  the given cover type mask.
 *  Start with coverindex==(-1) and parent==NULL to return the first coveritem
 *  in the database.
 *  Returns 0 at end of traversal, -1 if error.
 */
int
ucdb_NextCoverInDB(
    ucdbT               db,
    ucdbScopeT*         parent,     /* parent scope of coveritem */
    int*                coverindex, /* index of coveritem in parent */
    ucdbCoverMaskTypeT  covermask); /* mask for type of coveritem */

/* #########################################################################
 * ##### FORMAL -- begin
 * ######################################################################### */

typedef enum {
    UCDB_FORMAL_NONE         /* No formal information - default */
                             = 0x00000000,
    UCDB_FORMAL_FAILURE      /* Can be proven to fail */
                             = 0x00000001,
    UCDB_FORMAL_PROOF        /* Formal proof */
                             = 0x00000002,
    UCDB_FORMAL_VACUOUS      /* Vacuous formal proof -- never evaluates */
                             = 0x00000004,
    UCDB_FORMAL_INCONCLUSIVE /* Who knows? */
                             = 0x00000008,
    UCDB_FORMAL_ASSUMPTION   /* Assume directive */
                             = 0x00000010,
    UCDB_FORMAL_CONFLICT     /* Merge conflict */
                             = 0x00000080
} ucdbAssertFormalModeT;

/*
 * Four routines for setting/clearing and reading this data:
 *
 * These routines should only be called on a UCDB_ASSERT scope.
 * When a non-zero value is returned by the following routines
 * (i.e. an error case), that routine will have issued a message
 * via the UCDB error handler mechanism. The caller should ideally
 * not print any error message out, but rather rely on the UCDB's
 * error message system to return back the message via the message callback.
 */

/*
 * ucdb_SetFormalMode
 *
 * "mode" may be one of:
 *     UCDB_FORMAL_NONE
 *     UCDB_FORMAL_FAILURE
 *     UCDB_FORMAL_PROOF
 *     UCDB_FORMAL_VACUOUS
 *     UCDB_FORMAL_INCONCLUSIVE
 *     UCDB_FORMAL_ASSUMPTION or
 *     UCDB_FORMAL_CONFLICT.
 * If any input parameter is not valid or consistent with simulation results,
 * then the return int value will be non-zero and the scope data will not be
 * overwritten. Otherwise, the scope data will be overwritten and zero will be
 * returned. To reflect the intention of the mode, this function will
 * implicitly create/modify the bins under it as needed.
 *
 * Note: Any preexisting value is ignored.
 */
int
ucdb_SetFormalMode(
    ucdbT db,
    ucdbScopeT assertscope,
    ucdbAssertFormalModeT mode);

/*
 * ucdb_GetFormalMode
 *
 * "mode" may be set to one of:
 *     UCDB_FORMAL_NONE
 *     UCDB_FORMAL_FAILURE
 *     UCDB_FORMAL_PROOF
 *     UCDB_FORMAL_VACUOUS
 *     UCDB_FORMAL_INCONCLUSIVE
 *     UCDB_FORMAL_ASSUMPTION or
 *     UCDB_FORMAL_CONFLICT.
 * If any input parameter is not valid or consistent with simulation results,
 * then the return int value will be non-zero and the "mode" will not be
 * updated. Otherwise, the "mode" will be updated and zero will be returned.
 */
int
ucdb_GetFormalMode(
    ucdbT db,
    ucdbScopeT assertscope,
    ucdbAssertFormalModeT *mode);

/*
 * ucdb_SetProofRadius
 *
 * "radius" is an integer (negative values result in a blank being displayed).
 * If any input parameter is not valid or consistent with simulation results,
 * then the return int value will be non-zero and the scope data will not be
 * overwritten. Otherwise, the scope data will be overwritten and zero will be
 * returned.
 *
 * Note: Any preexisting value is ignored.
 */
int
ucdb_SetProofRadius(ucdbT db, ucdbScopeT assertscope, int radius);

/*
 * ucdb_GetProofRadius
 *
 * "radius" is an integer (negative values result in a blank being displayed).
 * If any input parameter is not valid or consistent with simulation results,
 * then the return int value will be non-zero and the scope data will not be
 * overwritten. Otherwise, "radius" will be overwritten and zero will be
 * returned.
 */
int
ucdb_GetProofRadius(ucdbT db, ucdbScopeT assertscope, int *radius);

/* #########################################################################
 * ##### FORMAL -- end
 * ######################################################################### */

/* #########################################################################
 * ##### GROUP -- begin
 * ######################################################################### */

#define UCDB_GROUP_MASK_PACKED  0x1000
#define UCDB_GROUP_MASK_ORDERED 0x2000
typedef enum {
    UCDB_GROUP_BASIC           = 0x0001, 
    UCDB_GROUP_UNPACKED_STRUCT = 0x0002, 
    UCDB_GROUP_UNPACKED_UNION  = 0x0003, 
    UCDB_GROUP_UNPACKED_ARRAY  = (0x0004|UCDB_GROUP_MASK_ORDERED), 
    UCDB_GROUP_ASSOC_ARRAY     = 0x0005,
    UCDB_GROUP_PACKED_STRUCT   
		= (UCDB_GROUP_UNPACKED_STRUCT|UCDB_GROUP_MASK_PACKED), 
    UCDB_GROUP_PACKED_UNION    
		= (UCDB_GROUP_UNPACKED_UNION|UCDB_GROUP_MASK_PACKED), 
    UCDB_GROUP_PACKED_ARRAY    
		= (UCDB_GROUP_UNPACKED_ARRAY|UCDB_GROUP_MASK_PACKED)
} ucdbGroupKind;

/*
 *  ucdb_CreateGroupScope()
 *
 *  Create the given scope underneath the given parent scope.
 *  Returns scope pointer or NULL if error.
 *  Note: in write streaming mode, "name" and "rangePairs" are not copied; 
 *  they need to be preserved unchanged until the next ucdb_WriteStream*
 *  call or the next ucdb_Create call.
 *
 */
ucdbScopeT
ucdb_CreateGroupScope(
    ucdbT         db,
    ucdbScopeT    parent,
    ucdbGroupKind kind,               /* The group kind */
    char*         name,               /* name of group object */
	ucdbFlagsT    flags,
    int           numberOfRangePairs, /* Used only for ordered groups */
    int*          rangePairs);        /* Used only for ordered groups */

/*
 *  ucdb_GetGroupInfo()
 *
 *  Returns group-specific information associated with a group scope. The
 *  memory for the names and for rangePairs are allocated by the system 
 *  and must not be de-allocated by the user. 
 *  Return 0 with success, -1 any error.
 */
int
ucdb_GetGroupInfo(
    ucdbT          db,
    ucdbScopeT     group,
    ucdbGroupKind* kind,               /* The group kind */
    const char**   name,               /* name of group object */
    int*           numberOfRangePairs, /* Used only for ordered groups */
    int**          rangePairs);        /* Used only for ordered groups */

/*
 *  ucdb_ExpandOrderedGroupRangeList()
 *
 *  The group scope must be either a UCDB_GROUP_PACKED_ARRAY 
 *  or UCDB_GROUP_UNPACKED_ARRAY group scope.
 *  Expands the groups range pairs to include the supplied range list:
 *    - Partial overlaps with an existing range will expand the existing range.
 *    - Non-overlaping ranges will be added.
 *    - Ranges completely enclosed by existing ranges will be ignored.
 *    - Existing ranges will be replaced by ranges completely enclosing them.
 *  Return 0 with success, -1 any error.
 */
int
ucdb_ExpandOrderedGroupRangeList(
    ucdbT      db,
    ucdbScopeT group,
    int        numberOfRangePairs,
    int*       rangePairs);

/*
 *  ucdb_GetOrderedGroupElementByIndex()
 *
 *  Finds the child of an ordered group scope specified by index.
 *  The parent scope must be either a UCDB_GROUP_PACKED_ARRAY 
 *  or UCDB_GROUP_UNPACKED_ARRAY group scope.
 *  Returns child scope pointer 
 *      or NULL if error or no element for the given index.
 *
 *  Note #1: Example of an ordered group corresponding to bus[3:1],
 *      Index '1' will get the rightmost range number (i.e. '1')
 *      Index '3' will get the leftmost range number (i.e. '3').
 *  Note #2: Memory mode only.
 */
ucdbScopeT
ucdb_GetOrderedGroupElementByIndex(
    ucdbT       db,
    ucdbScopeT  parent,
    int         index);

/* #########################################################################
 * ##### GROUP -- end
 * ######################################################################### */

/*------------------------------------------------------------------------------
 *  Simulator Memory Usage Statistics
 *
 *  This API supports summary statistics for simulator memory usage.  When
 *  merged, the maximum statistic of all merge inputs is taken for the merged
 *  output.
 *----------------------------------------------------------------------------*/
/*
 *  Enumerator for category of statistics
 */
typedef enum {
    UCDB_MEMSTATS_COVERGROUP,   /* covergroup */
    UCDB_MEMSTATS_ASSERT,       /* assertion */
    UCDB_MEMSTATS_CONSTRAINT,   /* constraint solver */
    UCDB_MEMSTATS_CLASS,        /* classes */
    UCDB_MEMSTATS_DYNAMIC,      /* dynamic objects */
    UCDB_MEMSTATS_OTHER,        /* other categories */
    UCDB_MEMSTATS_ENDCATEGORY   /* marker past last value */
} ucdbMemStatsEnumT;

/*
 *  Enumerator for type of statistic, used in combination with category above.
 */
typedef enum {
    UCDB_MEMSTATS_MAXMEM,       /* All categories: maximum memory usage high
                                   water mark) -- bytes */
    UCDB_MEMSTATS_PEAKTIME,     /* All categories: peak memory time */
    UCDB_MEMSTATS_CURRMEM,      /* All categories: current memory usage at time
                                   of saving the UCDB file -- bytes */
    UCDB_MEMSTATS_NUMOBJECTS,   /* All categories: number of objects */

    UCDB_MEMSTATS_ENDTYPE       /* marker past last value */
} ucdbMemStatsTypeEnumT;

/*
 *  ucdb_GetMemoryStats
 *  Return summary statistics regarding simulator memory usage.
 *  From Questa 6.3d onward, this call may be made on an open database handle
 *  without fully populating the in-memory data image, see "Note on
 *  constant-time access to summary statistics" above.
 *  Returns 0 with success, -1 with usage error, 1 if statistic does not apply.
 *
 *  Note: value will be set to point to memory owned by the UCDB; do not free.
 */
int
ucdb_GetMemoryStats(
    ucdbT                   db,
    ucdbMemStatsEnumT       category,   /* category of statistic */
    ucdbMemStatsTypeEnumT   type,       /* type of statistic */
    ucdbAttrValueT**        value);     /* value and type indicator */

/*
 *  ucdb_SetMemoryStats
 *  Set summary statistics regarding simulator memory usage.
 *  Returns 0 with success, non-zero with any error.
 */
int
ucdb_SetMemoryStats(
    ucdbT                   db,
    ucdbMemStatsEnumT       category,   /* category of statistic */
    ucdbMemStatsTypeEnumT   type,       /* type of statistic */
    ucdbAttrValueT*         value);     /* value and type indicator */

#ifdef __cplusplus
}
#endif

#endif
