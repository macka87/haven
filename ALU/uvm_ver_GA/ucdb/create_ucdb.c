/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_ucdb.c
 * Description:  UVM UCDB database API functions for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         23.8.2013
 * ************************************************************************** */
 
#include "ucdb.h"
#include <stdio.h>
#include <stdlib.h>

#define QUESTA_RELEASE 64   /* valid values: 63 64 */

const char* UCDBFILE = "alu.ucdb"; 

/*
 *  Create a filehandle from the given file in the current directory
 *  (Works on UNIX variants only, because of the reliance on the PWD
 *  environment variable.)
 *  Note this allows the UCDB API to create a global file table; you may create
 *  your own file tables by using ucdb_SrcFileTableAppend()
 */
ucdbFileHandleT
create_filehandle(ucdbT db,
                  const char* filename)
{
    ucdbFileHandleT filehandle;
    const char* pwd = getenv("PWD");
    ucdb_CreateSrcFileHandleByName(db,&filehandle,
                                   NULL,    /* let API create file table */
                                   filename,
                                   pwd);
    return filehandle;
}

/*
 *  Create test data.  For the most part, this is hardcoded to be identical to
 *  the test data for the example created with Questa.
 */
void
create_testdata(ucdbT db,
                const char* ucdbfile)
{
    ucdb_AddTest(db,
        ucdbfile,
        "test",                 /* test name */
        UCDB_TESTSTATUS_OK,     /* test status */
        0.0,                    /* simulation time */
        "ns",                   /* simulation time units */
        0.0,                    /* CPU time */
        "0",                    /* random seed */
        NULL,                   /* test script: not used by Questa */
                                /* simulator arguments: */
        "-coverage -do 'run -all; coverage save test.ucdb; quit' -c top ",
        NULL,                   /* comment */
        0,                      /* compulsory */
        "20070824143300",       /* fake date */
        "userid"                /* fake userid */
        );
}

/*
 *  Create a covergroup of the given name under the given parent.
 *  This hardcodes the type_options to the defaults.
 */
ucdbScopeT
create_covergroup(ucdbT db,
                  ucdbScopeT parent,
                  const char* name,
                  ucdbFileHandleT filehandle,
                  int line)
{
    ucdbScopeT cvg;
    ucdbSourceInfoT srcinfo;
    ucdbAttrValueT attrvalue;
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0;                  /* fake token # */
    cvg = ucdb_CreateScope(db,parent,name,
                           &srcinfo,
                           1,           /* from type_option.weight */
                           UCDB_SV,     /* source language type */
                           UCDB_COVERGROUP,
                           0);          /* flags */
    /* Hardcoding attribute values to defaults for type_options: */
    attrvalue.type = UCDB_ATTR_INT;
    attrvalue.u.ivalue = 100;
    ucdb_AttrAdd(db,cvg,-1,UCDBKEY_GOAL,&attrvalue);
    attrvalue.u.ivalue = 0;
    ucdb_AttrAdd(db,cvg,-1,UCDBKEY_STROBE,&attrvalue);
    attrvalue.u.ivalue = 1;
    ucdb_AttrAdd(db,cvg,-1,UCDBKEY_MERGEINSTANCES,&attrvalue);
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = "";
    ucdb_AttrAdd(db,cvg,-1,UCDBKEY_COMMENT,&attrvalue);
    return cvg;
}

/*
 *  Create a covergroup of the given name under the given parent.
 *  This hardcodes the type_options to the defaults.
 */
ucdbScopeT
create_coverpoint(ucdbT db,
                  ucdbScopeT parent,
                  const char* name,
                  ucdbFileHandleT filehandle,
                  int line,
                  int is_under_instance)
{
    ucdbScopeT cvp;
    ucdbSourceInfoT srcinfo;
    ucdbAttrValueT attrvalue;
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0;                  /* fake token # */
    cvp = ucdb_CreateScope(db,parent,name,
                           &srcinfo,
                           1,           /* from type_option.weight */
                           UCDB_SV,     /* source language type */
                           UCDB_COVERPOINT,
                           0);          /* flags */
    /* Hardcoding attribute values to defaults for type_options: */
    attrvalue.type = UCDB_ATTR_INT;
    attrvalue.u.ivalue = 100;
    ucdb_AttrAdd(db,cvp,-1,UCDBKEY_GOAL,&attrvalue);
    attrvalue.u.ivalue = 1;
    ucdb_AttrAdd(db,cvp,-1,UCDBKEY_ATLEAST,&attrvalue);
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = "";
    ucdb_AttrAdd(db,cvp,-1,UCDBKEY_COMMENT,&attrvalue);
#if (QUESTA_RELEASE == 64)
    if (is_under_instance) {
        attrvalue.type = UCDB_ATTR_INT;
        attrvalue.u.ivalue = 64;
        ucdb_AttrAdd(db,cvp,-1,UCDBKEY_AUTOBINMAX,&attrvalue);
        attrvalue.u.ivalue = 0;
        ucdb_AttrAdd(db,cvp,-1,UCDBKEY_DETECTOVERLAP,&attrvalue);
    }
#endif
    return cvp;
}

/*
 *  Create a coverpoint bin of the given name, etc., under the given
 *  coverpoint.
 *  Note: the right-hand-side value for a bin is the value(s) that can cause
 *  the bin to increment if sampled.
 */
void
create_coverpoint_bin(ucdbT db,
                      ucdbScopeT parent,
                      const char* name,
                      ucdbFileHandleT filehandle,
                      int line,
                      int at_least,
                      int count,
                      const char* binrhs)   /* right-hand-side value */
{
    ucdbSourceInfoT srcinfo;
    ucdbCoverDataT coverdata;
    ucdbAttrValueT attrvalue;
    int coverindex;
    coverdata.type = UCDB_CVGBIN;
    coverdata.flags = UCDB_IS_32BIT | UCDB_HAS_GOAL | UCDB_HAS_WEIGHT;
    coverdata.goal = at_least;
    coverdata.weight = 1;
    coverdata.data.int32 = count;
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0;                  /* fake token # */
    coverindex = ucdb_CreateNextCover(db,parent,name,
                                      &coverdata,&srcinfo);
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = binrhs;
    ucdb_AttrAdd(db,parent,coverindex,UCDBKEY_BINRHSVALUE,&attrvalue);
}

/*
     // activity coverpoint
     actH : coverpoint alu_in_trans.act {
       bins act1          = {1};    
       ignore_bins act_ig = {0};
     } 
*/     

/*
 *  top-level example code
 */ 
void
example_code(const char* ucdbfile)
{
    ucdbFileHandleT filehandle;
    ucdbScopeT cvg, cvp, cvip;
    ucdbT db = ucdb_Open(NULL); 
    create_testdata(db,ucdbfile);
    filehandle = create_filehandle(db,"alu_in_coverage_monitor.sv");
    
    /*
    du = create_design_unit(db,"work.top",filehandle,0);
    instance = create_instance(db,"top",NULL,du); */
    
    cvg = create_covergroup(db,NULL,"alu_in_covergroup",filehandle,44);
    cvp = create_coverpoint(db,cvg,"actH",filehandle,47,0);
    create_coverpoint_bin(db,cvp,"act1",filehandle,48,1,0,"1");
    
#if (QUESTA_RELEASE == 64)
    /*
     *  6.4 stores covergroup instances:
     */
    /* cvi = create_coverinstance(db,cvg,"\\/top/cv ",filehandle,16);  */
    cvip = create_coverpoint(db,NULL,"actH",filehandle,47,1);
    create_coverpoint_bin(db,cvip,"act1",filehandle,48,1,0,"1");
#endif

    printf("Writing UCDB file '%s'\n", ucdbfile);
    /* write database to file, NULL = entire database, -1 = all coverage types*/
    ucdb_Write(db,ucdbfile,NULL,1,-1);
    /* deallocation od database in memory */
    ucdb_Close(db);
}

/*
 *  Error handler and main program
 */
void
error_handler(void *data,
              ucdbErrorT *errorInfo)
{
    fprintf(stderr, "UCDB Error %d: %s\n",
            errorInfo->msgno, errorInfo->msgstr);
    if (errorInfo->severity == UCDB_MSG_ERROR)
        exit(1);
}

int
main(int argc, char* argv[])
{
    ucdb_RegisterErrorHandler(error_handler, NULL);
    example_code(UCDBFILE);
    return 0;
}   
