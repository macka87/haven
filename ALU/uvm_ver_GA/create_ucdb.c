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
 * UCDB_DU_MODULE
 */
ucdbScopeT
create_vlog_design_unit(ucdbT db,
                        const char* duname,
                        ucdbFileHandleT file,
                        int line)
{
    ucdbScopeT duscope;
    ucdbSourceInfoT srcinfo;
    ucdbAttrValueT attrvalue;
    srcinfo.filehandle = file;
    srcinfo.line = line;
    srcinfo.token = 0;                          /* fake token # */
    duscope = ucdb_CreateScope(db,
                               NULL,            /* DUs never have a parent */
                               duname,
                               &srcinfo,
                               1,               /* weight */
                               UCDB_VLOG,       /* source language */
                               UCDB_DU_MODULE,  /* scope type */
                               /* flags: */
                               UCDB_ENABLED_STMT | UCDB_ENABLED_BRANCH |
                               UCDB_ENABLED_COND | UCDB_ENABLED_EXPR |
                               UCDB_ENABLED_FSM | UCDB_ENABLED_TOGGLE |
                               UCDB_INST_ONCE | UCDB_SCOPE_UNDER_DU);
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = "FAKE DU SIGNATURE";
    ucdb_AttrAdd(db,duscope,-1,UCDBKEY_DUSIGNATURE,&attrvalue);
    return duscope;
}

/*
 * UCDB_DU_ARCH
 */
ucdbScopeT
create_vhdl_design_unit(ucdbT db,
                        const char* duname,
                        ucdbFileHandleT file,
                        int line)
{
    ucdbScopeT duscope;
    ucdbSourceInfoT srcinfo;
    ucdbAttrValueT attrvalue;
    srcinfo.filehandle = file;
    srcinfo.line = line;
    srcinfo.token = 0;                          /* fake token # */
    duscope = ucdb_CreateScope(db,
                               NULL,            /* DUs never have a parent */
                               duname,
                               &srcinfo,
                               1,               /* weight */
                               UCDB_VHDL,       /* source language */
                               UCDB_DU_ARCH,    /* scope type */
                               /* flags: */
                               UCDB_ENABLED_STMT | UCDB_ENABLED_BRANCH |
                               UCDB_ENABLED_COND | UCDB_ENABLED_EXPR |
                               UCDB_ENABLED_FSM | UCDB_ENABLED_TOGGLE |
                               UCDB_INST_ONCE | UCDB_SCOPE_UNDER_DU);
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = "FAKE DU SIGNATURE";
    ucdb_AttrAdd(db,duscope,-1,UCDBKEY_DUSIGNATURE,&attrvalue);
    return duscope;
}

/*
 * UCDB_INSTANCE contains a "DU" (design unit) or "type" pointer to one of:
 * UCDB_DU_MODULE, UCDB_DU_ARCH
 */ 
ucdbScopeT
create_instance(ucdbT db,
                const char* instname,
                ucdbScopeT parent,
                ucdbScopeT duscope)
{
    return
    ucdb_CreateInstance(db,parent,instname,
                        NULL,           /* source info: not used in Questa */
                        1,              /* weight */
                        UCDB_VLOG,      /* source language */
                        UCDB_INSTANCE,  /* instance of module/architecture */
                        duscope,        /* reference to design unit */
                        UCDB_INST_ONCE);/* flags */
}


/*
 * UCDB_DU_PACKAGE
 */
ucdbScopeT
create_vlog_package(ucdbT db,
                    const char* duname,
                    ucdbFileHandleT file,
                    int line)
{
    ucdbScopeT duscope;
    ucdbSourceInfoT srcinfo;
    ucdbAttrValueT attrvalue;
    srcinfo.filehandle = file;
    srcinfo.line = line;
    srcinfo.token = 0;                          /* fake token # */
    duscope = ucdb_CreateScope(db,
                               NULL,            /* DUs never have a parent ?????????????????????????????? */
                               duname,
                               &srcinfo,
                               1,               /* weight */
                               UCDB_SV,         /* source language */
                               UCDB_DU_PACKAGE, /* scope type */
                               /* flags: */
                               UCDB_ENABLED_STMT | UCDB_ENABLED_BRANCH |
                               UCDB_ENABLED_COND | UCDB_ENABLED_EXPR |
                               UCDB_ENABLED_FSM | UCDB_ENABLED_TOGGLE |
                               UCDB_INST_ONCE | UCDB_SCOPE_UNDER_DU);
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = "FAKE DU SIGNATURE";
    ucdb_AttrAdd(db,duscope,-1,UCDBKEY_DUSIGNATURE,&attrvalue);
    return duscope;
}

/*
 * UCDB_PACKAGE contains a "DU" (design unit) or "type" pointer to a:
 * UCDB_DU_PACKAGE
 */  
ucdbScopeT
create_package(ucdbT db,
               const char* instname,
               ucdbScopeT parent,
               ucdbScopeT duscope)
{
    return
    ucdb_CreateInstance(db,parent,instname,
                        NULL,           /* source info: not used in Questa */
                        1,              /* weight */
                        UCDB_VLOG,      /* source language */
                        UCDB_PACKAGE,  /* instance of module/architecture */
                        duscope,        /* reference to design unit */
                        UCDB_INST_ONCE);/* flags */
}

/*
 * UCDB_CLASS
 */
ucdbScopeT
create_class(ucdbT db,
             ucdbScopeT parent,
             const char* name,
             ucdbFileHandleT filehandle,
             int line)
{
    ucdbScopeT cls;
    ucdbSourceInfoT srcinfo;
    ucdbAttrValueT attrvalue;
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0;                          /* fake token # */
    cls = ucdb_CreateScope(db,parent,name,
                           &srcinfo,
                           1,           /* from type_option.weight */
                           UCDB_SV,     /* source language type */
                           UCDB_CLASS,
                           0);    
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = "FAKE DU SIGNATURE";
    ucdb_AttrAdd(db,cls,-1,UCDBKEY_DUSIGNATURE,&attrvalue);
    return cls;   
}

/*
 *  UCDB_COVERGROUP
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

#if (QUESTA_RELEASE == 64)
ucdbScopeT
create_coverinstance(ucdbT db,
                     ucdbScopeT parent,
                     const char* name,
                     ucdbFileHandleT filehandle,
                     int line)
{
    ucdbScopeT cvi;
    ucdbSourceInfoT srcinfo;
    ucdbAttrValueT attrvalue;
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0;                  /* fake token # */
    cvi = ucdb_CreateScope(db,parent,name,
                           &srcinfo,
                           1,           /* from type_option.weight */
                           UCDB_SV,     /* source language type */
                           UCDB_COVERINSTANCE,
                           0);          /* flags */
    /* Hardcoding attribute values to defaults for instance options: */
    attrvalue.type = UCDB_ATTR_INT;
    attrvalue.u.ivalue = 100;
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_GOAL,&attrvalue);
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = "";
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_COMMENT,&attrvalue);
    attrvalue.type = UCDB_ATTR_INT;
    attrvalue.u.ivalue = 1;
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_ATLEAST,&attrvalue);
    attrvalue.u.ivalue = 64;
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_AUTOBINMAX,&attrvalue);
    attrvalue.u.ivalue = 0;
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_DETECTOVERLAP,&attrvalue);
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_PERINSTANCE,&attrvalue);
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_NUMPRINTMISSING,&attrvalue);
    attrvalue.u.ivalue = 1;
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_GETINSTCOV,&attrvalue);
    return cvi;
}
#endif

/*
 *  UCDB_COVERPOINT
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
 *  UCDB_CVGBIN
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
 *  UCDB_IGNOREBIN
 */
void
create_coverpoint_ignore_bin(ucdbT db,
                      ucdbScopeT parent,
                      const char* name,
                      ucdbFileHandleT filehandle,
                      int line,
                      const char* binrhs)   /* right-hand-side value */
{
    ucdbSourceInfoT srcinfo;
    ucdbCoverDataT coverdata;
    ucdbAttrValueT attrvalue;
    int coverindex;
    coverdata.type = UCDB_IGNOREBIN;
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
 *  UCDB_ILLEGALBIN
 */
void
create_coverpoint_illegal_bin(ucdbT db,
                      ucdbScopeT parent,
                      const char* name,
                      ucdbFileHandleT filehandle,
                      int line,
                      const char* binrhs)   /* right-hand-side value */
{
    ucdbSourceInfoT srcinfo;
    ucdbCoverDataT coverdata;
    ucdbAttrValueT attrvalue;
    int coverindex;
    coverdata.type = UCDB_ILLEGALBIN;
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
    ucdbFileHandleT filehandle_top, filehandle_cov_pkg, filehandle_class_in, filehandle_class_out; 
    ucdbScopeT du_top, inst_top, du_alu, inst_alu, du_mult, inst_mult; 
    ucdbScopeT env_package, inst_env_pkg, alu_in_class, alu_out_class;  
    ucdbScopeT cvg_in, cvp_actH, cvp_moviH, cvp_operationH, cvp_op_after_op, cvp_opA, cvp_opB, cvp_opIMM, cvp_opMEM; 
        
    ucdbT db = ucdb_Open(NULL); 
    create_testdata(db,ucdbfile);
    
    /* TOP LEVEL */
    /*
     * HIERARCHY: Top_TB -> VHDL_DUT_U -> booth_mult_i
     */
    filehandle_top = create_filehandle(db, "top_level.sv");
    /* create UCDB_DU_MODULE */
    du_top = create_vlog_design_unit(db, "work.Top_TB", filehandle_top, 0);
    /* create UCDB_INSTANCE */
    inst_top = create_instance(db, "Top_TB", NULL, du_top);    
    /* create UCDB_DU_ARCH */
    du_alu = create_vhdl_design_unit(db, "work.alu_ent", filehandle_top, 0);
    /* create UCDB_INSTANCE */
    inst_alu = create_instance(db, "VHDL_DUT_U", inst_top, du_alu);
    /* create UCDB_DU_ARCH */
    du_mult =  create_vhdl_design_unit(db, "work.mult", filehandle_top, 0);
    /* create UCDB_INSTANCE */
    inst_mult = create_instance(db, "booth_mult_i", inst_alu, du_mult);
    
    /* ALU COVERAGE LEVEL */
    filehandle_cov_pkg = create_filehandle(db, "/env_lib/sv_alu_env_pkg.sv");
    /* create UCDB_DU_PACKAGE */
    env_package = create_vlog_package(db, "work.sv_alu_env_pkg", filehandle_cov_pkg, 0);
    /* create UCDB_PACKAGE */
    inst_env_pkg = create_package(db, "sv_alu_env_pkg", NULL, env_package);
    /* create UCDB_CLASS */
    filehandle_class_in = create_filehandle(db, "/env_lib/alu_in_coverage_monitor.svh");
    alu_in_class = create_class(db, inst_env_pkg, "AluInCoverageMonitor", filehandle_class_in, 0);
    /* create UCDB_COVERGROUP */
    cvg_in = create_covergroup(db, alu_in_class, "alu_in_covergroup", filehandle_class_in, 44);
    /* create UCDB_COVERPOINT */
    cvp_actH = create_coverpoint(db, cvg_in, "actH", filehandle_class_in, 47, 0);
    create_coverpoint_bin(db, cvp_actH, "act1", filehandle_class_in, 48, 100, 0, "1");
    create_coverpoint_ignore_bin(db, cvp_actH, "act_ig", filehandle_class_in, 49, "0");  
    
    cvp_moviH = create_coverpoint(db, cvg_in, "moviH", filehandle_class_in, 53, 0);
    create_coverpoint_bin(db, cvp_moviH, "movi_opB", filehandle_class_in, 54, 100, 0, "0"); 
    create_coverpoint_bin(db, cvp_moviH, "movi_opMEM", filehandle_class_in, 55, 100, 0, "1"); 
    create_coverpoint_bin(db, cvp_moviH, "movi_opIMM", filehandle_class_in, 56, 100, 0, "2");
    create_coverpoint_illegal_bin(db, cvp_moviH, "movi_ill_op", filehandle_class_in, 57, "3"); 
    
    cvp_operationH = create_coverpoint(db, cvg_in, "operationH", filehandle_class_in, 61, 0);
    create_coverpoint_bin(db, cvp_operationH, "auto[ADD]", filehandle_class_in, 62, 1, 0, "ADD"); 
    create_coverpoint_bin(db, cvp_operationH, "auto[SUB]", filehandle_class_in, 62, 1, 0, "SUB");
    create_coverpoint_bin(db, cvp_operationH, "auto[MULT]", filehandle_class_in, 62, 1, 0, "MULT");
    create_coverpoint_bin(db, cvp_operationH, "auto[SHIFT_RIGHT]", filehandle_class_in, 62, 1, 0, "SHIFT_RIGHT");
    create_coverpoint_bin(db, cvp_operationH, "auto[SHIFT_LEFT]", filehandle_class_in, 62, 1, 0, "SHIFT_LEFT");
    create_coverpoint_bin(db, cvp_operationH, "auto[ROTATE_RIGHT]", filehandle_class_in, 62, 1, 0, "ROTATE_RIGHT");
    create_coverpoint_bin(db, cvp_operationH, "auto[ROTATE_LEFT]", filehandle_class_in, 62, 1, 0, "ROTATE_LEFT");
    create_coverpoint_bin(db, cvp_operationH, "auto[NOT]", filehandle_class_in, 62, 1, 0, "NOT");
    create_coverpoint_bin(db, cvp_operationH, "auto[AND]", filehandle_class_in, 62, 1, 0, "AND");
    create_coverpoint_bin(db, cvp_operationH, "auto[OR]", filehandle_class_in, 62, 1, 0, "OR");
    create_coverpoint_bin(db, cvp_operationH, "auto[XOR]", filehandle_class_in, 62, 1, 0, "XOR");
    create_coverpoint_bin(db, cvp_operationH, "auto[NAND]", filehandle_class_in, 62, 1, 0, "NAND");
    create_coverpoint_bin(db, cvp_operationH, "auto[NOR]", filehandle_class_in, 62, 1, 0, "NOR");
    create_coverpoint_bin(db, cvp_operationH, "auto[XNOR]", filehandle_class_in, 62, 1, 0, "XNOR");
    create_coverpoint_bin(db, cvp_operationH, "auto[INC]", filehandle_class_in, 62, 1, 0, "INC");
    create_coverpoint_bin(db, cvp_operationH, "auto[DEC]", filehandle_class_in, 62, 1, 0, "DEC");
    
    cvp_op_after_op = create_coverpoint(db, cvg_in, "op_after_op", filehandle_class_in, 64, 0);
    create_coverpoint_bin(db, cvp_op_after_op, "auto[DEC=>DEC]", filehandle_class_in, 64, 1, 0, "DEC=>DEC"); 
    create_coverpoint_bin(db, cvp_op_after_op, "auto[DEC=>ADD]", filehandle_class_in, 64, 1, 0, "DEC=>ADD");
   
    cvp_opA = create_coverpoint(db, cvg_in, "opA", filehandle_class_in, 69, 0);
    create_coverpoint_bin(db, cvp_opA, "zeros", filehandle_class_in, 71, 1, 0, "0");
    
    
    cvp_opB = create_coverpoint(db, cvg_in, "opB", filehandle_class_in, 78, 0);
    cvp_opIMM = create_coverpoint(db, cvg_in, "opIMM", filehandle_class_in, 87, 0);
    cvp_opMEM = create_coverpoint(db, cvg_in, "opMEM", filehandle_class_in, 96, 0);
    
    /* create UCDB_CLASS */
    filehandle_class_out = create_filehandle(db, "/env_lib/alu_out_coverage_monitor.svh");
    alu_out_class = create_class(db, inst_env_pkg, "AluOutCoverageMonitor", filehandle_class_out, 0);  
    
       
    
    /*    
    cvg = create_covergroup(db,instance,"alu_in_covergroup",filehandle,44);
    cvp = create_coverpoint(db,cvg,"actH",filehandle,47,0);
    create_coverpoint_bin(db,cvp,"act1",filehandle,48,1,0,"1");  */
    
/*#if (QUESTA_RELEASE == 64)
    cvi = create_coverinstance(db,cvg,"\\/top/cv ",filehandle,16); 
    cvip = create_coverpoint(db,NULL,"actH",filehandle,47,1);
    create_coverpoint_bin(db,cvip,"act1",filehandle,48,1,0,"1");
#endif */

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
