/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    basic_transaction_table.sv
 * Description:  OVM Basic Transaction Table Class
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         16.8.2012
 * ************************************************************************** */

 `include "ovm_macros.svh"

 package BasicTransactionTable_pkg;
  
   //include official ovm package
   import ovm_pkg::*;
 
  /*!
   * Transaction's comparison rules 
   *  
   * Transaction table behaviour - it compares all transactions (FIFO) or first
   * transaction (FIRST_ONLY) in the table with coming transaction
   */
   typedef enum {TR_TABLE_FIFO, TR_TABLE_FIRST_ONLY} tTrTableBehav;

  /*!
   * \brief BasicTransactionTable
   * 
   * This class is parent class for any transaction table.
   *  
   * This class contains transaction table and adds and removes transactions 
   * from the table according to special rules defined by tTrTableBehav. 
   * 
   * \param behav     - selected comparison rule
   * \param TransType - type of transaction that is stored into the table     
   */
   class BasicTransactionTable #(int behav = TR_TABLE_FIRST_ONLY, 
                       type TransType = BasicTransaction) extends ovm_component;
     
     //registration of component tools
     `ovm_component_utils(BasicTransactionTable)

    /*
     * Public Class Atributes
     */
     tTransMbx tr_table = new(0); //! Mailbox
     integer added;               //! Items added to transaction table
     integer removed;             //! Items removed from transaction table

    /*! 
     * Constructor - creates BasicTransactionTable object  
     *
     * \param name     - transaction instance name
     * \param parent   - parent class identification
     */  
     function new (string name, ovm_component parent);
       super.new(name, parent);
       added = 0;
       removed = 0;
     endfunction: new
   
    /*! 
     * Build - instanciates child components
     */     
     function void build;
       super.build();
     endfunction: build

    /*! 
     * Adds transaction items to the transaction table
     */    
     task add(TransType transaction);
       this.tr_table.put(transaction);
       added++;
     endtask: add

    /*! 
     * Remove transaction items from the transaction table
     */ 
     task remove(TransType transaction, inout bit status, input int kind = -1);
       string diff;
       Transaction tr;
       status=0;
    
       //compares all transactions in the table with coming transaction
       //KED BUDE VSETKO FRCAT, TREBA ODKOMENTOVAT A ODLADIT!
       /*if (behav==TR_TABLE_FIFO)begin  
         for(int i=0; i < tr_table.size; i++) begin 
           if (tr_table[i].compare(transaction,diff, kind)==1) begin
             this.tr_table.delete(i);
             status=1;
             removed++;
             break;
           end
         end
       end*/
     
       // compares first transaction in the table with coming transaction
       if (behav == TR_TABLE_FIRST_ONLY) begin
         tr_table.peek(tr);
         if (tr.compare(transaction,diff,kind)==1)begin
           status=1;
           tr_table.get(tr);
           removed++;
         end 
       end     
     endtask: remove
   
    /*! 
     * Display the actual state of transaction table
     */
     task display(integer full=1, string inst = "");
       TransType tr;
        $write("------------------------------------------------------------\n");
        $write("-- %s: TRANSACTION TABLE\n", inst);
        $write("------------------------------------------------------------\n");
        $write("Size: %d\n", tr_table.num());
        $write("Items added: %d\n", added);
        $write("Items removed: %d\n", removed);
        $write("\n");
        if (full) begin
           $write("!!! REMAINING TRANSACTIONS !!!\n\n");
           while (tr_table.num() != 0) begin
             tr_table.get(tr);
             tr.display();
             //foreach(tr_table[i]) tr_table[i].display();
           end  
        end   
        $write("------------------------------------------------------------\n");
     endtask: display

   endclass : BasicTransactionTable
 
 endpackage: BasicTransactionTable_pkg