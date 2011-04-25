/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Transaction Table Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */


/*!
 * Transaction's comparison rules 
 *  
 * Transaction table behaviour - it compares all transactions (FIFO) or first
 * transaction (FIRST_ONLY) in the table with coming transaction
 */
 typedef enum {TR_TABLE_FIFO, TR_TABLE_FIRST_ONLY} tTrTableBehav;

/*!
 * Transaction Table Class 
 *  
 * This class contains transaction table and adds and removes transactions from 
 * the table according to special rules defined by tTrTableBehav. 
 * 
 * \param behav     - selected comparison rule
 * \param TransType - type of transaction that is stored into the table     
 */
 class TransactionTable #(int behav = TR_TABLE_FIRST_ONLY, 
                          type TransType = Transaction);
   
   /*
    * Public Class Atributes
    */
    //TransType tr_table[$];     //! Table of transactions
    //semaphore sem;             //! Semaphore solves problems with concurent acces
    tTransMbx tr_table = new(0); //! Mailbox
    integer added;               //! Items added to transaction table
    integer removed;             //! Items removed from transaction table
        
   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates transaction table object  
    */
    function new();
      //sem = new(1);
      added = 0;
      removed = 0;
    endfunction
   
   /*
    * Private Class Methods
    */  
    
   /*! 
    * Adds transaction items to the transaction table
    */    
    task add(TransType transaction);
      //lock();
      //this.tr_table.push_back(transaction);
      this.tr_table.put(transaction);
      added++;
      //unlock();
    endtask: add
    
   /*! 
    * Remove transaction items from the transaction table
    */ 
    task remove(TransType transaction, ref bit status, input int kind = -1);
      string diff;
      Transaction tr;
      status=0;
    
     // lock();

     //compares all transactions in the table with coming transaction
     /*if (behav==TR_TABLE_FIFO)begin  
       for(integer i=0; i < this.tr_table.size; i++) begin 
         if (this.tr_table[i].compare(transaction,diff, kind)==1) begin
           this.tr_table.delete(i);
           status=1;
           removed++;
           break;
         end
       end
     end*/
      
     // compares first transaction in the table with coming transaction
     /*if (behav==TR_TABLE_FIRST_ONLY && tr_table.size > 0) begin
       TransType elem = this.tr_table.pop_front();
       if (elem.compare(transaction,diff, kind)==1) begin
         if (this.tr_table[0].compare(transaction,diff,kind)==1) begin
           this.tr_table.delete();
           status=1;
           removed++;
         end
         else begin
           this.tr_table.push_front(elem);
         end
     end*/ 
     
     if (behav == TR_TABLE_FIRST_ONLY) begin
       tr_table.get(tr);
         if (tr.compare(transaction,diff,kind)==1)begin
           status=1;
           removed++;
         end  
     end     
    
     //  unlock();     
   endtask: remove 
 
   /*! 
    * Lock scoreboard
    */ 
    //task lock();
    //   sem.get(1);  //! Semaphore is set to lock 
    //endtask: lock

   /*! 
    * Unlock scoreboard
    */
    //task unlock();
    //   sem.put(1);  //! Semaphore is set to unlock
    //endtask: unlock
    
   /*! 
    * Display the actual state of transaction table
    */
    task display(integer full=1, string inst = "");
      // lock();
      TransType tr;
       $write("------------------------------------------------------------\n");
       $write("-- %s TRANSACTION TABLE\n", inst);
       $write("------------------------------------------------------------\n");
       $write("Size: %d\n", tr_table.num());
       $write("Items added: %d\n", added);
       $write("Items removed: %d\n", removed);
       $write("\n");
       if (full) begin
          while (tr_table.num() != 0) begin
            $write("!!! REMAINING TRANSACTIONS !!!\n");
            tr_table.get(tr);
            tr.display();
            //foreach(tr_table[i]) tr_table[i].display();
          end  
       end   
       $write("------------------------------------------------------------\n");
       //unlock();
    endtask: display
 endclass : TransactionTable

