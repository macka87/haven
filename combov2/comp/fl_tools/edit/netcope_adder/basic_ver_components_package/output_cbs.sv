/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Output Callback Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** *
 
/*!
 * \brief Output Callback 
 * 
 * This is a abstract class for creating objects which get benefits from
 * function callback. Inheritence from this basic class is neaded for 
 * functionality.
 */
 class OutputCbs;
   
   /*
    * Private Class Methods
    */

   /*! 
    * Preprocessing call 
    */
    virtual task pre_tr(ref Transaction transaction, byte id);
      // By default, callback does nothing
    endtask : pre_tr
    
   /*! 
    * Postprocessing call - function is called before a transaction is sended to
    * scoreboard. It is usefull for transaction modifications.
    */
    virtual task post_tr(Transaction transaction, byte id);
      // By default, callback does nothing
    endtask: post_tr
 endclass : OutputCbs

