/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Input Callback Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** *
 
/*!
 * \brief Input Callback 
 * 
 * This is a abstract class for creating objects which get benefits from
 * function callback. Inheritence from this basic class is needed for 
 * functionality.
 */
 class InputCbs;
    
   /*
    * Private Class Methods
    */

   /*! 
    * Preprocessing call - function is called before a transaction is sended to
    * DUT. It is usefull for transaction modifications.
    */     
    virtual task pre_tr(ref Transaction transaction, byte id);
      // By default, callback does nothing
    endtask: pre_tr
    
   /*! 
    * Postprocessing call - function is called before a transaction is sended to
    * scoreboard. It is usefull for transaction modifications.
    */
    virtual task post_tr(Transaction transaction, byte id);
      // By default, callback does nothing
    endtask: post_tr
 endclass : InputCbs

