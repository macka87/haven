/* *****************************************************************************
 * Project Name: HGEN Functional Verification 
 * File Name:    scoreboard.sv
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         24.4.2011         
 * ************************************************************************** */
 
/*!
 * \brief Bob Jenkins Hash Model 
 */
 class BJHModel;
    typedef bit[31:0] mytype;
   
    mytype init;
    
    function new(mytype init);
       this.init = init;
    endfunction
    
    function void mix(inout mytype a, inout mytype b, inout mytype c);
       a -= b; a -= c; a ^= (c>>13);
       b -= c; b -= a; b ^= (a<<8);
       c -= a; c -= b; c ^= (b>>13);
       a -= b; a -= c; a ^= (c>>12);
       b -= c; b -= a; b ^= (a<<16);
       c -= a; c -= b; c ^= (b>>5);
       a -= b; a -= c; a ^= (c>>3);
       b -= c; b -= a; b ^= (a<<10);
       c -= a; c -= b; c ^= (b>>15);
    endfunction
      
    function bit[95:0] hash(byte unsigned data[]);
       mytype a,b,c,len, i;
   
       /* Set up the internal state */
       len = data.size();
       a = 32'h9e3779b9;  /* the golden ratio; an arbitrary value */
       b = 32'h9e3779b9;  /* the golden ratio; an arbitrary value */
       c = this.init;     /* the previous hash value */
       i = 0;             /* index into data array */ 
      
       /*---------------------------------------- handle most of the key */
       while (len >= 12)
       begin
          a += (mytype'(data[i + 0]) + (mytype'(data[i + 1]) << 8) + (mytype'(data[i + 2]) << 16) + (mytype'(data[i + 3]) << 24));
          b += (mytype'(data[i + 4]) + (mytype'(data[i + 5]) << 8) + (mytype'(data[i + 6]) << 16) + (mytype'(data[i + 7]) << 24));
          c += (mytype'(data[i + 8]) + (mytype'(data[i + 9]) << 8) + (mytype'(data[i + 10]) << 16) + (mytype'(data[i + 11]) << 24));
          mix(a,b,c);
          i += 12; len -= 12;
       end
      
       /*------------------------------------- handle the last 11 bytes */
       c += data.size();

       if (len == 11)
       begin
          c += (mytype'(data[i + 10]) << 24);
          len--;
       end
         
       if (len == 10)
       begin
          c += (mytype'(data[i + 9]) << 16);
          len--;
       end
         
       if (len == 9)
       begin
          c += (mytype'(data[i + 8]) << 8);
          len--;
       end
         
       if (len == 8)
       begin
          b += (mytype'(data[i + 7]) << 24);
          len--;
       end
         
       if (len == 7)
       begin
          b += (mytype'(data[i + 6]) << 16);
          len--;
       end
         
       if (len == 6)
       begin
          b += (mytype'(data[i + 5]) << 8);
          len--;
       end
         
       if (len == 5)
       begin
          b += mytype'(data[i + 4]);
          len--;
       end
         
       if (len == 4)
       begin
          a += (mytype'(data[i + 3]) << 24);
          len--;
       end
         
       if (len == 3)
       begin
          a += (mytype'(data[i + 2]) << 16);
          len--;
       end
         
       if (len == 2)
       begin
          a += (mytype'(data[i + 1]) << 8);
          len--;
       end
         
       if (len == 1)
       begin
          a += mytype'(data[i + 0]);
          len--;
       end
         
       mix(a,b,c);
         
       return {a,b,c};
    endfunction
  endclass : BJHModel
  
/*!
 * \brief FrameLink Input Callbacks 
 *
 * This class is responsible adding transaction into transaction table and 
 * offers possibility to modify transaction.  
 *    
 * \param pChannels - count of channels
 * \param behav - TransactionTable behavior                
 */
 class ScoreboardInputCbs extends InputCbs;

     /*
      * Public Class Atributes
      */
      TransactionTable #(0) sc_table;
      int              flow_id_width;
      bit[31:0]        hgen_init;
      bit[63:0]        hgen_mask;

      int cnt;
     /*
      * Public Class Methods
      */

     /*! 
      * Constructor - creates driver callback object 
      *      
      * \param sc_table - transaction tables
      */ 
      function new (TransactionTable #(0) sc_table, int flow_id_width, bit[63:0] hgen_init, bit[63:0] hgen_mask);
         this.sc_table = sc_table;
         this.flow_id_width = flow_id_width;
         this.hgen_init = hgen_init;
         this.hgen_mask = hgen_mask;
         this.cnt = 0;
      endfunction
    
     /*! 
      * Transaction preprocessing
      *     
      * Function is called before transaction is sended to DUT.         
      * 
      * \param transaction - transaction     
      */
      virtual task pre_tr(ref Transaction transaction, byte id);
        // Transaction is not modified before sending to DUT
      endtask : pre_tr
    
     /*! 
      * Transaction postprocessing
      *
      * \param transaction - transaction 
      * \param inst        - driver identification         
      */
      virtual task post_tr(Transaction transaction, byte id);
        FrameLinkTransaction tr;
        FrameLinkTransaction res;
        bit[95:0] result;
        BJHModel bjh;
        byte unsigned data[];
        // BJH parametrs       
        bjh = new(hgen_init);
        
        $cast(tr,transaction);
        data = new[tr.data[0].size];

        // input data masking
        for(int i = 0; i<tr.data[0].size; i++)
        begin
          if(hgen_mask[i]==0)
            data[i]=8'h0;
          else
            data[i]= tr.data[0][i];
        end;
        
        // bjh compute
        result = bjh.hash(data);
        
        // output FrameLink frame assembly
        res = new;
        res.data = new[1];
        res.frameParts = 1;
        res.data[0] = new[tr.data[0].size + flow_id_width/8];
        for(int i=0; i < tr.data[0].size; i++)
          res.data[0][i+flow_id_width/8] = tr.data[0][i];
        for(int i = 4; i < flow_id_width/8; i++)
          res.data[0][i] =  '0;
        res.data[0][11] = result[95:88];
        res.data[0][10] = result[87:80];
        res.data[0][9] = result[79:72];
        res.data[0][8] = result[71:64];
        res.data[0][7] = result[63:56];
        res.data[0][6] = result[55:48];
        res.data[0][5] = result[47:40];
        res.data[0][4] = result[39:32];
        res.data[0][3] = result[31:24];
        res.data[0][2] = result[23:16];
        res.data[0][1] = result[15:8];
        res.data[0][0] = result[7:0];
        sc_table.add(res);

        ++cnt;

        if (cnt % 4000 == 0)
        begin
          $write("generated %d scoreboard transactions at ", cnt);
          $system("date");
          #10ns;
        end;
      endtask : post_tr
 endclass : ScoreboardInputCbs
    
 /*!
 * \brief FrameLink Output Callbacks 
 * 
 * This class is responsible removing transaction from transaction table.
 *    
 * \param pChannels - count of channels
 * \param behav - TransactionTable behavior                
 */
  
 class ScoreboardOutputCbs extends OutputCbs;
      
   /*
    * Public Class Atributes
    */
    
    //! Scoreboard identification
    string inst;
    //! Transaction Table
    TransactionTable #(0) sc_table;
      
   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates callback object 
    *      
    * \param sc_table - transaction tables
    * \param inst - scoreboard identification     
    */
    function new (TransactionTable #(0) sc_table);
      this.sc_table = sc_table;
    endfunction
   
   int cnt = 0;
   /*! 
    * Transaction postprocessing
    *
    * Function is called after transaction is received. It checks correct
    * transaction table for the same transaction. If they match, transaction is
    * removed, otherwise error is reporting.                         
    * 
    * \param transaction - transaction 
    * \param inst - monitor identifier         
    */
    virtual task post_tr(Transaction transaction, byte id);
      bit status=0;
      
      //transaction.display("REMOVED TRANSACTION FROM SCOREBOARD");
      
      // Gets number of transaction table from ID number
      sc_table.remove(transaction, status);
            
      ++cnt;
      if (cnt % 1000 == 0) begin
        $write("Removed %d transactions from scoreboard at ", cnt);
        $system("date");
      end

      if (status==0)begin
         $write("STATUS==0\n");
         $write("Unknown transaction received from monitor %d\n", inst);
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         transaction.display(); 
         sc_table.display("scoreboard");
         $stop;
      end;
    endtask : post_tr 
 endclass : ScoreboardOutputCbs   
 
 /*!
 * \brief HGEN Scoreboard
 * 
 * This class is responsible for creating Tranaction table and monitor and 
 * driver callback classes. It also prints Transaction table.   
 *    
 * \param pChannels - count of channels
 * \param behav - TransactionTable behavior                
 */
  
 class HGENScoreboard;
   /*
    * Public Class Atributes
    */
    //! Transaction Table
    TransactionTable #(0) scoreTable;
    //! Input callback
    ScoreboardInputCbs    inputCbs;
    //! Output callback
    ScoreboardOutputCbs   outputCbs;
    //! Monitor callback
    InputCbs              mi32DriverCbs;
    
   /*! 
    * Constructor
    * It creates monitor and driver callbacks and Transaction Table for each 
    * flow.
    * 
    * \param inst - scoreboard identification
    */
    function new (int flow_id_width, bit[31:0] hgen_init, bit[63:0] hgen_mask);
      this.scoreTable    = new; 
      this.inputCbs      = new(scoreTable,flow_id_width, hgen_init, hgen_mask);
      this.outputCbs     = new(scoreTable);
      this.mi32DriverCbs = new;
    endfunction

   /*!
    * Display
    *     
    * Prints Transaction Table
    * 
    */
    task display();
      scoreTable.display();
    endtask
 endclass : HGENScoreboard
