//xbeles00
//balicek my_pkg - odvodenie tried pre moje testovacie a verifikacne prostredie

//vyuzivame z toho napriklad makra pre registraciu
`include "ovm_macros.svh"

package my_pkg;
  
  //include na oficialny ovm balicek
  import ovm_pkg::*;
  
  
  
  
  //odvodenie triedy pre nasu tranzakciu
  //ovm_sequence_item mozeme na rozdiel od ovm_tranzaction savat do sekvencii
  class my_transaction extends ovm_sequence_item;

    //zaregistrovanie sekvencie
    `ovm_object_utils(my_transaction)

    //data, ktore obsahuje a budu mat nahodnu hodnotu
    rand bit RESET;
    rand int OPERACIA;
    rand int OPERAND_A;
    rand int OPERAND_B;

    //obmedzenia na nahodne generovane hodnoty vyssie uvedenych premennych
    constraint c_OPERACIA { OPERACIA >= 0; OPERACIA < 4; }
    constraint c_OPERAND_A { OPERAND_A >= 0; OPERAND_A < 16; }
    constraint c_OPERAND_B { OPERAND_B >= 0; OPERAND_B < 16; }

    //konstruktor
    function new (string name = "");
      //nema parent argumenta, lebo sekvencia nie je sucastou hierarchie
      super.new(name);
    endfunction: new

    //zobrazi obsah tranzakcie
    function void display(string prefix = "");
       if (prefix != "")
       begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
       end
       $write("RESET: %d\n", RESET);      
       $write("OPERAND_A: %d\n", OPERAND_A);  
       $write("OPERAND_B: %d\n", OPERAND_B); 
       $write("OPERACIA: %d\n", OPERACIA);
       $write("\n");
    endfunction: display

  endclass: my_transaction




  //odvodenie triedy tranzakciu s vysledom od DUT
  //ovm_sequence_item mozeme na rozdiel od ovm_tranzaction savat do sekvencii
  class my_tr_vysledok extends ovm_sequence_item;

    //zaregistrovanie sekvencie
    `ovm_object_utils(my_tr_vysledok)

    //data, ktore tranzakcia obsahuje
    int VYSLEDOK;

    //konstruktor
    function new (string name = "");
      //nema parent argumenta, lebo sekvencia nie je sucastou hierarchie
      super.new(name);
    endfunction: new

    //zobrazi obsah tranzakcie
    function void display(string prefix = "");
       if (prefix != "")
       begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
       end
       $write("VYSLEDOK: %d\n", VYSLEDOK);
    endfunction: display

  endclass: my_tr_vysledok
  
  
  
  
  //trieda odvodena pre sequencer vo vnutri agenta
  //parametrizovana trieda
  class my_sequencer extends ovm_sequencer #(my_transaction);
    
    //registracia komponenty
    `ovm_component_utils(my_sequencer)

    //konstruktor
    function new(string name, ovm_component parent);
      super.new(name, parent);
    endfunction: new

  endclass: my_sequencer
  
  
  
  
  //obal pre virtual interface aby sme ho mohli dat do konfiguracnej tabulky
  class dut_if_wrapper extends ovm_object;
    
    //premenna odkazujuca na interface
    virtual dut_if dut_if1;

    //konstruktor
    function new(string name, virtual dut_if arg);
      super.new(name);
      dut_if1 = arg;
    endfunction: new

  endclass: dut_if_wrapper

  
  
  
  //odvodenie triedy pre driver
  //funkcia: davanie tranzakcii na virtual interface
  //umiestnenie: vo vnutri agenta
  class my_driver extends ovm_driver #(my_transaction);

    //zaregistrovanie triedy
    `ovm_component_utils(my_driver)

    //port, ktorym sa budu data z virtual interface presuvat do scoreboardu
    //prenasa tranzakcie s resetom, operandami a operatorom
    ovm_analysis_port #(my_transaction) aport_zadanie;
    
    //referencia na virtual interface
    virtual dut_if dut_if1;

    //konstruktor
    function new(string name, ovm_component parent);
      super.new(name, parent);
    endfunction: new

    function void build;
      super.build();
      aport_zadanie = new("aport_zadanie", this);
      begin
        ovm_object obj;
        dut_if_wrapper if_wrapper;
        //precita objekt z konfiguracnej tabulky
        get_config_object("dut_if_wrapper", obj, 0);
        //prerobime precitany objekt na obal pre virtual interface
        assert( $cast(if_wrapper, obj) );
        //z obalu vybereme virtual interface
        dut_if1 = if_wrapper.dut_if1;
      end
    endfunction: build
    
    task run;

      //driver zkonzumuje 12 tranzakcii a poziada o zastavenie simulacie
      //pri zvyseni poctu treba zvysit aj cas na poziadanie o zastavenie
      //simulacie ovm_top.stop_request() v task run triedy my_env
      //ukazka ze sa verifikacia da zastavit z viacerych miest
      repeat(12)
      begin

        my_transaction tx;

        //$write("driver caka na CLK\n");

        //synchronizacia s DUT
        @(posedge dut_if1.CLK);
        seq_item_port.get(tx);

        tx.display("DRIVER:");

        //poslanie hodnot z tranzakcie na virtual interface
        dut_if1.RESET = tx.RESET;
        dut_if1.OPERACIA = tx.OPERACIA;
        dut_if1.OPERAND_A = tx.OPERAND_A;
        dut_if1.OPERAND_B = tx.OPERAND_B;
        
        //poslanie vygenerovanej sekvencie do scoreboardu
        aport_zadanie.write(tx);
             
      end
      //vyckaj na clock a zastav simulaciu
      @(posedge dut_if1.CLK) ovm_top.stop_request();
    endtask: run

  endclass: my_driver
  
  
  
   
  //odvodenie triedy pre monitor
  //davanie tranzakcii z virtual interface na analyticky port pre subscribera
  //umiestnenie: vo vnutri agenta  
  class my_monitor extends ovm_monitor;

    //zaregistrovanie komponenty
    `ovm_component_utils(my_monitor)

    //port, ktorym sa budu data z virtual interface presuvat do subscribera
    //a scoreboardu
    //prenasa tranzakcie s resetom, operandami a operatorom
    ovm_analysis_port #(my_transaction) aport;
    //prenasa tranzakcie s vysledkom
    ovm_analysis_port #(my_tr_vysledok) aport_vysledok;

    //referencia na virtual interface
    virtual dut_if dut_if1;
    
    //konstruktor
    function new (string name, ovm_component parent);
      super.new(name, parent);
    endfunction: new

    function void build;
      super.build();
      aport = new("aport", this);
      aport_vysledok = new("aport_vysledok", this);
      
      begin
        ovm_object obj;
        dut_if_wrapper if_wrapper;
        //precita objekt z konfiguracnej tabulky
        get_config_object("dut_if_wrapper", obj, 0);
        //prerobime precitany objekt na obal pre virtual interface
        assert( $cast(if_wrapper, obj) );
        //z obalu vybereme virtual interface
        dut_if1 = if_wrapper.dut_if1;  
      end
    endfunction: build
    
    task run;

      //aby boli ocakavany a prislusny aktualny vysledok v rovnakom case,
      //aby nenacitalo vysledok z virtual inerface, ktory este neni vysledkom
      //ale inicializacnou hodnotou
      #10;
      
      forever
      begin
        //my_transaction tx;
        my_tr_vysledok tx_vysledok;
        @(posedge dut_if1.CLK);
        //tx = my_transaction::type_id::create("tx");
        tx_vysledok = my_tr_vysledok::type_id::create("tx_vysledok");
        //tx.OPERACIA = dut_if1.OPERACIA;
        //tx.OPERAND_A = dut_if1.OPERAND_A;
        //tx.OPERAND_B = dut_if1.OPERAND_B;
        //tx.RESET = dut_if1.RESET;
        tx_vysledok.VYSLEDOK = dut_if1.VYSLEDOK;
        //tx.display("MONITOR:");
        //$write("MONITOR DOSTAL OD DUT VYSLEDOK: %d\n", dut_if1.VYSLEDOK); 
        //poslanie tranzakcie cez analyticky port
        //aport.write(tx);
        aport_vysledok.write(tx_vysledok);
      end
    endtask: run
      
  endclass: my_monitor 
  
  
  
  
  //odvodenie triedy pre agenta vo vnutri verifikacneho prostredia
  class my_agent extends ovm_agent;

    //registracia agenta
    `ovm_component_utils(my_agent)
    
    //pripojenie monitoru k agentovi
    ovm_analysis_port #(my_transaction) aport_zadanie;
    ovm_analysis_port #(my_tr_vysledok) aport_vysledok;

    //"handles" na objekty, ktore bude obsahovat
    my_sequencer my_sequencer_h;
    my_driver my_driver_h;
    my_monitor my_monitor_h;

    //konstruktor
    function new(string name, ovm_component parent);
      super.new(name, parent);
    endfunction: new

    function void build;
      super.build();
      //vytvorenie instancii detskych komponent
      //factory metody tj. dovoluju prepisat typ objektu od hocikial pocas
      //vytvarania a mozeme im prepisat aj spravanie bez prepisovania kodu
      my_sequencer_h = my_sequencer::type_id::create("my_sequencer_h", this);
      my_driver_h = my_driver ::type_id::create("my_driver_h" , this);
      my_monitor_h = my_monitor ::type_id::create("my_monitor_h" , this);
      aport_zadanie = new("aport_zadanie", this);
      aport_vysledok = new("aport_vysledok", this);
    endfunction: build

    //metoda an pospajanie detskych komponent
    //fungovalo by to aj v build v tomto pripade, ale osobitne je to lepsie
    function void connect;
      my_driver_h.seq_item_port.connect(my_sequencer_h.seq_item_export);
      my_driver_h.aport_zadanie.connect(aport_zadanie);
      my_monitor_h.aport_vysledok.connect(aport_vysledok);
    endfunction: connect
  
  endclass: my_agent




  //trieda pre subscribera vo vnutri verifikacneho prostredia
  //funkcia subscriberov je na overovanie funkcionalneho coverage
  class my_subscriber extends ovm_subscriber#(my_transaction);
  
    //zaregistrovanie
    `ovm_component_utils(my_subscriber)

    //vstupne signaly pre DUT
    bit RESET;
    int OPERACIA;
    int OPERAND_A;
    int OPERAND_B;

    covergroup cover_bus;
      //RESET: coverpoint RESET;
      //OPERACIA: coverpoint OPERACIA { bins o[4] = {0,1,2,3}; }
      //OPERAND_A: coverpoint OPERAND_A { bins a[2] = {[0:9],[10:15]}; }
      //OPERAND_B: coverpoint OPERAND_B { bins b[2] = {[0:9],[10:15]}; }
      //basic: cross RESET,OPERACIA,OPERAND_A,OPERAND_B;
      RESET: coverpoint RESET { bins not_reset = {0}; bins reset = {1};}
      OPERACIA: coverpoint OPERACIA { bins scitanie = {0}; bins minimum = {1}; bins posuv = {2}; bins neplatne ={3}; }
      OPERAND_A: coverpoint OPERAND_A { bins A_ok = {[0:9]}; bins A_fail = {[10:15]}; }
      OPERAND_B: coverpoint OPERAND_B { bins B_ok = {[0:9]}; bins B_fail = {[10:15]}; }
      CROSS: cross RESET,OPERACIA,OPERAND_A,OPERAND_B;
      option.per_instance = 1;
    endgroup: cover_bus
    
    //konstruktor
    function new(string name, ovm_component parent);
      super.new(name, parent);
      cover_bus = new();
    endfunction: new

    function void build;
      super.build();
    endfunction: build

    //ako argument tranzakcia predana cez analyticky port
    //povinna funkcia
    function void write(my_transaction t);
      RESET = t.RESET;
      OPERACIA = t.OPERACIA;
      OPERAND_A = t.OPERAND_A;
      OPERAND_B = t.OPERAND_B;
      cover_bus.sample();
    endfunction: write
    
  endclass: my_subscriber

  
               
  
  //scoreboard - overovanie spravnosti vysledkov
  class my_scoreboard extends ovm_scoreboard;
  
    `ovm_component_utils(my_scoreboard)
    
    //pre pripojenie na driver a monitor
    ovm_analysis_export #(my_transaction) driver_export;
    ovm_analysis_export #(my_tr_vysledok) monitor_export;
    
    //fronty prijatych tranzakcii
    local tlm_analysis_fifo #(my_transaction) driver_fifo;
    local tlm_analysis_fifo #(my_tr_vysledok) monitor_fifo;

    //konstruktor
    function new(string name, ovm_component parent);
      super.new(name, parent);
    endfunction: new
    
    function void build();
      driver_export = new("driver_export",this);
      monitor_export = new("monitor_export",this);
      driver_fifo = new("driver_fifo",this);
      monitor_fifo = new("monitor_fifo",this);
    endfunction: build
    
    virtual function void connect();
      driver_export.connect(driver_fifo.analysis_export);
      monitor_export.connect(monitor_fifo.analysis_export);
    endfunction: connect
    
    virtual task run();
      my_transaction driver_transaction;
      my_tr_vysledok monitor_transaction;
      int ocakavany_vysledok;
      string msg;
            
      forever begin
        
        //ziskanie tranzakcii
        driver_fifo.get(driver_transaction);
        monitor_fifo.get(monitor_transaction);
        
        //pomocne vypisy, co obsahuju prijate tranzakcie
        //driver transaction je o jedno posunuta, aby sme nedostavali expected
        //transaction skor, nez treba
        //driver_transaction.display("SCOREBOARD:");
        monitor_transaction.display("SCOREBOARD:");
        
        //vypocet ocakavaneho vysledku
        if (driver_transaction.RESET == 1) ocakavany_vysledok = 0;
        else
          begin
            priority case(driver_transaction.OPERACIA)
              0:begin
                  if (((driver_transaction.OPERAND_A > 9)||(driver_transaction.OPERAND_A < 0))||((driver_transaction.OPERAND_B > 9)||(driver_transaction.OPERAND_B < 0))) ocakavany_vysledok=31;
                  else ocakavany_vysledok = driver_transaction.OPERAND_A + driver_transaction.OPERAND_B; 
                end
              1:begin
                  if (((driver_transaction.OPERAND_A > 9)||(driver_transaction.OPERAND_A < 0))||((driver_transaction.OPERAND_B > 9)||(driver_transaction.OPERAND_B < 0))) ocakavany_vysledok=31;
                  else
                    begin
                      if (driver_transaction.OPERAND_A < driver_transaction.OPERAND_B) ocakavany_vysledok = driver_transaction.OPERAND_A;
                      else ocakavany_vysledok = driver_transaction.OPERAND_B; 
                    end
                end
              2:begin
                  if ((driver_transaction.OPERAND_A > 9)||(driver_transaction.OPERAND_A < 0)) ocakavany_vysledok = 31;
                  else ocakavany_vysledok = driver_transaction.OPERAND_A >> 1;
                end
              default:ocakavany_vysledok = 31;
            endcase;
          end
        
        //pomocne vypisy
        $write("OCAKAVANY VYSLEDOK: %d\n", ocakavany_vysledok);
        if (ocakavany_vysledok == monitor_transaction.VYSLEDOK) ovm_report_info("SCOREBOARD", "vysledok je v poriadku");
        else begin
            $sformat(msg, "ZLY VYSLEDOK! \n aktualny vysledok: %d, ocakavany vysledok: %d \n operacia: %d, operand_a: %d, operand_b: %d, reset: %d.\n", monitor_transaction.VYSLEDOK , ocakavany_vysledok , driver_transaction.OPERACIA , driver_transaction.OPERAND_A , driver_transaction.OPERAND_B , driver_transaction.RESET);
            ovm_report_error("SCOREBOARD", msg,OVM_LOW);
          end
        $write("______________________________\n");
      
      end
    endtask: run    
    
  endclass: my_scoreboard
  
  
  
  
  //odvodenie tiriedy my_env pre nase konkretne verifikacne prostredie
  class my_env extends ovm_env;
  
    //registracia prostredia
    `ovm_component_utils(my_env)
    
    //"handles" na objekty, ktore bude obsahovat
    my_agent my_agent_h;
    my_subscriber my_subscriber_h;
    my_scoreboard my_scoreboard_h;

    //konstruktor
    function new(string name, ovm_component parent);
      super.new(name, parent);
    endfunction: new

    function void build;
      super.build();
      my_agent_h = my_agent ::type_id::create("my_agent_h" , this);
      my_subscriber_h = my_subscriber::type_id::create("my_subscriber_h" , this);
      my_scoreboard_h = my_scoreboard::type_id::create("my_scoreboard_h", this); 
    endfunction: build
    
    function void connect;
      //subscriber by mal byt z nejakych divnych dvovodov podla verification
      //academy napichnuty na monitor a nie driver
      my_agent_h.aport_zadanie.connect(my_subscriber_h.analysis_export);
      my_agent_h.aport_zadanie.connect(my_scoreboard_h.driver_export);
      my_agent_h.aport_vysledok.connect(my_scoreboard_h.monitor_export);
    endfunction: connect

    //testovanie testovaneho zariadenia, beh verifikacneho prostredia
    task run;
      
      //aby boli ocakavany a prislusny aktualny vysledok v rovnakom case,
      //vlozime uvodnu tranzakciu
      //naplname to tu, aby nedosla aj do subscribera a covergroup
      my_transaction tx;
      tx = my_transaction::type_id::create("tx");
      tx.OPERACIA = 0;
      tx.OPERAND_A = 0;
      tx.OPERAND_B = 0;
      tx.RESET = 0;
      my_scoreboard_h.driver_export.write(tx);
      
      //stop nie na moj najvyssi modul v hierarchii systemVer. ale najvyssi
      //objekt v objektovo zalozeneom verifikacnom prostredi
      //po 50 casovych jednotkach zastav simulaciu
      //aktualne simulaciu zastavuje driver
      #200 ovm_top.stop_request();
    endtask: run
  
  endclass: my_env
  
  
  
  
endpackage: my_pkg