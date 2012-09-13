//xbeles00
//balicek my_test_library - odvodenie tried pre moje testy

`include "ovm_macros.svh"

package my_test_library;

  //obecne kniznice a makra
  import ovm_pkg::*;
  `include "ovm_macros.svh"

  //moje kniznice
  import my_pkg::*;
  import my_seq_library::*;
  
  
  
  
  //odvodenie tiriedy my_test pre nase konkretne testovacie prostredie
  class my_test extends ovm_test;
    
    //registracia prostredia
    `ovm_component_utils(my_test)

    //reference na instanciu verifikacneho prostredia
    //testovacie prostredie zabaluje verifikacne prostredie
    my_env my_env_h;

    //konstruktor
    function new(string name, ovm_component parent);
      super.new(name, parent);
    endfunction: new

    function void build;
      super.build();
      //instanciacia verifikacneho prostredia, parametre: meno, rodic
      my_env_h = my_env::type_id::create("my_env_h", this);
    endfunction: build
    
    task run;
      my_sequence seq;
      seq = my_sequence::type_id::create("seq");
      seq.start( my_env_h.my_agent_h.my_sequencer_h);
    endtask: run
  
  endclass: my_test




endpackage: my_test_library