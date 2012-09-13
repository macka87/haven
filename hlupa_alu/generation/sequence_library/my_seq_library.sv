//xbeles00
//balicek my_seq_library - odvodenie tried pre moje sekvencie tranzakcii

//vyuzivame z toho napriklad makra pre registraciu
`include "ovm_macros.svh"

package my_seq_library;
  
  import ovm_pkg::*;
  import my_pkg::*;

  //trieda pre sekvenciu tranzakcii
  //parametrizovana - z akeho typu tranzakcii sa sekvencia bude skladat
  class my_sequence extends ovm_sequence #(my_transaction);

    //registracia triedy
    `ovm_object_utils(my_sequence)

    //konstruktor
    function new (string name = "");
      super.new(name);
    endfunction: new

    //task body je iba len v sekvenciach
    //popis spravania sekvencii
    task body;
      //neustaly prud tranzakcii pokym neskonci simulacia
      forever
      begin
        my_transaction tx;
        //instanciacia objektu tranzakcia
        //factory metoda - tj. v teste mozeme modifikovat typ tranzakcie
        tx = my_transaction::type_id::create("tx");
        //vyvola masineriu ktora bude komunikovat s driverom, ktory tranzakciu
        //preberie
        start_item(tx);
        assert( tx.randomize() );
        //tx.display();
        finish_item(tx);
      end
    endtask: body

  endclass: my_sequence
  
endpackage