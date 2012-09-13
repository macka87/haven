//xbeles00
//modul top - tj. najvrchnejsia verifikacna obalka(nie top DUT)

module top;

  //include; ovm_pkg je oficialny balicek a my_pkg je moj odvodenymi triedami
  import ovm_pkg::*;
  import my_pkg::*;
  import my_seq_library::*;
  import my_test_library::*;
  import ovm_container_pkg::*;
  
  //instancovanie struktur DUT a interface
  dut_if dut_if1 ();
  dut dut1 ( ._if(dut_if1) );

  //generovanie hodin
  initial
    begin
      dut_if1.CLK = 0;
      forever begin
        #5 dut_if1.CLK = ~dut_if1.CLK;
      end
    end

  //reset na zaciatku
  initial
    begin
      dut_if1.RESET = 1;
    end
  
  initial
    begin: blk

      //vytvorenie obalu na virtual interface aby mohlo ist do konfig. tabulky
      //do konfiguracnej tabulky ho chceme aby ku nemu mohli aj ine obejkty
      dut_if_wrapper if_wrapper = new("if_wrapper", dut_if1);
      //danie obalu do konfiguracnej tabulky
      //parametre: cesta pre ktore objekty ma byt pristupny(* = pre vsetky)
      //dalsie parametre: field meno, hodnota, neklonovat
      set_config_object("*", "dut_if_wrapper", if_wrapper, 0);
      //najde class kt. bola zaregistrovana ako my_test a nainstancuje ju
      //nainstancovanie my_test vyvola instancovanie verification enviroment,
      //spustenie verificatin enviroment...
      run_test("my_test");
    end

endmodule: top