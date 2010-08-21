#
# README.txt : Verification Enviroment Usage 
#
# $Id: README.txt 5510 2008-09-05 18:33:59Z kajan $
#

=============================
Verification Enviroment Usage
=============================

Postup pri verifikacii lubovolnej komponenty s Frame Link rozhranim:

Podstatou je zmena parametrov v jednotlivych suboroch porstredia template
na oznacenych riadkoch. Zmena, ktoru treba vykonat, je strucne popisana nad
kazdym z uvedenych riadkov zmien v komentari. Doporucenia sa tykaju najma
zmeny kodu v pripade doplnenia viac interfacov, driverov alebo monitorov.

1. template/top_level.fdo
   zmena riadkov:   35,39

2. template/signals_sig.fdo
   zmena riadkov:   42

3. template/tbench/dut.sv
   doporucenia:     42,52
   zmena riadkov:   53

4. template/tbench/test.sv  
   doporucenia:     44,57,58,114,119,139,149

5. template/tbench/testbench.sv 
   doporucenia:     46,47  

6. template/tbench/test_pkg.sv
   zmena riadkov:   vsetkych podla potreby zmeny jednotlivych parametrov                 

7. template/tbench/scoreboard.sv
   doporucenia:	    63
   Umoznuje zmodifikovat transakciu pred jej odoslanim, napriklad nastavenie konkretneho
   bajtu na konkretnu hodnotu. Zmena sa prevedie nastavenim prislusneho bajtu v dvojrozmernom
   poli tr.data[packet_no][byte_no], kde prvy index urcuje poradie paketu v ramci framu
   a druhy poradie bajtu v pakete. Dlzku pola je mozne zistit metodou .size, napr. 
   tr.data.size alebo tr.data[i].size.
   Pre pristup k jednotlivym bitom je mozme pouzit treti index: tr.data[packet_no][byte_no][bit_offset]