# Author: Jan Koøenek <korenek@liberouter.org>
# $Id$


proc test_mem {base size} {
   set err 0;

   for {set i 0} {$i < $size } {incr i 1} {
        combo_space_write $base [expr $i * 4 ] [expr $i * 0x10000 + $i ]
   }

   for {set i 0} {$i < $size } {incr i 1} {
       set data [combo_space_read $base [expr $i * 4] ];
       if { $data != [expr $i * 0x10000 + $i ]  } {
             puts [to_hex $i ]
             puts " Source = $i; Dest = $data"
             puts "Error: $i row don't read (Readed = $data, Written = $i).";
             set err 1;
       }
   }
   return $err;
}

   puts "---- BlockRAM (1) preparation ---"
   test_mem fpga.uh_fifo1 512
   puts "---- BlockRAM (1) test done ---"

   puts "---- BlockRAM (2) preparation ---"
   test_mem fpga.uh_fifo2 512
   puts "---- BlockRAM (2) test done ---"

   puts "---- BlockRAM (3) preparation ---"
   test_mem fpga.uh_fifo3 512
   puts "---- BlockRAM (3) test done ---"

   puts "---- BlockRAM (4) preparation ---"
   test_mem fpga.uh_fifo4 512
   puts "---- BlockRAM (4) test done ---"

   puts "---- Lookup results RAMS preparation ---"
   test_mem fpga.lup_res 1024
   puts "---- Lookup results RAMS done ---"





