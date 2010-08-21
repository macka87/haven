# Author: Jan Koøenek <korenek@liberouter.org>
# $Id$
# comboctl.conf

ctlvar fpga
ctlvar fpga.ident       offset 0x0000

ctlvar fpga.ident.id0   offset 0x00
ctlvar fpga.ident.id1   offset 0x04
ctlvar fpga.ident.id2   offset 0x08
ctlvar fpga.ident.id3   offset 0x0c
ctlvar fpga.ident.id4   offset 0x10
ctlvar fpga.ident.id5   offset 0x14
ctlvar fpga.ident.id6   offset 0x18
ctlvar fpga.ident.id7   offset 0x1c


ctlvar fpga.uh_fifo1   offset 0x0200
ctlvar fpga.uh_fifo2   offset 0x0A00
ctlvar fpga.uh_fifo3   offset 0x1200
ctlvar fpga.uh_fifo4   offset 0x1A00
ctlvar fpga.lup_res    offset 0x8000

proc in_bytestream_read { space offset } {
        return [ combo_space_read $space $offset ]
}

proc in_bytestream_write { space offset val } {
        combo_space_write $space $offset $val
        return
}

