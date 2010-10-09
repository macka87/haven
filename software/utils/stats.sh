# vim: textwidth=0
do_start(){
  csbus 00081000 1
}

do_stop(){
  csbus 00081000 20
}

do_reset(){
  csbus 00081000 2
}

do_show(){

  # sample
  csbus 00081000 8

  echo ""
  echo "Application core stats:"
  echo "Control register:            " $(csbus 00081000)
  echo "Clock cycles:                " $(csbus 0008100C) $(csbus 00081008)
  echo ""
  echo "Input interface:             " "SRC_RDY_N: " $(csbus 00081054) $(csbus 00081050) "   DST_RDY_N: " $(csbus 00081064) $(csbus 00081060) "   both: " $(csbus 00081074) $(csbus 00081070)
  echo "Output interface:            " "SRC_RDY_N: " $(csbus 00081094) $(csbus 00081090) "   DST_RDY_N: " $(csbus 000810A4) $(csbus 000810A0) "   both: " $(csbus 000810B4) $(csbus 000810B0)
  echo ""
}


case $1 in
  start)
    do_start
  ;;
  stop)
    do_stop
  ;;
  reset)
    do_reset
  ;;
  show)
    do_show
  ;;
  *)
    echo "Usage: $0 (start|stop|reset|show)"
  ;;
esac
