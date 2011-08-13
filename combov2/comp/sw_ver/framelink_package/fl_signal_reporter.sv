/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    FrameLink Signal Reporter Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         11.8.2011 
 * ************************************************************************** */
 
class FrameLinkSignalReporter extends SignalReporter;

 /*! 
  * Constructor 
  */    
  function new(string inst,
               byte id,
               tTransMbx mbx
               ); 
    super.new(inst, id, mbx);
  endfunction: new

  virtual function void writeReport(ref NetCOPETransaction ntr, integer fId);
    ntr.display("FrameLink REPORTER:");
    $fwrite(fId, "Ahoj\n");
  endfunction
endclass
