/*!
 * \file ddm_ring_modul.sv
   \brief  Descriptor Download Manager Ring Modul
 * \date Copyright (C) 2009 CESNET
 * \author Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 * 3. Neither the name of the Company nor the names of its contributors
 *    may be used to endorse or promote products derived from this
 *    software without specific prior written permission.
 *
 * This software is provided ``as is'', and any express or implied
 * warranties, including, but not limited to, the implied warranties of
 * merchantability and fitness for a particular purpose are disclaimed.
 * In no event shall the company or contributors be liable for any
 * direct, indirect, incidental, special, exemplary, or consequential
 * damages (including, but not limited to, procurement of substitute
 * goods or services; loss of use, data, or profits; or business
 * interruption) however caused and on any theory of liability, whether
 * in contract, strict liability, or tort (including negligence or
 * otherwise) arising in any way out of the use of this software, even
 * if advised of the possibility of such damage.
 *
 * $Id: ddm_ring_modul.sv 10920 2009-08-31 09:24:33Z xspinl00 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  /*!
   * \brief DDM Ring Modul Class
   *
   * This class simulates RX and TX ring. It contains functions, that operate
   * with ring and initial functions.  
   *
   * \param pFlows - count of flows
   * \param pRingParts - parts in ring for each flow
   * \param pRingPartSize - part size   
   */
  // --------------------------------------------------------------------------
  class DdmRingModul #(int pFlows = 4, int pRingPartSize = 512, int pRingParts =
  3);
    
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string    inst;                             //! Driver identification
    bit       enabled;                          //! Driver is enabled
    byte      ring[];                           //! Simulated Ring 
    int       ringSize;                         //! Size of the Ring
    int       actDescPos[];                     //! Actual descdriptor position for each flow 
    int       descSize;                         //! Descriptor Size

    DdmSoftwareModul sw;                        //! DDM Software Modul
    
    // -------------------
    // -- Class Methods --
    // -------------------

    // ------------------------------------------------------------------------
    //! Constructor
    /*
     * Create ring modul object
     */
    function new (string inst,
                  DdmSoftwareModul sw
                 );
      this.enabled     = 0;                     //! Driver is disabled by default
      this.inst        = inst;                  //! Store driver identifier
      this.sw          = sw;                    //! DDM Software Modul

      //! descriptor size is 16 B 
      descSize = 16; 

      //! ring size = 2(RX and TX) * flows count * each flow parts * part size
      // * descriptor size 
      ringSize = 2*pFlows*pRingParts*pRingPartSize*descSize; 
      ring = new[ringSize];

      //! free address space in ring where new descriptor can be stored (for each flow)
      actDescPos = new[pFlows*2]; 

      //! ring initialization    
      for(int i=0; i<ringSize; i++)
        ring[i]=0;

      //! descriptor position initialization
      for(int j=0; j<pFlows*2; j++)
        actDescPos[j] = pRingPartSize*descSize*j;
    endfunction: new          
    
    // ---------------------------
    // -- Private Class Methods --
    // ---------------------------
   
    // -----------------------------------------------------------------------
    //! DDM Modul Initialization
    /*!
     * 1. Tail register is zeroised.
     * 2. Control register - RUN.
     */ 
    task initDdm();
      int tailHwAddr;               //! Tail Pointers addresses
      int controlAddr;              //! Control addresses
      int controlRegAddr= 32'h00;   //! Control register address
      int tailRegAddr   = 32'h0C;   //! Tail Register Address
      int partFlows     = 32'h40;   //! This constant makes from Register Address
                                    //  Reqister Addresses for flows

      for (int i=0; i<pFlows*2; i++)begin
        //! Tail Pointers Initialization
        tailHwAddr = tailRegAddr + partFlows*i;  
        sw.writeMI32(tailHwAddr, 0);
      end
      
      for (int i=0; i<pFlows*2; i++)begin
        //! Control register Initialization - RUN
        controlAddr = controlRegAddr +partFlows*i;
        sw.writeMI32(controlAddr, 2);   
      end  

      //! Descriptors type One are set in Rings      
      setDescriptorsTypeOne();        
    endtask : initDdm

    // --------------------------------------------------------------------------
    //! Run DDM
    /*
     * Control Register - RUN.
     */
    task runDdm(int flow, int rxtx);
      int controlAddr;              //! Control addresses
      int controlRegAddr= 32'h00;   //! Control register address
      int partFlows     = 32'h40;   //! This constant makes from Register Address
                                    //  Reqister Addresses for flows
      //! Control register - Pause
      controlAddr = controlRegAddr +partFlows*(2*flow+rxtx);
              
      //! Control Register is set via MI32
      sw.swQueue.push_back(controlAddr);
      sw.swQueue.push_back(2);
    endtask : runDdm

    // --------------------------------------------------------------------------
    //! Pause DDM
    /*
     * Control Register - PAUSE.
     */
    task pauseDdm(int flow, int rxtx);
      int controlAddr;              //! Control addresses
      int controlRegAddr= 32'h00;   //! Control register address
      int partFlows     = 32'h40;   //! This constant makes from Register Address
                                    //  Reqister Addresses for flows
      //! Control register - Pause
      controlAddr = controlRegAddr +partFlows*(2*flow+rxtx);
           
      //! Control Register is set via MI32
      sw.swQueue.push_back(controlAddr);
      sw.swQueue.push_back(1);
    endtask : pauseDdm

    // --------------------------------------------------------------------------
    //! Stop DDM
    /*
     * Control Register - STOP.
     */
    task stopDdm(int flow, int rxtx);
      int controlAddr;              //! Control addresses
      int controlRegAddr= 32'h00;   //! Control register address
      int partFlows     = 32'h40;   //! This constant makes from Register Address
                                    //  Reqister Addresses for flows
      //! Control register - Stop
      controlAddr = controlRegAddr +partFlows*(2*flow+rxtx);
             
      //! Control Register is set via MI32
      sw.swQueue.push_back(controlAddr);
      sw.swQueue.push_back(0);

      initTail(flow,rxtx);
    endtask : stopDdm

    // --------------------------------------------------------------------------
    //! Init TailPointer Register
    /*
     * Set TailPointer register to 0.
     */
    task initTail(int flow, int rxtx);
      int tailHwAddr;               //! Tail Pointers addresses
      int tailRegAddr   = 32'h0C;   //! Tail Register Address
      int partFlows     = 32'h40;   //! This constant makes from Register Address
                                    //  Reqister Addresses for flows

      //! Tail Pointer Initialization
      tailHwAddr = tailRegAddr + partFlows*(2*flow+rxtx);  
      
      //! Tail Pointer Register is set via MI32
      sw.swQueue.push_back(tailHwAddr);
      sw.swQueue.push_back(0);
    endtask : initTail

    // --------------------------------------------------------------------------
    //! Set Descriptors Type One
    /*!
     * Store Descriptors Type One to TX and RX ring
     */
    task setDescriptorsTypeOne();
      logic[127:0]  desc;
      int base_addr[];                 //! lower bound of flows space
      int bound_addr[];                //! upper bound of flows space
      int desc_addr = pRingPartSize*descSize-descSize;   //! first position of descriptor type one in ring
      int onePartSize = pRingPartSize*descSize*pFlows*2; //! size of one part size * pFlows 
                         
      base_addr  = new[pFlows*2]; 
      bound_addr = new[pFlows*2];

      //! initialization values of base_addr and bound_addr
      for(int k=0; k<pFlows*2; k++)begin
        base_addr[k]=pRingPartSize*descSize*k;
        bound_addr[k]=onePartSize*pRingParts+base_addr[k];
      end 
            
      //! descriptor is created and stored to ring 
      for (int j=0;j<pRingParts;j++)begin
        for(int i=0; i<pFlows*2; i++)begin
          desc[31:0]   = 0;
          desc[63:32]  = 6;
          desc[127:64] = onePartSize+base_addr[i]+j*onePartSize;

          if (desc[127:64]==bound_addr[i])
            desc[127:64] = base_addr[i];
         
          for (int r=0; r<descSize; r++) begin
            for (int k=0; k<8; k++)
              ring[desc_addr][k] = desc[8*r+k]; 
            desc_addr++;  
          end   
          desc_addr+=pRingPartSize*descSize-descSize;  
        end  
      end 
    endtask : setDescriptorsTypeOne

    // ---------------------------------------------------------------------------
    //! Store to Descriptor to Ring
    /*
     * Store descriptor type Zero to TX or RX Ring
     * 
     * \param transaction - DDM transaction (descriptor)
     * \param flow - rx or tx actual flow
     * \param rxtx - rx or tx ring is used to store descriptor
     */
    task storeToRing(input DdmTransaction transaction, int rxtx);
        logic[127:0] descTypeOne;
        int newAddr; 

        //! interface number
        int flow = transaction.block_addr;
        //$write("STORETORING: actdescpos:  %d\n",actDescPos[2*flow+rxtx]);

        //! Descriptor is stored to free position in address space
        for (int i=0; i<descSize; i++)begin
          for (int k=0; k<8; k++)
            ring[actDescPos[2*flow+rxtx]][k] = transaction.data[8*i+k];
          actDescPos[2*flow+rxtx]++;
        end    
        
        //! If actual position is occupied by descriptor type one,
        //  read this descriptor and update actual position according descriptor's value
        if ((actDescPos[2*flow+rxtx]+descSize)%(pRingPartSize*descSize)==0) begin
          for(int i=0; i<descSize; i++)begin
            for(int k=0; k<8; k++)
              descTypeOne[8*i+k] = ring[actDescPos[2*flow+rxtx]][k];
            actDescPos[2*flow+rxtx]++;  
          end  
          actDescPos[2*flow+rxtx] = descTypeOne[127:64];
        end  
    endtask : storeToRing

    // ---------------------------------------------------------------------------
    //! Get descriptor from Ring
    /*
     * Get descriptors from RX or TX Ring
     *
     * \param transaction - descriptor from ring
     * \param addr - global address in ring
     */
    task getFromRing(output byte dataPart, input int addr);
       dataPart = ring[addr];  
    endtask : getFromRing 

  endclass : DdmRingModul

