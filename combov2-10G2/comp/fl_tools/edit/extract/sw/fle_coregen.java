/* 
 * fle_coregen.java: Core generator for FL_EXTRACT
 * Copyright (C) 2007 CESNET
 * Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
 * $Id: fle_coregen.java 80 2007-08-06 18:02:22Z xkosar02 $
 *
 */

import java.io.*;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.ParserConfigurationException;
import org.w3c.dom.*;
import org.xml.sax.*;

public class fle_coregen
{
  public static void printRegister(String inputSignal,int inTop,int inBottom, String outputSignal, int outTop, int outBottom, String WE, String resetValue)
  {
    System.out.println("");
    System.out.println("process (clk, reset)");
    System.out.println("  begin");
    System.out.println("   if reset='1' then   --asynchronous reset active High");
    System.out.println("      "+outputSignal+"("+outTop+" downto "+outBottom+") <= "+resetValue+";");
    System.out.println("   elsif (clk'event and clk='1' and "+WE+"='1') then  -- clk rising edge");
    System.out.println("      "+outputSignal+"("+outTop+" downto "+outBottom+") <= "+inputSignal+"("+inTop+" downto "+inBottom+");");
    System.out.println("   end if;");
    System.out.println("end process;");
    System.out.println("");
  }

  public static void printRegister(String inputSignal, String outputSignal, String resetValue)
  {
    System.out.println("");
    System.out.println("process (clk, reset)");
    System.out.println("  begin");
    System.out.println("   if reset='1' then   --asynchronous reset active High");
    System.out.println("      "+outputSignal+" <= "+resetValue+";");
    System.out.println("   elsif (clk'event and clk='1') then  -- clk rising edge");
    System.out.println("      "+outputSignal+" <= "+inputSignal+";");
    System.out.println("   end if;");
    System.out.println("end process;");
    System.out.println("");
  } 

  public static void printHeader()
  {
    System.out.println("-- fl_extract_full.vhd: Full architecture of FrameLink Extract component");
    System.out.println("-- Copyright (C) 2007 CESNET");
    System.out.println("-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>");
    System.out.println("--");
    System.out.println("-- Redistribution and use in source and binary forms, with or without");
    System.out.println("-- modification, are permitted provided that the following conditions");
    System.out.println("-- are met:");
    System.out.println("-- 1. Redistributions of source code must retain the above copyright");
    System.out.println("--    notice, this list of conditions and the following disclaimer.");
    System.out.println("-- 2. Redistributions in binary form must reproduce the above copyright");
    System.out.println("--    notice, this list of conditions and the following disclaimer in");
    System.out.println("--    the documentation and/or other materials provided with the");
    System.out.println("--    distribution.");
    System.out.println("-- 3. Neither the name of the Company nor the names of its contributors");
    System.out.println("--    may be used to endorse or promote products derived from this");
    System.out.println("--    software without specific prior written permission.");
    System.out.println("--");
    System.out.println("-- This software is provided ``as is'', and any express or implied");
    System.out.println("-- warranties, including, but not limited to, the implied warranties of");
    System.out.println("-- merchantability and fitness for a particular purpose are disclaimed.");
    System.out.println("-- In no event shall the company or contributors be liable for any");
    System.out.println("-- direct, indirect, incidental, special, exemplary, or consequential");
    System.out.println("-- damages (including, but not limited to, procurement of substitute");
    System.out.println("-- goods or services; loss of use, data, or profits; or business");
    System.out.println("-- interruption) however caused and on any theory of liability, whether");
    System.out.println("-- in contract, strict liability, or tort (including negligence or");
    System.out.println("-- otherwise) arising in any way out of the use of this software, even");
    System.out.println("-- if advised of the possibility of such damage.");
    System.out.println("--");
    System.out.println("--");
  }

  public static void printDecoder(int DW, int PW)
  {
    System.out.println("");
    System.out.println("decoder: entity work.FL_EXTRACT_DECODER");
    System.out.println("  generic map(");
    System.out.println("   DECODER_WIDTH=> "+DW+",");
    System.out.println("   POSITION_WIDTH=> "+PW+"");
    System.out.println("  )");
    System.out.println("  port map(");
    System.out.println("   CLK=>CLK,");
    System.out.println("   RESET=>RESET,");
    System.out.println("   SRC_RDY_N=>RX_SRC_RDY_N,");
    System.out.println("   DST_RDY_N=>TX_DST_RDY_N,");
    System.out.println("   EOP_N=>RX_EOP_N,");
    System.out.println("   EOF_N=>RX_EOF_N,");
    System.out.println("   HEAD_EN=>HEAD_EN,");
    System.out.println("   POSITION=>POSITION");
    System.out.println("  );");
    System.out.println("");
  }

  public static void printControlBlock(String target, int part, int position, int PW)
  {
     System.out.println("");
     System.out.println(target+"<=not RX_SRC_RDY_N and not TX_DST_RDY_N and HEAD_EN("+part+") when POSITION=conv_std_logic_vector("+position+" / reduced_data_width,"+PW+") else '0';");
     System.out.println("");
  }
  
  public static void printInterface(int dataWidth,int[] size,String[] port)
  {
     System.out.println("library IEEE;");
     System.out.println("use IEEE.std_logic_1164.all;");
     System.out.println("use IEEE.std_logic_unsigned.all;");
     System.out.println("use IEEE.std_logic_arith.all;");
     System.out.println("");
     System.out.println("-- Math package - log2 function");
     System.out.println("use work.math_pack.all;");
     System.out.println("");
     System.out.println("-- ----------------------------------------------------------------------------");
     System.out.println("--                        Entity declaration");
     System.out.println("-- ----------------------------------------------------------------------------");
     System.out.println("entity FL_EXTRACT is");
     System.out.println("   port(");
     System.out.println("      CLK          : in std_logic;");
     System.out.println("      RESET        : in std_logic;");
     System.out.println("");
     for (int i=0;i<port.length;i++)
     {
       System.out.println("      "+port[i]+"  : out std_logic_vector("+(size[i]*8-1)+" downto 0);");
       System.out.println("      "+port[i]+"_VLD  : out std_logic;");
     }
     System.out.println("      -- Input Interface");
     System.out.println("      RX_DATA      : in  std_logic_vector("+(dataWidth-1)+" downto 0);");
     if (dataWidth != 8) 
        System.out.println("      RX_REM       : in  std_logic_vector(log2("+dataWidth+"/8) - 1 downto 0);");
     System.out.println("      RX_SRC_RDY_N : in  std_logic;");
     System.out.println("      RX_DST_RDY_N : out std_logic;");
     System.out.println("      RX_SOP_N     : in  std_logic;");
     System.out.println("      RX_EOP_N     : in  std_logic;");
     System.out.println("      RX_SOF_N     : in  std_logic;");
     System.out.println("      RX_EOF_N     : in  std_logic;");
     System.out.println("");
     System.out.println("      -- Output Interface");
     System.out.println("      TX_DATA      : out std_logic_vector("+(dataWidth-1)+" downto 0);");
     if (dataWidth != 8) 
       System.out.println("      TX_REM       : out std_logic_vector(log2("+dataWidth+"/8)-1 downto 0);");
     System.out.println("      TX_SRC_RDY_N : out std_logic;");
     System.out.println("      TX_DST_RDY_N : in  std_logic;");
     System.out.println("      TX_SOP_N     : out std_logic;");
     System.out.println("      TX_EOP_N     : out std_logic;");
     System.out.println("      TX_SOF_N     : out std_logic;");
     System.out.println("      TX_EOF_N     : out std_logic");
     System.out.println("   );");
     System.out.println("end entity FL_EXTRACT;");
     System.out.println("");
     System.out.println("architecture full of FL_EXTRACT is");
     System.out.println("");
  }
  public static void printLastPart(String outSignal,int outTop,int outBottom,int inTop, int inBottom)
  { 
    System.out.println(outSignal+"( "+outTop+" downto " +outBottom+") <= RX_DATA("+inTop+" downto "+inBottom+");");
    
  }
  public static void printSignals(int DW, int PW, String[] port, int[] size, int[] offset, int width)
  {
     System.out.println("");
     System.out.println("signal HEAD_EN   : std_logic_vector(2**"+DW+"-1 downto 0);");
     System.out.println("signal POSITION  : std_logic_vector( "+(PW-1)+" downto 0);");
     int reducedDataWidth = width / 8;
     for (int i=0;i<port.length;i++)
     {
       int numberOfFulReg = (size[i] - (reducedDataWidth - offset[i] % reducedDataWidth)) / reducedDataWidth;
       System.out.println("signal "+port[i]+"_WE : std_logic_vector( "+numberOfFulReg+" downto 0 );");
     }
     System.out.println("");
     System.out.println("constant reduced_data_width : integer := "+reducedDataWidth+";");
     System.out.println("");
     System.out.println("begin");
     System.out.println("");
  }
  public static void showHelp()
  {
    System.err.println("FL_EXTRACT core generator:");
    System.err.println("This program generates VHDL code from XML description. For detail information see unit documentation. VHDL code will be written on STDOUT.");
    System.err.println("");
    System.err.println("Usage:");
    System.err.println("java fle_coregen --help");
    System.err.println("java fle_coregen XML_file_name");
    System.err.println(" --help        -> Show this help.");
    System.err.println(" XML_file_name -> Input XML file.");

  }
  public static void main(String[] args) throws Throwable
  {
    if (args.length!=1)
      {
        System.err.println("Error: Expecting file name.");
        showHelp();
        System.exit(1);
      }
    if (args[0].equals("--help"))
      {
        showHelp();
        System.exit(0);
      }
    // XML document parsing
    DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
    dbf.setValidating(true);
    try{
      DocumentBuilder builder = dbf.newDocumentBuilder();
      builder.setErrorHandler(
        new org.xml.sax.ErrorHandler() 
          {
            // Fatal error are thrown automatic
            public void fatalError(SAXParseException exception) throws SAXException
              {
              }
            // Validation error
            public void error(SAXParseException e) throws SAXParseException
              {
                throw e;
              }
            // Warning
            public void warning(SAXParseException err) throws SAXParseException
              {
                System.err.println("Warning: " + err.getMessage());
                throw err;
              }
          }
      );
      Document doc = builder.parse(args[0]);
      NodeList nl = doc.getElementsByTagName("fl_extract");
      Element myNode = (Element)nl.item(0);
      String flw = myNode.getAttribute("fl_width");
      int width = Integer.parseInt(flw);
      boolean pipeline = Boolean.parseBoolean(myNode.getAttribute("fl_pipeline"));
      //boolean transformer = Boolean.parseBoolean(myNode.getAttribute("fl_transformer"));
      int DW = Integer.parseInt(myNode.getAttribute("packet_counter_width"));
      int PW = Integer.parseInt(myNode.getAttribute("part_counter_width"));
      nl = doc.getElementsByTagName("fields");
      int n = nl.getLength();
      NodeList pom = doc.getElementsByTagName("field");
      int[] packetArray = new int[pom.getLength()];
      int[] offsetArray = new int[pom.getLength()];
      int[] sizeArray = new int[pom.getLength()];
      String[] portArray = new String[pom.getLength()];
      int position=0;
      for (int i=0;i<n;i++)
      {
        Element node = (Element)nl.item(i);
        NodeList inl = node.getChildNodes();
        int m = inl.getLength();
        for (int j=0; j<m; j++)
        {
          String s=inl.item(j).getNodeName();
          if (s.equals("field"))
            {
              Element node2 = (Element)inl.item(j);
              int packet_no = Integer.parseInt(node2.getAttribute("packet_no"));
              int offset = Integer.parseInt(node2.getAttribute("offset"));
              int size = Integer.parseInt(node2.getAttribute("size"));
              StringBuffer port = new StringBuffer();
              NodeList inl1 = node2.getChildNodes();
              int mm = inl1.getLength();
              for (int jj=0; jj<mm; jj++)
              {
                if (inl1.item(jj).getNodeType() == Node.TEXT_NODE)
                  port.append(inl1.item(jj).getNodeValue());
              }
              String portName = port.toString();
              for (int k=0;k<position;k++)
                {
                  if (portName.equals(portArray[k]))
                   {
                     System.err.println("Error: Two names of port are same.");
                     System.exit(1);
                   }
                }
              packetArray[position]= packet_no;
              offsetArray[position]= offset;
              sizeArray[position]= size;
              portArray[position]= portName;
              position+=1;
            }
        }
      }
      // VHDL file generating
      printHeader();
      printInterface(width,sizeArray,portArray);
      printSignals(DW, PW, portArray, sizeArray, offsetArray, width);
      if (pipeline==true) 
      {
        printRegister("RX_DATA","TX_DATA","(others=>'0')");
        if (width != 8)
          printRegister("RX_REM","TX_REM","(others=>'0')");
        printRegister("RX_SOF_N","TX_SOF_N","'1'");
        printRegister("RX_EOF_N","TX_EOF_N","'1'");
        printRegister("RX_SOP_N","TX_SOP_N","'1'");
        printRegister("RX_EOF_N","TX_EOF_N","'1'");
        printRegister("RX_SRC_RDY_N","TX_SRC_RDY_N","'1'");
        printRegister("TX_DST_RDY_N","RX_DST_RDY_N","'1'");
      }
      else
      {
        System.out.println("TX_DATA<=RX_DATA;");
        if (width != 8) 
          System.out.println("TX_REM<=RX_REM;");
        System.out.println("TX_SOF_N<=RX_SOF_N;");
        System.out.println("TX_EOF_N<=RX_EOF_N;");
        System.out.println("TX_SOP_N<=RX_SOP_N;");
        System.out.println("TX_EOP_N<=RX_EOP_N;");
        System.out.println("TX_SRC_RDY_N<=RX_SRC_RDY_N;");
        System.out.println("RX_DST_RDY_N<=TX_DST_RDY_N;");
        System.out.println("");
      }
      printDecoder(DW,PW);
      for (int i=0;i<portArray.length;i++)
      {
        if (offsetArray[i]%(width/8)+sizeArray[i]<=width/8)
         {
           printControlBlock(portArray[i]+"_VLD", packetArray[i], offsetArray[i],PW);
           printLastPart(portArray[i],sizeArray[i]*8-1,0,(offsetArray[i]%(width/8))*8+sizeArray[i]*8-1,(offsetArray[i]%(width/8))*8);
         }
        else
         {
           int reducedDataWidth = width / 8;
           int firstRegTop = (reducedDataWidth - offsetArray[i] % reducedDataWidth) * 8 - 1;
           int firstRegDataTop = width - 1;
           int firstRegDataBottom = (offsetArray[i] % reducedDataWidth) * 8;
           int inRegOut = (reducedDataWidth - offsetArray[i] % reducedDataWidth) * 8;
           int lastTop = sizeArray[i] * 8 - 1;
           int lastBottom = (sizeArray[i] - (reducedDataWidth - offsetArray[i] % reducedDataWidth)) / reducedDataWidth * width + (reducedDataWidth - offsetArray[i] % reducedDataWidth) * 8;
           int lastDataTop = ((sizeArray[i] - (reducedDataWidth - offsetArray[i] % reducedDataWidth)) % reducedDataWidth) * 8 - 1;
           int numberOfFulReg = (sizeArray[i] - (reducedDataWidth - offsetArray[i] % reducedDataWidth)) / reducedDataWidth;
           int remOfFulReg = (sizeArray[i]-(reducedDataWidth - offsetArray[i] % reducedDataWidth)) % reducedDataWidth;
           if (remOfFulReg==0)
            {
              numberOfFulReg-=1;
              lastBottom=lastTop-width+1;
              lastDataTop=width-1;
            }
           printRegister("RX_DATA",firstRegDataTop,firstRegDataBottom,portArray[i], firstRegTop, 0, portArray[i]+"_WE(0)", "(others => '0')");
           printControlBlock(portArray[i]+"_WE(0)", packetArray[i],  offsetArray[i],PW);
           for (int j=1;j<=numberOfFulReg;j++)
            {
              printRegister("RX_DATA",width-1, 0,portArray[i], j * width + inRegOut - 1, (j - 1) * width + inRegOut, portArray[i]+"_WE("+j+")", "(others => '0')");
              printControlBlock(portArray[i]+"_WE("+j+")", packetArray[i],  offsetArray[i]+j*reducedDataWidth,PW);
            }
           printControlBlock(portArray[i]+"_VLD", packetArray[i], offsetArray[i]+(numberOfFulReg+1)*reducedDataWidth, PW);
           printLastPart(portArray[i],lastTop,lastBottom,lastDataTop,0);
         }
      }

    System.out.println("end architecture full;"); 
  }
    catch (SAXException sxe) {
       // Parse error
       sxe.printStackTrace();

    } catch (IOException ioe) {
       // Error during I/O operation
       ioe.printStackTrace();
    }
  }
}
