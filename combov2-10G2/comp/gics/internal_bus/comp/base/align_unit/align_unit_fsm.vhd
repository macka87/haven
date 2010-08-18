-- align_unit_fsm.vhd: Output FSM for controling control signals.
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
-- 1. Redistributions of source code must retain the above copyright
--    notice, this list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright
--    notice, this list of conditions and the following disclaimer in
--    the documentation and/or other materials provided with the
--    distribution.
-- 3. Neither the name of the Company nor the names of its contributors
--    may be used to endorse or promote products derived from this
--    software without specific prior written permission.
--
-- This software is provided ``as is'', and any express or implied
-- warranties, including, but not limited to, the implied warranties of
-- merchantability and fitness for a particular purpose are disclaimed.
-- In no event shall the company or contributors be liable for any
-- direct, indirect, incidental, special, exemplary, or consequential
-- damages (including, but not limited to, procurement of substitute
-- goods or services; loss of use, data, or profits; or business
-- interruption) however caused and on any theory of liability, whether
-- in contract, strict liability, or tort (including negligence or
-- otherwise) arising in any way out of the use of this software, even
-- if advised of the possibility of such damage.
--
-- $Id$
--
-- TODO: 
--       Delete ERR state after verifications!
--       Remove S_WAIT_EOF state

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity ALIGN_UNIT_FSM is
   port(
      -- global signals 
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input signals
      DATA_VALID     : in  std_logic_vector(1 downto 0); -- data valid    
      IN_SOF      	: in  std_logic;  				      -- input registred sof	
	   IN_EOF         : in  std_logic;					      -- input registred eof
      ENABLE         : in  std_logic;                    -- enable automata
      
      -- output control signals
      SRC_RDY        : out std_logic;   -- stop output
      DST_RDY        : out std_logic;   -- stop input 
      OUT_SOF        : out std_logic;   -- output start of frame
      OUT_EOF        : out std_logic    -- output end of frame
   );
end entity ALIGN_UNIT_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ALIGN_UNIT_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( ERR, S_START, S_SEND_SOF, S_WAIT_SOF, S_SEND_EOF, S_WAIT_EOF, S_SEND_VALID );
   
   -- ------------------ Signals declaration ----------------------------------
   signal present_state, next_state : t_state;

begin
   
   -- --------------- Sync logic -------------------------------------------
   sync_logic  : process( RESET, CLK )
   begin
      if (RESET = '1') then
         present_state <= S_START;
      elsif (CLK'event AND CLK = '1') then
         present_state <= next_state;
      end if;
   end process sync_logic;

   -- ------------------ Next state logic -------------------------------------
   next_state_logic : process( present_state, IN_SOF, IN_EOF, DATA_VALID, ENABLE )
   begin
   case (present_state) is

      -- ---------------------------------------------
	  when ERR =>								      -- test error state
	  	next_state <= ERR;

      -- ---------------------------------------------
      when S_START =>
         if (ENABLE = '1') then
            -- --------------
            if(IN_SOF = '1' and IN_EOF = '0') then
               if(DATA_VALID = "11") then    
                  next_state <= S_SEND_SOF;     -- send sof
               elsif(DATA_VALID = "01") then
                  next_state <= S_WAIT_SOF;     -- wait sof
               else
                  next_state <= ERR;            -- possible error
               end if;
            -- --------------
            elsif(IN_SOF = '1' and IN_EOF = '1') then
               next_state <= S_START;           -- send sof and eof
            -- --------------
            else
               next_state <= S_START;           -- no active signal
            -- --------------
            end if;
         else
            next_state <= S_START;              -- no allow
         end if;
            
      -- ---------------------------------------------
      when S_SEND_SOF =>
         if (ENABLE = '1') then
            -- --------------
            if(IN_EOF = '1') then
               if(DATA_VALID = "10") then
                  next_state <= S_START;        -- send eof
               elsif(DATA_VALID = "11") then
                  next_state <= S_WAIT_EOF;     -- wait eof
               else
                  next_state <= ERR;            -- possible error
                end if;
            -- --------------
            elsif(IN_EOF = '0') then
               if(DATA_VALID(1) = '1') then
                  next_state <= S_SEND_VALID;   -- send data
               else
                  next_state <= ERR;            -- possible error (not valid?)
               end if;
            -- --------------
            end if;
         else
            next_state <= S_SEND_SOF;           -- no allow
         end if;

      -- ---------------------------------------------
      when S_WAIT_SOF =>
         if (ENABLE = '1') then
            -- --------------
            if(IN_SOF = '0' and IN_EOF = '0') then
               next_state <= S_SEND_SOF;        -- send sof
            -- --------------
            elsif(IN_SOF = '0' and IN_EOF = '1') then
               if(DATA_VALID = "10") then
                  next_state <= S_START;        -- send sof and eof
               elsif(DATA_VALID = "11") then
                  next_state <= S_WAIT_EOF;     -- send sof, wait eof
               else
                  next_state <= ERR;            -- possible error 
               end if;
            -- --------------
            else
               next_state <= ERR;               -- possibe error
            end if;
            -- --------------
         else
            next_state <= S_WAIT_SOF;           -- no allow
         end if;

      -- ---------------------------------------------
      when S_SEND_EOF =>
         if (ENABLE = '1') then
            -- --------------
            if(IN_SOF = '0' and IN_EOF = '0') then
               next_state <= S_START;           -- end, go to start
            -- --------------
            elsif(IN_SOF = '1' and IN_EOF = '0') then
               if(DATA_VALID = "11") then    
                  next_state <= S_SEND_SOF;     -- send sof
               elsif(DATA_VALID = "01") then
                  next_state <= S_WAIT_SOF;     -- wait sof
               else
                  next_state <= ERR;            -- possible error
               end if;
            -- --------------
            elsif(IN_SOF = '1' and IN_EOF = '1') then
               next_state <= S_START;           -- send sof and eof
            -- --------------
            else
               next_state <= ERR;               -- possible error
            end if;
             -- --------------
         else
            next_state <= S_SEND_EOF;           -- no allow
         end if;

      -- ---------------------------------------------
      when S_WAIT_EOF =>
         if (ENABLE = '1') then
            -- --------------
            if(IN_SOF = '0' and IN_EOF = '0') then
                next_state <= S_START;          -- send eof
            -- --------------
            else
               next_state <= ERR;               -- possible error
            end if;
            -- --------------
         else
            next_state <= S_WAIT_EOF;           -- no allow
         end if;
         
      -- ---------------------------------------------
      when S_SEND_VALID =>
         if (ENABLE = '1') then
            -- --------------
            if(IN_EOF = '1') then
               if (DATA_VALID = "11") then
                  next_state <= S_WAIT_EOF;		-- wait eof
               elsif(DATA_VALID = "10") then
				      next_state <= S_START;		   -- send eof
			      else
                  next_state <= ERR;				-- possible error
               end if;
            -- -----------------
            elsif(IN_EOF = '0') then
               if(DATA_VALID(1) = '1') then
                  next_state <= S_SEND_VALID;   -- send data
               else
                  next_state <= ERR;
               end if;
            -- -----------------
            else 
                next_state <= ERR;              -- possible error
            end if;
            -- ----------------
		   else
			   next_state <= S_SEND_VALID;		   -- send data, but wait on enable
		   end if;
      -- ---------------------------------------------

      end case;
   end process next_state_logic;

   -- ------------------ Output logic -----------------------------------------
   output_logic: process( present_state, IN_SOF, IN_EOF, DATA_VALID, ENABLE )
   begin
  
      -- FIXME
      -- ---------------------------------------------
      -- Initial values
      -- no active signals
      SRC_RDY    	  <= '0'; -- stop output
      DST_RDY       <= '0'; -- stop input 
      OUT_SOF       <= '0'; -- output start of frame
      OUT_EOF       <= '0'; -- output end of frame
      -- ---------------------------------------------
      case (present_state) is

      -- ---------------------------------------------
	  when ERR =>								      -- error state
      		SRC_RDY <= '0';
      		DST_RDY <= '0'; 
      		OUT_SOF <= '0';
      		OUT_EOF <= '0';
      -- ---------------------------------------------
      when S_START =>
         if (ENABLE = '1') then
            -- --------------
            if(IN_SOF = '1' and IN_EOF = '0') then
               if(DATA_VALID = "11") then    -- send sof
                  SRC_RDY <= '1';
                  DST_RDY <= '1';
                  OUT_SOF <= '1';
                  OUT_EOF <= '0';
               elsif(DATA_VALID = "01") then -- wait sof
                  SRC_RDY <= '0';
                  DST_RDY <= '1';
                  OUT_SOF <= '0';
                  OUT_EOF <= '0';
               else                          -- possible error 
                  SRC_RDY <= '0';
                  DST_RDY <= '0';
                  OUT_SOF <= '0';
                  OUT_EOF <= '0'; 
               end if;
            -- --------------
            elsif(IN_SOF = '1' and IN_EOF = '1') then --send sof and eof
               SRC_RDY <= '1';
               DST_RDY <= '1';
               OUT_SOF <= '1';
               OUT_EOF <= '1';
            -- --------------
            else                             -- no active signal
               SRC_RDY <= '0';
               DST_RDY <= '1';
               OUT_SOF <= '0';
               OUT_EOF <= '0';
            end if;
            -- --------------
         else                                -- no allow
            SRC_RDY <= '0';
            DST_RDY <= '1';
            OUT_SOF <= '0';
            OUT_EOF <= '0';
         end if;
      -- ---------------------------------------------
      when S_SEND_SOF =>
         if (ENABLE = '1') then
            -- --------------
            if(IN_EOF = '1') then
               if(DATA_VALID = "10") then    -- send eof
                  SRC_RDY <= '1';
                  DST_RDY <= '1';
                  OUT_SOF <= '0';
                  OUT_EOF <= '1';
               elsif(DATA_VALID = "11") then -- wait eof
                  SRC_RDY <= '1';
                  DST_RDY <= '0';
                  OUT_SOF <= '0';
                  OUT_EOF <= '0';
               else                          -- possible error
                  SRC_RDY <= '0';
                  DST_RDY <= '1';
                  OUT_SOF <= '0';
                  OUT_EOF <= '0';
               end if;
            -- --------------
            elsif(IN_EOF = '0') then
               if(DATA_VALID(1) = '1') then  -- send data
                  SRC_RDY <= '1';
                  DST_RDY <= '1';
                  OUT_SOF <= '0';
                  OUT_EOF <= '0';
               else                          -- possible error (not valid?)
                  SRC_RDY <= '0';
                  DST_RDY <= '0';
                  OUT_SOF <= '0';
                  OUT_EOF <= '0';
               end if;
            -- --------------
            end if;
         else                                -- no allow
            SRC_RDY <= '1';
            DST_RDY <= '1';
            OUT_SOF <= '1';
            OUT_EOF <= '0';
         end if;
      -- ---------------------------------------------
      when S_WAIT_SOF =>
         if (ENABLE = '1') then
            -- --------------
            if(IN_SOF = '0' and IN_EOF = '0') then -- send sof
                  SRC_RDY <= '1';
                  DST_RDY <= '1';
                  OUT_SOF <= '1';
                  OUT_EOF <= '0';
            -- --------------
            elsif(IN_SOF = '0' and IN_EOF = '1') then 
               if(DATA_VALID = "10") then          -- send sof and eof
                  SRC_RDY <= '1';
                  DST_RDY <= '1';
                  OUT_SOF <= '1';
                  OUT_EOF <= '1';
               elsif(DATA_VALID = "11") then       -- send sof, wait eof
                  SRC_RDY <= '1';
                  DST_RDY <= '1';
                  OUT_SOF <= '1';
                  OUT_EOF <= '0';
               else                                -- possible error
                  SRC_RDY <= '0';
                  DST_RDY <= '0';
                  OUT_SOF <= '0';
                  OUT_EOF <= '0';
               end if;
            -- --------------         
            else                                   -- possible error
               SRC_RDY <= '0';
               DST_RDY <= '0';
               OUT_SOF <= '0';
               OUT_EOF <= '0';
            end if;
            -- --------------
         else                                      -- no allow
            SRC_RDY <= '0';
            DST_RDY <= '1';
            OUT_SOF <= '0';
            OUT_EOF <= '0';
         end if;
      -- ---------------------------------------------
      when S_SEND_EOF =>
         if (ENABLE = '1') then
            -- --------------
            if(IN_SOF = '0' and IN_EOF = '0') then -- end, go to start
               SRC_RDY <= '1';
               DST_RDY <= '1';
               OUT_SOF <= '0';
               OUT_EOF <= '0';
            -- --------------
            elsif(IN_SOF = '1' and IN_EOF = '0') then
               if(DATA_VALID = "11") then          -- send sof
                  SRC_RDY <= '1';
                  DST_RDY <= '1';
                  OUT_SOF <= '1';
                  OUT_EOF <= '0';
               elsif(DATA_VALID = "01") then       -- wait sof
                  SRC_RDY <= '0';
                  DST_RDY <= '1';
                  OUT_SOF <= '0';
                  OUT_EOF <= '0';
               else                                -- possible error
                  SRC_RDY <= '0';
                  DST_RDY <= '0';
                  OUT_SOF <= '0';
                  OUT_EOF <= '0';
               end if;
            -- --------------
            elsif(IN_SOF = '1' and IN_EOF = '1') then -- send sof and eof
               SRC_RDY <= '1';
               DST_RDY <= '1';
               OUT_SOF <= '1';
               OUT_EOF <= '1';
            -- --------------
            else                                      -- possible error
               SRC_RDY <= '0';
               DST_RDY <= '1';
               OUT_SOF <= '0';
               OUT_EOF <= '0';
            end if;   
            -- --------------
         else                                         -- no allow
            SRC_RDY <= '1';
            DST_RDY <= '1';
            OUT_SOF <= '0';
            OUT_EOF <= '1';
         end if;
      -- ---------------------------------------------
      when S_WAIT_EOF =>
         if (ENABLE = '1') then
            -- --------------
            if(IN_SOF = '0' and IN_EOF = '0') then -- send eof
               SRC_RDY <= '1';
               DST_RDY <= '1';
               OUT_SOF <= '0';
               OUT_EOF <= '1';
            -- --------------
            else                                   -- possible error
               SRC_RDY <= '0';
               DST_RDY <= '0';
               OUT_SOF <= '0';
               OUT_EOF <= '0';
            end if;
            -- --------------
         else                                       -- no allow
            SRC_RDY <= '1';
            DST_RDY <= '0';
            OUT_SOF <= '0';
            OUT_EOF <= '0';
         end if;
      -- ---------------------------------------------
      when S_SEND_VALID =>
         if (ENABLE = '1') then
            -- --------------
            if(IN_EOF = '1') then
               if (DATA_VALID = "11") then		-- wait eof
			   	   SRC_RDY <= '1';
      	   		DST_RDY <= '0'; 
      	   		OUT_SOF <= '0';
      	   		OUT_EOF <= '0';
               elsif(DATA_VALID = "10") then	   -- send eof
			   	   SRC_RDY <= '1';
      	   		DST_RDY <= '1'; 
      	   		OUT_SOF <= '0';
      	   		OUT_EOF <= '1';
			      else								      -- possible error
			         SRC_RDY <= '0';
      	   	   DST_RDY <= '0'; 
      	   	   OUT_SOF <= '0';
      	   	   OUT_EOF <= '0';
               end if;
            -- --------------
            elsif(IN_EOF = '0') then			
               if(DATA_VALID(1) = '1') then     -- send data
		 	         SRC_RDY <= '1';
      	   	   DST_RDY <= '1'; 
      	   	   OUT_SOF <= '0';
      	   	   OUT_EOF <= '0';
               -- ---------------
		         else									   -- possible error
			         SRC_RDY <= '0';
      	         DST_RDY <= '0'; 
      	         OUT_SOF <= '0';
      	         OUT_EOF <= '0';
		         end if;
            -- --------------
        end if;
         else
            SRC_RDY <= '1';
            DST_RDY <= '1';
            OUT_SOF <= '0';
            OUT_EOF <= '0';
         end if;
      -- ---------------------------------------------

      end case;
   end process output_logic;

end architecture full;


