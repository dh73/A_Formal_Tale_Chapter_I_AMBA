/*  AXI4 Formal Properties.
 *  Copyright (C) 2021  Diego Hernandez <diego@yosyshq.com>
 *                                      <dhdezr@fpgaparadox.com>
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */
`default_nettype none
module amba_axi4_write_response_channel
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter unsigned     ID_WIDTH        = AMBA_AXI4_ID_WIDTH,
     parameter unsigned     BUSER_WIDTH     = AMBA_AXI4_BUSER_WIDTH,
     parameter axi4_agent_t AGENT_TYPE      = SOURCE,
     parameter axi4_types_t PROTOCOL_TYPE   = AXI4LITE,
     parameter bit          ENABLE_COVER    = 1,
     parameter bit          ENABLE_DEADLOCK = 1,
     parameter unsigned     MAXWAIT         = 16)
   (input wire                   ACLK,
    input wire 			 ARESETn,
    input wire [ID_WIDTH-1:0] 	 BID,
    input wire [1:0] 		 BRESP,
    input wire [BUSER_WIDTH-1:0] BUSER,
    input wire 			 BVALID,
    input wire 			 BREADY);

   // Import the properties in this scope
   import definition_of_axi4_lite::*;
   import amba_axi4_single_interface_requirements::*;

   // Default clocking for all properties
   default clocking axi4_aclk @(posedge ACLK); endclocking
   logic first_point;
   always_ff @(posedge ACLK) begin
      if (!ARESETn) first_point <= 1'b1;
      else          first_point <= 1'b0;
   end

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section B1.1: Definition of AXI4-Lite                *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   generate
      if (PROTOCOL_TYPE == AXI4LITE) begin: axi4lite_defs
	 // Now configure unsupported AXI4-Lite signals
	 logic B_unsupported_sig;
	 assign B_unsupported_sig = (/* Optional User-defined signal in the write address channel.
				      * Supported only in AXI4. */
				     BUSER   == {BUSER_WIDTH{1'b0}} &&
				     /* AXI4-Lite does not support AXI IDs. This means
	                              * all transactions must be in order, and all
	                              * accesses use a single fixed ID value. */
	                             BID     == {ID_WIDTH{1'b0}});
	 
	 // Configure the AXI4-Lite checker unsupported signals.
	 cp_B_unsupported_axi4l: assume property(disable iff (!ARESETn) axi4_lite_unsupported_sig(B_unsupported_sig))
	   else $error("Violation: For B in AXI4-Lite, only signals described in B1.1 are",
		       "required or supported (B1.1 Definition of AXI4-Lite, pB1-126).");
	 
	 if (AGENT_TYPE == DESTINATION || AGENT_TYPE == MONITOR) begin: a_exclusive_responses
	    ap_B_UNSUPPORTED_RESPONSE: assert property(disable iff (!ARESETn) unsupported_transfer_status(BVALID, BRESP, EXOKAY))
	      else $error("Violation: The EXOKAY response is not supported on the read data",
			  "and write response channels (B1.1.1 Signal List, pB1-126).");
	 end
	 else if (AGENT_TYPE == SOURCE || AGENT_TYPE == CONSTRAINT) begin: c_exclusive_responses
	    cp_B_UNSUPPORTED_RESPONSE: assume property(disable iff (!ARESETn) unsupported_transfer_status(BVALID, BRESP, EXOKAY))
	      else $error("Violation: The EXOKAY response is not supported on the read data",
			  "and write response channels (B1.1.1 Signal List, pB1-126).");
	 end
      end
   endgenerate

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Chapter A3. Single Interface Requirements            *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   generate
      if (AGENT_TYPE == SOURCE || AGENT_TYPE == MONITOR) begin: source_properties
	 // Section A3.1.2: Reset
	 ap_B_SRC_DST_EXIT_RESET: assert property (exit_from_reset(ARESETn, first_point, BVALID))
	   else $error ("Violation: BVALID must be low for the first clock edge",
			"after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 // Section A3.2.1: Handshake process
	 ap_B_SRC_DST_STABLE_BRESP: assert property (disable iff (!ARESETn) stable_before_handshake(BVALID, BREADY, BRESP))
	   else $error ("Violation: Once the master has asserted BVALID, data and control information",
			"from master must remain stable [BRESP] until BREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 ap_B_SRC_DST_BVALID_until_BREADY: assert property (disable iff (!ARESETn) valid_before_handshake(BVALID, BREADY))
	   else $error ("Violation: Once BVALID is asserted it must remain asserted until the handshake",
			"occurs (A3.2.1 Handshake process, pA3-39).");
      end
      else if (AGENT_TYPE == DESTINATION || AGENT_TYPE == CONSTRAINT) begin: destination_properties
	 // Section A3.1.2: Reset
	 cp_B_DST_SRC_EXIT_RESET:   assume property (exit_from_reset(ARESETn, first_point, BVALID))
	   else $error ("Violation: BVALID must be low for the first clock edge",
			"after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 // Section A3.2.1: Handshake process
	 cp_B_DST_SRC_STABLE_BRESP: assume property (disable iff (!ARESETn) stable_before_handshake(BVALID, BREADY, BRESP))
	   else $error ("Violation: Once the master has asserted BVALID, data and control information",
			"from master must remain stable [BRESP] until BREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 cp_B_DST_SRC_BVALID_until_BREADY: assume property (disable iff (!ARESETn) valid_before_handshake(BVALID, BREADY))
	   else $error ("Violation: Once BVALID is asserted it must remain asserted until the handshake",
			"occurs (A3.2.1 Handshake process, pA3-39).");
      end // block: destination_properties
   endgenerate

   // AMBA Recommended property for potential deadlock detection
   generate
      if (ENABLE_DEADLOCK)
	if (AGENT_TYPE == DESTINATION || AGENT_TYPE == MONITOR) begin: deadlock_check
	   ap_B_DST_SRC_READY_MAXWAIT: assert property (disable iff (!ARESETn) handshake_max_wait(BVALID, BREADY, MAXWAIT))
	     else $error ("Violation: BREADY should be asserted within MAXWAIT cycles of BVALID being asserted (AMBA Recommended).");
	end
	else if (AGENT_TYPE == SOURCE || AGENT_TYPE == CONSTRAINT) begin: deadlock_cons
	   cp_B_SRC_DST_READY_MAXWAIT: assume property (disable iff (!ARESETn) handshake_max_wait(BVALID, BREADY, MAXWAIT))
	     else $error ("Violation: BREADY should be asserted within MAXWAIT cycles of BVALID being asserted (AMBA Recommended).");
	end
   endgenerate

   // Witnessing scenarios stated in the AMBA AXI4 spec
   generate
      if (ENABLE_COVER) begin: witness
	 wp_BVALID_before_BREADY: cover property (disable iff (!ARESETn) valid_before_ready(BVALID, BREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-2 VALID before READY handshake capability.");
	 wp_BREADY_before_BVALID: cover property (disable iff (!ARESETn) ready_before_valid(BVALID, BREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-3 READY before VALID handshake capability.");
	 wp_BVALID_with_BREADY: cover property (disable iff (!ARESETn) valid_with_ready(BVALID, BREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-4 VALID with READY handshake capability.");

	 if (PROTOCOL_TYPE != AXI4LITE) begin: exok_resp
	    wp_WRITE_RESP_EXOKAY: cover property (disable iff (!ARESETn) rdwr_response_exokay(BVALID, BREADY, BRESP))
	      $info("Witnessed: EXOKAY, exclusive access success, A3-58 with Table A3-4.");
	 end
	 wp_WRITE_RESP_OKAY: cover property (disable iff (!ARESETn) rdwr_response_okay(BVALID, BREADY, BRESP))
	   $info("Witnessed: OKAY, normal access success, A3-57 with Table A3-4.");
	 wp_WRITE_RESP_SLVERR: cover property (disable iff (!ARESETn) rdwr_response_slverr(BVALID, BREADY, BRESP))
	   $info("Witnessed: SLVERR, slave error, A3-57 with Table A3-4.");
	 wp_WRITE_RESP_DECERR: cover property (disable iff (!ARESETn) rdwr_response_decerr(BVALID, BREADY, BRESP))
	   $info("Witnessed: DECERR, decode error, A3-57 with Table A3-4.");
      end
   endgenerate
endmodule // amba_axi4_write_response_channel
`default_nettype wire
