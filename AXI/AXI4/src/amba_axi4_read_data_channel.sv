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
module amba_axi4_read_data_channel
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter axi4_checker_params_t cfg =
     '{ID_WIDTH:         4,
       DATA_WIDTH:       32,
       RUSER_WIDTH:      32,
       AGENT_TYPE:       SOURCE,
       PROTOCOL_TYPE:    AXI4LITE,
       CHECK_PARAMETERS: 1,
       ENABLE_COVER:     1,
       ARM_RECOMMENDED:  1,
       MAXWAIT:          16,
       OPTIONAL_RESET:   1,
       default:          0})
   (input wire                       ACLK,
    input wire 			     ARESETn,
    input wire [cfg.ID_WIDTH-1:0]    RID,
    input wire [cfg.DATA_WIDTH-1:0]  RDATA,
    input wire [1:0] 		     RRESP,
    input wire 			     RLAST,
    input wire [cfg.RUSER_WIDTH-1:0] RUSER,
    input wire 			     RVALID,
    input wire 			     RREADY);

   // Import the properties in this scope
   import amba_axi4_definition_of_axi4_lite::*;
   import amba_axi4_single_interface_requirements::*;

   // Default clocking for all properties
   default clocking axi4_aclk @(posedge ACLK); endclocking

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section B1.1: Definition of AXI4-Lite                *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4LITE) begin: axi4lite_defs
	 if(cfg.CHECK_PARAMETERS == 1) begin: check_dataw
	    ap_R_AXI4LITE_DATAWIDTH: assert property(axi4l_databus_width(cfg.DATA_WIDTH))
	      else $error("Violation: AXI4-Lite supports a data bus width of 32-bit or 64-bit",
			  "(B.1 Definition of AXI4-Lite, pB1-126).");
	 end

	 // Now configure unsupported AXI4-Lite signals
	 logic R_unsupported_sig;
	 assign R_unsupported_sig = (/* All bursts are defined to be of length 1,
				      * equivalent to a WLAST or RLAST value of 1. */
				     RLAST == 1'b1 &&
				     /* Optional User-defined signal in the write address channel.
				      * Supported only in AXI4. */
				     RUSER == {cfg.RUSER_WIDTH{1'b0}} &&
				     /* AXI4-Lite does not support AXI IDs. This means
	                              * all transactions must be in order, and all
	                              * accesses use a single fixed ID value. */
				     RID == {cfg.ID_WIDTH{1'b0}});

         // Configure the AXI4-Lite checker unsupported signals.
	 cp_R_unsupported_axi4l: assume property(disable iff (!ARESETn) axi4_lite_unsupported_sig(R_unsupported_sig))
	   else $error("Violation: For R in AXI4-Lite, only signals described in B1.1 are",
		       "required or supported (B1.1 Definition of AXI4-Lite, pB1-126).");

	 if(cfg.AGENT_TYPE == DESTINATION || cfg.AGENT_TYPE == MONITOR) begin: a_exclusive_responses
	    ap_R_UNSUPPORTED_RESPONSE: assert property(disable iff (!ARESETn) unsupported_transfer_status(RVALID, RRESP, EXOKAY))
	      else $error("Violation: The EXOKAY response is not supported on the read data",
			  "and write response channels (B1.1.1 Signal List, pB1-126).");
	 end
	 else if(cfg.AGENT_TYPE == SOURCE || cfg.AGENT_TYPE == CONSTRAINT) begin: c_exclusive_responses
	    cp_R_UNSUPPORTED_RESPONSE: assume property(disable iff (!ARESETn) unsupported_transfer_status(RVALID, RRESP, EXOKAY))
	      else $error("Violation: The EXOKAY response is not supported on the read data",
			  "and write response channels (B1.1.1 Signal List, pB1-126).");
	 end
      end
   endgenerate

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Chapter A3. Single Interface Requirements            *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   generate
      if(cfg.AGENT_TYPE == SOURCE || cfg.AGENT_TYPE == MONITOR) begin: source_properties
	 // Section A3.1.2: Reset
	 if(cfg.OPTIONAL_RESET == 1) begin: optional_reset
	    ap_R_SRC_DST_EXIT_RESET: assert property(exit_from_reset(ARESETn, RVALID))
	      else $error("Violation: WVALID must be low for the first clock edge",
			  "after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 end

	 // Section A3.2.1: Handshake process
	 ap_R_SRC_DST_STABLE_RRESP: assert property(disable iff (!ARESETn) stable_before_handshake(RVALID, RREADY, RRESP))
	   else $error("Violation: Once the master has asserted RVALID, data and control information",
		       "from master must remain stable [RRESP] until RREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 ap_R_SRC_DST_STABLE_RDATA: assert property(disable iff (!ARESETn) stable_before_handshake(RVALID, RREADY, RDATA)) // TODO: Need to take ARSIZE into account as well.
	   else $error("Violation: Once the master has asserted RWVALID, data and control information",
		       "from master must remain stable [RDATA] until RREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 ap_R_SRC_DST_RVALID_until_RREADY: assert property(disable iff (!ARESETn) valid_before_handshake(RVALID, RREADY))
	   else $error("Violation: Once RVALID is asserted it must remain asserted until the handshake",
		       "occurs  (A3.2.1 Handshake process, pA3-39).");
      end // block: source_properties

      else if(cfg.AGENT_TYPE == DESTINATION || cfg.AGENT_TYPE == CONSTRAINT) begin: destination_properties
	 // Section A3.1.2: Reset
	 if(cfg.OPTIONAL_RESET == 1) begin: optional_reset
	    cp_R_DST_SRC_EXIT_RESET: assume property(exit_from_reset(ARESETn, RVALID))
	      else $error("Violation: WVALID must be low for the first clock edge",
			  "after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 end

	 // Section A3.2.1: Handshake process
	 cp_R_DST_SRC_STABLE_RRESP: assume property(disable iff (!ARESETn) stable_before_handshake(RVALID, RREADY, RRESP))
	   else $error("Violation: Once the master has asserted RVALID, data and control information",
		       "from master must remain stable [RRESP] until RREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 cp_R_DST_SRC_STABLE_RDATA: assume property(disable iff (!ARESETn) stable_before_handshake(RVALID, RREADY, RDATA)) // TODO: Need to take ARSIZE into account as well.
	   else $error("Violation: Once the master has asserted RWVALID, data and control information",
		       "from master must remain stable [RDATA] until RREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 cp_R_DST_SRC_RVALID_until_RREADY: assume property(disable iff (!ARESETn) valid_before_handshake(RVALID, RREADY))
	   else $error("Violation: Once RVALID is asserted it must remain asserted until the handshake",
		       "occurs  (A3.2.1 Handshake process, pA3-39).");
      end // block: destination_properties
   endgenerate

   // AMBA Recommended property for potential deadlock detection
   generate
      if(cfg.ARM_RECOMMENDED)
	if(cfg.AGENT_TYPE == DESTINATION || cfg.AGENT_TYPE == MONITOR) begin: deadlock_check
	   ap_R_DST_SRC_READY_MAXWAIT: assert property(disable iff (!ARESETn) handshake_max_wait(RVALID, RREADY, cfg.MAXWAIT)) // TODO: hmm, analyse this again.
	     else $error("Violation: RREADY should be asserted within MAXWAIT cycles of RVALID being asserted (AMBA recommended).");
	end
	else if(cfg.AGENT_TYPE == SOURCE || cfg.AGENT_TYPE == CONSTRAINT) begin: deadlock_cons
	   cp_R_DST_SRC_READY_MAXWAIT: assume property(disable iff (!ARESETn) handshake_max_wait(RVALID, RREADY, cfg.MAXWAIT))
	     else $error("Violation: AWREADY should be asserted within MAXWAIT cycles of AWVALID being asserted (AMBA recommended).");
	end
   endgenerate

   // Witnessing scenarios stated in the AMBA AXI4 spec
   generate
      if (cfg.ENABLE_COVER == 1) begin: witness
	 wp_RVALID_before_RREADY: cover property(disable iff (!ARESETn) valid_before_ready(RVALID, RREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-2 VALID before READY handshake capability.");
	 wp_RREADY_before_RVALID: cover property(disable iff (!ARESETn) ready_before_valid(RVALID, RREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-3 READY before VALID handshake capability.");
	 wp_RVALID_with_RREADY: cover property(disable iff (!ARESETn) valid_with_ready(RVALID, RREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-4 VALID with READY handshake capability.");

	 if (cfg.PROTOCOL_TYPE != AXI4LITE) begin: exok_resp
	    wp_READ_RESP_EXOKAY: cover property(disable iff (!ARESETn) rdwr_response_exokay(RVALID, RREADY, RRESP))
	      $info("Witnessed: EXOKAY, exclusive access success, A3-58 with Table A3-4.");
	 end
	 wp_READ_RESP_OKAY: cover property(disable iff (!ARESETn) rdwr_response_okay(RVALID, RREADY, RRESP))
	   $info("Witnessed: OKAY, normal access success, A3-57 with Table A3-4.");
	 wp_READ_RESP_SLVERR: cover property(disable iff (!ARESETn) rdwr_response_slverr(RVALID, RREADY, RRESP))
	   $info("Witnessed: SLVERR, slave error, A3-57 with Table A3-4.");
	 wp_READ_RESP_DECERR: cover property(disable iff (!ARESETn) rdwr_response_decerr(RVALID, RREADY, RRESP))
	   $info("Witnessed: DECERR, decode error, A3-57 with Table A3-4.");
      end
   endgenerate
endmodule // amba_axi4_read_data_channel
`default_nettype wire
