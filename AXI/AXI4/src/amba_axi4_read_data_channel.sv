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
  #(parameter unsigned     DATA_WIDTH      = 32,
    parameter axi4_agent_t AGENT_TYPE      = SOURCE,
    parameter axi4_types_t PROTOCOL_TYPE   = AXI4LITE,
    parameter bit          ENABLE_COVER    = 1,
    parameter bit          ENABLE_DEADLOCK = 1,
    parameter unsigned     MAXWAIT         = 16)
   (input wire                  ACLK,
    input wire 			ARESETn,
    input wire 			RVALID,
    input wire 			RREADY,
    input wire [DATA_WIDTH-1:0] RDATA,
    input wire [1:0] 		RRESP);

   // Import the properties in this scope
   import amba_axi4_single_interface_requirements::*;
   // Default clocking for all properties
   default clocking axi4_aclk @(posedge ACLK); endclocking
   logic first_point;
   always_ff @(posedge ACLK) begin
      if (!ARESETn) first_point <= 1'b1;
      else          first_point <= 1'b0;
   end

   generate
      if (AGENT_TYPE == SOURCE || AGENT_TYPE == MONITOR) begin: source_properties
	 // Section A3.1.2: Reset
	 ap_R_SRC_DST_EXIT_RESET: assert property (exit_from_reset(ARESETn, first_point, RVALID))
	   else $error ("Violation: WVALID must be low for the first clock edge",
			"after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 // Section A3.2.1: Handshake process
	 ap_R_SRC_DST_STABLE_RRESP: assert property (disable iff (!ARESETn) stable_before_handshake(RVALID, RREADY, RRESP))
	   else $error ("Violation: Once the master has asserted RVALID, data and control information",
			"from master must remain stable [RRESP] until RREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 ap_R_SRC_DST_STABLE_RDATA: assert property (disable iff (!ARESETn) stable_before_handshake(RVALID, RREADY, RDATA)) // TODO: Need to take ARSIZE into account as well.
	   else $error ("Violation: Once the master has asserted RWVALID, data and control information",
			"from master must remain stable [RDATA] until RREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 ap_R_SRC_DST_RVALID_until_RREADY: assert property (disable iff (!ARESETn) valid_before_handshake(RVALID, RREADY))
	   else $error ("Violation: Once RVALID is asserted it must remain asserted until the handshake",
			"occurs  (A3.2.1 Handshake process, pA3-39).");
      end // block: source_properties

      else if (AGENT_TYPE == DESTINATION || AGENT_TYPE == CONSTRAINT) begin: destination_properties
	 // Section A3.1.2: Reset
	 cp_R_DST_SRC_EXIT_RESET: assume property (exit_from_reset(ARESETn, first_point, RVALID))
	   else $error ("Violation: WVALID must be low for the first clock edge",
			"after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 // Section A3.2.1: Handshake process
	 cp_R_DST_SRC_STABLE_RRESP: assume property (disable iff (!ARESETn) stable_before_handshake(RVALID, RREADY, RRESP))
	   else $error ("Violation: Once the master has asserted RVALID, data and control information",
			"from master must remain stable [RRESP] until RREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 cp_R_DST_SRC_STABLE_RDATA: assume property (disable iff (!ARESETn) stable_before_handshake(RVALID, RREADY, RDATA)) // TODO: Need to take ARSIZE into account as well.
	   else $error ("Violation: Once the master has asserted RWVALID, data and control information",
			"from master must remain stable [RDATA] until RREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 cp_R_DST_SRC_RVALID_until_RREADY: assume property (disable iff (!ARESETn) valid_before_handshake(RVALID, RREADY))
	   else $error ("Violation: Once RVALID is asserted it must remain asserted until the handshake",
			"occurs  (A3.2.1 Handshake process, pA3-39).");
      end // block: destination_properties
   endgenerate

   // Witnessing scenarios stated in the AMBA AXI4 spec
   generate
      if (ENABLE_COVER) begin: witness
	 wp_RVALID_before_RREADY: cover property (disable iff (!ARESETn) valid_before_ready(RVALID, RREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-2 VALID before READY handshake capability.");
	 wp_RREADY_before_RVALID: cover property (disable iff (!ARESETn) ready_before_valid(RVALID, RREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-3 READY before VALID handshake capability.");
	 wp_RVALID_with_RREADY: cover property (disable iff (!ARESETn) valid_with_ready(RVALID, RREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-4 VALID with READY handshake capability.");
      end
   endgenerate

   // AMBA Recommended property for potential deadlock detection
   generate
      if (ENABLE_DEADLOCK)
	if (AGENT_TYPE == DESTINATION || AGENT_TYPE == MONITOR) begin: deadlock_check
	   ap_R_DST_SRC_READY_MAXWAIT: assert property (disable iff (!ARESETn) handshake_max_wait(RVALID, RREADY, MAXWAIT)) // TODO: hmm, analyse this again.
	     else $error ("Violation: RREADY should be asserted within MAXWAIT cycles of RVALID being asserted (AMBA recommended).");
	end
	else if (AGENT_TYPE == SOURCE || AGENT_TYPE == CONSTRAINT) begin: deadlock_cons
	   cp_R_DST_SRC_READY_MAXWAIT: assume property (disable iff (!ARESETn) handshake_max_wait(RVALID, RREADY, MAXWAIT))
	     else $error ("Violation: AWREADY should be asserted within MAXWAIT cycles of AWVALID being asserted (AMBA recommended).");
	end
   endgenerate
endmodule // amba_axi4_read_data_channel
`default_nettype wire
