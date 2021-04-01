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
module amba_axi4_write_data_channel
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter unsigned     DATA_WIDTH      = 32,
     parameter axi4_agent_t AGENT_TYPE      = SOURCE,
     parameter axi4_types_t PROTOCOL_TYPE   = AXI4LITE,
     parameter bit          CHECK_PARAMS    = 1,
     parameter bit          ENABLE_COVER    = 1,
     parameter bit          ENABLE_DEADLOCK = 1,
     parameter unsigned     MAXWAIT         = 16,
     localparam             STRB_WIDTH      = DATA_WIDTH/8)
   (input wire                  ACLK,
    input wire 			ARESETn,
    input wire 			WVALID,
    input wire 			WREADY,
    input wire [DATA_WIDTH-1:0] WDATA,
    input wire [STRB_WIDTH-1:0] WSTRB);

   // Import the properties in this scope
   import definition_of_axi4_lite::*; 
   import amba_axi4_single_interface_requirements::*;
   // Default clocking for all properties
   default clocking axi4_aclk @(posedge ACLK); endclocking
   logic [DATA_WIDTH-1:0] 	mask_wdata;
   logic 			first_point;
   for (genvar n = 0; n < STRB_WIDTH; n++) begin: mask_valid_byte_lanes
      assign mask_wdata[(8*n)+7:(8*n)] = {8{WSTRB[n]}};
   end
   always_ff @(posedge ACLK) begin
      if (!ARESETn) first_point <= 1'b1;
      else          first_point <= 1'b0;
   end

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section B1.1: Definition of AXI4-Lite                *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   generate
      if (PROTOCOL_TYPE == AXI4LITE) begin: axi4lite_defs
	 if (CHECK_PARAMS) begin: check_dataw
	    ap_W_AXI4LITE_DATAWIDTH: assert property (axi4l_databus_width(DATA_WIDTH))
	      else $error("Violation: AXI4-Lite supports a data bus width of 32-bit or 64-bit",
			  "(B.1 Definition of AXI4-Lite, pB1-126).");
	 end
      end
   endgenerate

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Chapter A3. Single Interface Requirements            *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   generate
      if (AGENT_TYPE == SOURCE || AGENT_TYPE == MONITOR) begin: source_properties
	 // Section A3.1.2: Reset
	 ap_W_SRC_DST_EXIT_RESET: assert property (exit_from_reset(ARESETn, first_point, WVALID))
	   else $error ("Violation: WVALID must be low for the first clock edge",
			"after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 // Section A3.2.1: Handshake process
	 ap_W_SRC_DST_STABLE_WSTRB: assert property (disable iff (!ARESETn) stable_before_handshake(WVALID, WREADY, WSTRB))
	   else $error ("Violation: Once the master has asserted WVALID, data and control information",
			"from master must remain stable [WSTRB] until WREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 ap_W_SRC_DST_STABLE_WDATA: assert property (disable iff (!ARESETn) stable_before_handshake(WVALID, WREADY, (WDATA & mask_wdata)))
	   else $error ("Violation: Once the master has asserted AWVALID, data and control information",
			"from master must remain stable [WDATA] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 ap_W_SRC_DST_AWVALID_until_AWREADY: assert property (disable iff (!ARESETn) valid_before_handshake(WVALID, WREADY))
	   else $error ("Violation: Once WVALID is asserted it must remain asserted until the handshake",
			"occurs (A3.2.1 Handshake process, pA3-39).");
      end // block: source_properties

      else if (AGENT_TYPE == DESTINATION || AGENT_TYPE == CONSTRAINT) begin: destination_properties
	 // Section A3.1.2: Reset
	 cp_W_DST_SRC_EXIT_RESET: assume property (exit_from_reset(ARESETn, first_point, WVALID))
	   else $error ("Violation: WVALID must be low for the first clock edge",
			"after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 // Section A3.2.1: Handshake process
	 cp_W_DST_SRC_STABLE_AWPROT: assume property (disable iff (!ARESETn) stable_before_handshake(WVALID, WREADY, WSTRB))
	   else $error ("Violation: Once the master has asserted WVALID, data and control information",
			"from master must remain stable [WSTRB] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 cp_W_DST_SRC_STABLE_AWADDR: assume property (disable iff (!ARESETn) stable_before_handshake(WVALID, WREADY, (WDATA & mask_wdata)))
	   else $error ("Violation: Once the master has asserted WVALID, data and control information",
			"from master must remain stable [WDATA] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 cp_W_DST_SRC_AWVALID_until_AWREADY: assume property (disable iff (!ARESETn) valid_before_handshake(WVALID, WREADY))
	   else $error ("Violation: Once WVALID is asserted it must remain asserted until the handshake",
			"occurs  (A3.2.1 Handshake process, pA3-39).");
      end // block: destination_properties
   endgenerate

   // AMBA Recommended property for potential deadlock detection
   generate
      if (ENABLE_DEADLOCK)
	if (AGENT_TYPE == DESTINATION || AGENT_TYPE == MONITOR) begin: deadlock_check
	   ap_W_DST_SRC_READY_MAXWAIT: assert property (disable iff (!ARESETn) handshake_max_wait(WVALID, WREADY, MAXWAIT))
	     else $error ("Violation: WREADY should be asserted within MAXWAIT cycles of WVALID being asserted (AMBA Recommended).");
	end
	else if (AGENT_TYPE == SOURCE || AGENT_TYPE == CONSTRAINT) begin: deadlock_cons
	   cp_W_SRC_DST_READY_MAXWAIT: assume property (disable iff (!ARESETn) handshake_max_wait(WVALID, WREADY, MAXWAIT))
	     else $error ("Violation: AWREADY should be asserted within MAXWAIT cycles of AWVALID being asserted (AMBA Recommended).");
	end
   endgenerate

   generate
      // Witnessing scenarios stated in the AMBA AXI4 spec
      if (ENABLE_COVER) begin: witness
	 wp_WVALID_before_WREADY: cover property (disable iff (!ARESETn) valid_before_ready(WVALID, WREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-2 VALID before READY handshake capability.");
	 wp_WREADY_before_WVALID: cover property (disable iff (!ARESETn) ready_before_valid(WVALID, WREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-3 READY before VALID handshake capability.");
	 wp_WVALID_with_WREADY: cover property (disable iff (!ARESETn) valid_with_ready(WVALID, WREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-4 VALID with READY handshake capability.");
      end
   endgenerate
endmodule // amba_axi4_write_data_channel
`default_nettype wire
