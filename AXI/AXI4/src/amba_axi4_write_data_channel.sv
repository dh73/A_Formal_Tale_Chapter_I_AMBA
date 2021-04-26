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
   #(parameter axi4_checker_params_t cfg =
     '{DATA_WIDTH:       32,
       WUSER_WIDTH:      32,
       AGENT_TYPE:       SOURCE,
       PROTOCOL_TYPE:    AXI4LITE,
       CHECK_PARAMETERS: 1,
       ENABLE_COVER:     1,
       ARM_RECOMMENDED:  1,
       MAXWAIT:          16,
       default:          0},
     localparam STRB_WIDTH = cfg.DATA_WIDTH/8)
   (input wire                       ACLK,
    input wire 			     ARESETn,
    input wire [cfg.DATA_WIDTH-1:0]  WDATA,
    input wire [STRB_WIDTH-1:0]      WSTRB,
    input wire 			     WLAST,
    input wire [cfg.WUSER_WIDTH-1:0] WUSER,
    input wire 			     WVALID,
    input wire 			     WREADY);

   // Import the properties in this scope
   import definition_of_axi4_lite::*;
   import amba_axi4_single_interface_requirements::*;
   // Default clocking for all properties
   default clocking axi4_aclk @(posedge ACLK); endclocking

   logic [cfg.DATA_WIDTH-1:0] mask_wdata;
   for (genvar n = 0; n < STRB_WIDTH; n++) begin: mask_valid_byte_lanes
      assign mask_wdata[(8*n)+7:(8*n)] = {8{WSTRB[n]}};
   end

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section B1.1: Definition of AXI4-Lite                *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   generate
      if (cfg.PROTOCOL_TYPE == AXI4LITE) begin: axi4lite_defs
	 if (cfg.CHECK_PARAMETERS == 1) begin: check_dataw
	    ap_W_AXI4LITE_DATAWIDTH: assert property (axi4l_databus_width(cfg.DATA_WIDTH))
	      else $error("Violation: AXI4-Lite supports a data bus width of 32-bit or 64-bit",
			  "(B.1 Definition of AXI4-Lite, pB1-126).");
	 end
	 // Now configure unsupported AXI4-Lite signals
	 logic W_unsupported_sig;
	 assign W_unsupported_sig = (/* All bursts are defined to be of length 1,
				      * equivalent to a WLAST or RLAST value of 1. */
				     WLAST  == 1'b1 &&
				     /* Optional User-defined signal in the write address channel.
				      * Supported only in AXI4. */
				     WUSER   == {cfg.WUSER_WIDTH{1'b0}});

	 // Configure the AXI4-Lite checker unsupported signals.
	 cp_W_unsupported_axi4l: assume property(disable iff (!ARESETn) axi4_lite_unsupported_sig(W_unsupported_sig))
	   else $error("Violation: For W in AXI4-Lite, only signals described in B1.1 are",
		       "required or supported (B1.1 Definition of AXI4-Lite, pB1-126).");
      end
   endgenerate

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Chapter A3. Single Interface Requirements            *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   generate
      if (cfg.AGENT_TYPE == SOURCE || cfg.AGENT_TYPE == MONITOR) begin: source_properties
	 // Section A3.1.2: Reset
	 ap_W_SRC_DST_EXIT_RESET: assert property (exit_from_reset(ARESETn, WVALID))
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

      else if (cfg.AGENT_TYPE == DESTINATION || cfg.AGENT_TYPE == CONSTRAINT) begin: destination_properties
	 // Section A3.1.2: Reset
	 cp_W_DST_SRC_EXIT_RESET: assume property (exit_from_reset(ARESETn, WVALID))
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
      if (cfg.ARM_RECOMMENDED)
	if (cfg.AGENT_TYPE == DESTINATION || cfg.AGENT_TYPE == MONITOR) begin: deadlock_check
	   ap_W_DST_SRC_READY_MAXWAIT: assert property (disable iff (!ARESETn) handshake_max_wait(WVALID, WREADY, cfg.MAXWAIT))
	     else $error ("Violation: WREADY should be asserted within MAXWAIT cycles of WVALID being asserted (AMBA Recommended).");
	end
	else if (cfg.AGENT_TYPE == SOURCE || cfg.AGENT_TYPE == CONSTRAINT) begin: deadlock_cons
	   cp_W_SRC_DST_READY_MAXWAIT: assume property (disable iff (!ARESETn) handshake_max_wait(WVALID, WREADY, cfg.MAXWAIT))
	     else $error ("Violation: AWREADY should be asserted within MAXWAIT cycles of AWVALID being asserted (AMBA Recommended).");
	end
   endgenerate

   generate
      // Witnessing scenarios stated in the AMBA AXI4 spec
      if (cfg.ENABLE_COVER == 1) begin: witness
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
