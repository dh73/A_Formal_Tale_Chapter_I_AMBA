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
module amba_axi4_read_address_channel
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter axi4_checker_params_t cfg =
     '{ID_WIDTH:        4,
       ADDRESS_WIDTH:   32,
       DATA_WIDTH:      32,
       ARUSER_WIDTH:    32,
       AGENT_TYPE:      SOURCE,
       PROTOCOL_TYPE:   AXI4LITE,
       ENABLE_COVER:    1,
       ARM_RECOMMENDED: 1,
       MAXWAIT:         16,
       OPTIONAL_RESET:  1,
       default:         0},
     // Read only
     localparam unsigned STRB_WIDTH = cfg.DATA_WIDTH/8)
   (input wire                         ACLK,
    input wire 			       ARESETn,
    input wire [cfg.ID_WIDTH-1:0]      ARID,
    input wire [cfg.ADDRESS_WIDTH-1:0] ARADDR,
    input wire [7:0] 		       ARLEN,
    input wire [2:0] 		       ARSIZE,
    input wire [1:0] 		       ARBURST,
    input wire 			       ARLOCK,
    input wire [3:0] 		       ARCACHE,
    input wire [2:0] 		       ARPROT,
    input wire [3:0] 		       ARQOS,
    input wire [3:0] 		       ARREGION,
    input wire [cfg.ARUSER_WIDTH-1:0]  ARUSER,
    input wire 			       ARVALID,
    input wire 			       ARREADY);

   // Import the properties in this scope
   import amba_axi4_definition_of_axi4_lite::*;
   import amba_axi4_single_interface_requirements::*;
   // Default clocking for all properties
   default clocking axi4_aclk @(posedge ACLK); endclocking

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *            Section B1.1: Definition of AXI4-Lite                *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   generate
      if(cfg.PROTOCOL_TYPE == AXI4LITE) begin: axi4lite_defs
	 // AXI4-Lite can have a burst size of either 4 (AWSIZE=3'b010) or 8 (AWSIZE=3'b011).
	 // which is log2(STRB_WIDTH) [if WDATA = 32, STRB=32/8=4, log2(4)=2=AWSIZE of 3'b010.
	 localparam MAX_SIZE = $clog2(STRB_WIDTH); // TODO, guard DW
	 logic AR_unsupported_sig;
	 assign AR_unsupported_sig = (/* The burst length is defined to be 1,
				       * equivalent to an AxLEN value of zero. */
				      ARLEN    == 8'b00000000 &&
				      /* All accesses are defined to be the width
				       * of the data bus. */
				      ARSIZE   == MAX_SIZE &&
				      /* The burst type has no meaning because the burst
				       * length is 1. */
				      ARBURST  == 2'b00 &&
				      /* All accesses are defined as Normal accesses,
				       * equivalent to an AxLOCK value of zero. */
				      ARLOCK   == 1'b0 &&
				      /* All accesses are defined as Non-modifiable,
				       * Non-bufferable, equivalent to an AxCACHE
				       * value of 0b0000. */
				      ARCACHE  == 4'b0000 &&
				      /* A default value of 0b0000 indicates that
				       * the interface is not participating in any
				       * QoS scheme. */
				      ARQOS    == 4'b0000 &&
				      /* Table A10-1 Master interface write channel
				       * signals and default signal values.
				       * AWREGION Default all zeros. */
				      ARREGION == 4'b0000 &&
				      /* Optional User-defined signal in the write address channel.
				       * Supported only in AXI4. */
				      ARUSER   == {cfg.ARUSER_WIDTH{1'b0}} &&
	                              /* AXI4-Lite does not support AXI IDs. This means
	                               * all transactions must be in order, and all
	                               * accesses use a single fixed ID value. */
	                              ARID     == {cfg.ID_WIDTH{1'b0}});

	 // Configure the AXI4-Lite checker unsupported signals.
	 cp_AR_unsupported_axi4l: assume property(disable iff (!ARESETn) axi4_lite_unsupported_sig(AR_unsupported_sig))
	   else $error("Violation: For AR in AXI4-Lite, only signals described in B1.1 are",
		       "required or supported (B1.1 Definition of AXI4-Lite, pB1-126).");

         if(cfg.AGENT_TYPE == DESTINATION || cfg.AGENT_TYPE == MONITOR) begin: a_exclusive_responses
            ap_AR_UNSUPPORTED_EXCLUSIVE: assert property(disable iff (!ARESETn) unsupported_exclusive_access(ARVALID, ARLOCK, EXCLUSIVE))
              else $error("Violation: Exclusive read accesses are not supported in AXI4 Lite",
                          "(Definition of AXI4-Lite, pB1-126).");
         end

         else if(cfg.AGENT_TYPE == SOURCE || cfg.AGENT_TYPE == CONSTRAINT) begin: c_exclusive_responses
            cp_AR_UNSUPPORTED_EXCLUSIVE: assume property(disable iff (!ARESETn) unsupported_exclusive_access(ARVALID, ARLOCK, EXCLUSIVE))
              else $error("Violation: Exclusive read accesses are not supported in AXI4 Lite",
                          "(Definition of AXI4-Lite, pB1-126).");
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
	    ap_AR_SRC_DST_EXIT_RESET: assert property(exit_from_reset(ARESETn, ARVALID))
	      else $error("Violation: ARVALID must be low for the first clock edge",
			  "after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 end

	 // Section A3.2.1: Handshake process
	 ap_AR_SRC_DST_STABLE_ARPROT: assert property(disable iff (!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARPROT))
	   else $error("Violation: Once the master has asserted ARVALID, data and control information",
		       "from master must remain stable [ARPROT] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 ap_AR_SRC_DST_STABLE_ARADDR: assert property(disable iff (!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARADDR))
	   else $error("Violation: Once the master has asserted ARVALID, data and control information",
		       "from master must remain stable [ARADDR] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 ap_AR_SRC_DST_ARVALID_until_ARREADY: assert property(disable iff (!ARESETn) valid_before_handshake(ARVALID, ARREADY))
	   else $error("Violation: Once ARVALID is asserted it must remain asserted until the handshake",
		       "occurs  (A3.2.1 Handshake process, pA3-39).");
      end // block: source_properties

      else if(cfg.AGENT_TYPE == DESTINATION || cfg.AGENT_TYPE == CONSTRAINT) begin: destination_properties
	 // Section A3.1.2: Reset
	 if(cfg.OPTIONAL_RESET == 1) begin: optional_reset
	    cp_AR_DST_SRC_EXIT_RESET: assume property(exit_from_reset(ARESETn, ARVALID))
	      else $error("Violation: ARVALID must be low for the first clock edge after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 end

	 // Section A3.2.1: Handshake process
	 cp_AR_DST_SRC_STABLE_AWPROT: assume property(disable iff (!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARPROT))
	   else $error("Violation: Once the master has asserted ARVALID, data and control information",
		       "from master must remain stable [ARPROT] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 cp_AR_DST_SRC_STABLE_AWADDR: assume property(disable iff (!ARESETn) stable_before_handshake(ARVALID, ARREADY, ARADDR))
	   else $error("Violation: Once the master has asserted ARVALID, data and control information",
		       "from master must remain stable [ARADDR] until ARREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 cp_AR_DST_SRC_AWVALID_until_AWREADY: assume property(disable iff (!ARESETn) valid_before_handshake(ARVALID, ARREADY))
	   else $error("Violation: Once ARVALID is asserted it must remain asserted until the handshake",
		       "occurs  (A3.2.1 Handshake process, pA3-39).");
      end // block: destination_properties
   endgenerate

   // AMBA Recommended property for potential deadlock detection
   generate
      if (cfg.ARM_RECOMMENDED)
	if (cfg.AGENT_TYPE == DESTINATION || cfg.AGENT_TYPE == MONITOR) begin: deadlock_check
	   ap_AR_DST_SRC_READY_MAXWAIT: assert property(disable iff (!ARESETn) handshake_max_wait(ARVALID, ARREADY, cfg.MAXWAIT))
	     else $error("Violation: ARREADY should be asserted within MAXWAIT cycles of ARVALID being asserted (AMBA recommended.");
	end

	else if (cfg.AGENT_TYPE == SOURCE || cfg.AGENT_TYPE == CONSTRAINT) begin: deadlock_cons
	   cp_AR_SRC_DST_READY_MAXWAIT: assume property(disable iff (!ARESETn) handshake_max_wait(ARVALID, ARREADY, cfg.MAXWAIT))
	     else $error("Violation: ARREADY should be asserted within MAXWAIT cycles of ARVALID being asserted (AMBA recommended).");
	end
   endgenerate

   generate
      // Witnessing scenarios stated in the AMBA AXI4 spec
      if (cfg.ENABLE_COVER == 1) begin: witness
	 wp_ARVALID_before_ARREADY: cover property (disable iff (!ARESETn) valid_before_ready(ARVALID, ARREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-2 VALID before READY handshake capability.");
	 wp_ARREADY_before_ARVALID: cover property (disable iff (!ARESETn) ready_before_valid(ARVALID, ARREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-3 READY before VALID handshake capability.");
	 wp_ARVALID_with_ARREADY: cover property (disable iff (!ARESETn) valid_with_ready(ARVALID, ARREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-4 VALID with READY handshake capability.");
      end
   endgenerate
endmodule // amba_axi4_read_address_channel
`default_nettype wire
