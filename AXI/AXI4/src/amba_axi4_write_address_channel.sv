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
module amba_axi4_write_address_channel
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter axi4_checker_params_t cfg =
     '{ID_WIDTH:         4,
       ADDRESS_WIDTH:    32,
       DATA_WIDTH:       32,
       AWUSER_WIDTH:     32,
       AGENT_TYPE:       SOURCE,
       PROTOCOL_TYPE:    AXI4LITE,
       CHECK_PARAMETERS: 1,
       ENABLE_COVER:     1,
       ARM_RECOMMENDED:  1,
       MAXWAIT:          16,
       OPTIONAL_RESET:   1,
       default:          0},
     // Read only
     localparam unsigned STRB_WIDTH = cfg.DATA_WIDTH/8)
   (input wire                         ACLK,
    input wire 			       ARESETn,
    input wire [cfg.ID_WIDTH-1:0]      AWID,
    input wire [cfg.ADDRESS_WIDTH-1:0] AWADDR,
    input wire [7:0] 		       AWLEN,
    input wire [2:0] 		       AWSIZE,
    input wire [1:0] 		       AWBURST,
    input wire 			       AWLOCK,
    input wire [3:0] 		       AWCACHE,
    input wire [2:0] 		       AWPROT,
    input wire [3:0] 		       AWQOS,
    input wire [3:0] 		       AWREGION,
    input wire [cfg.AWUSER_WIDTH-1:0]  AWUSER,
    input wire 			       AWVALID,
    input wire 			       AWREADY);

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
	 // Guard correct AXI4-Lite DATA_WIDTH since the parameter is used here.
	 if(cfg.CHECK_PARAMETERS == 1) begin: check_dataw
            ap_W_AXI4LITE_DATAWIDTH: assert property(axi4l_databus_width(cfg.DATA_WIDTH))
              else $error("Violation: AXI4-Lite supports a data bus width of 32-bit or 64-bit",
                          "(B.1 Definition of AXI4-Lite, pB1-126).");
         end
	 // Now configure unsupported AXI4-Lite signals
	 logic AW_unsupported_sig;
	 // "all transactions are of burst length 1".
	 // "all data accesses use the full width of the data bus".
	 // "AXI4-Lite supports a data bus width of 32-bit or 64-bit". (B1.1, pB1-126).
	 // AXI4-Lite can have a burst size of either 4 (AWSIZE=3'b010) or 8 (AWSIZE=3'b011).
	 // which is log2(STRB_WIDTH) [if WDATA = 32, STRB=32/8=4, log2(4)=2=AWSIZE of 3'b010.
	 localparam MAX_SIZE = $clog2(STRB_WIDTH);
	 assign AW_unsupported_sig = (/* The burst length is defined to be 1,
				       * equivalent to an AxLEN value of zero. */
				      AWLEN    == 8'b00000000 &&
				      /* All accesses are defined to be the width
				       * of the data bus. */
				      AWSIZE   == MAX_SIZE &&
				      /* The burst type has no meaning because the burst
				       * length is 1. */
				      AWBURST  == 2'b00 &&
				      /* All accesses are defined as Normal accesses,
				       * equivalent to an AxLOCK value of zero. */
				      AWLOCK   == 1'b0 &&
				      /* All accesses are defined as Non-modifiable,
				       * Non-bufferable, equivalent to an AxCACHE
				       * value of 0b0000. */
				      AWCACHE  == 4'b0000 &&
				      /* A default value of 0b0000 indicates that
				       * the interface is not participating in any
				       * QoS scheme. */
				      AWQOS    == 4'b0000 &&
				      /* Table A10-1 Master interface write channel
				       * signals and default signal values.
				       * AWREGION Default all zeros. */
				      AWREGION == 4'b0000 &&
				      /* Optional User-defined signal in the write address channel.
				       * Supported only in AXI4. */
				      AWUSER   == {cfg.AWUSER_WIDTH{1'b0}} &&
	                              /* AXI4-Lite does not support AXI IDs. This means
	                               * all transactions must be in order, and all
	                               * accesses use a single fixed ID value. */
	                              AWID     == {cfg.ID_WIDTH{1'b0}});

	 // Configure the AXI4-Lite checker unsupported signals.
	 cp_AW_unsupported_axi4l: assume property(disable iff (!ARESETn) axi4_lite_unsupported_sig(AW_unsupported_sig))
	   else $error("Violation: For AW in AXI4-Lite, only signals described in B1.1 are",
		       "required or supported (B1.1 Definition of AXI4-Lite, pB1-126).");

	 if (cfg.AGENT_TYPE == DESTINATION || cfg.AGENT_TYPE == MONITOR) begin: a_exclusive_responses
            ap_AW_UNSUPPORTED_EXCLUSIVE: assert property(disable iff (!ARESETn) unsupported_exclusive_access(AWVALID, AWLOCK, EXCLUSIVE))
              else $error("Violation: Exclusive read accesses are not supported in AXI4 Lite",
                          "(Definition of AXI4-Lite, pB1-126).");
         end
         else if (cfg.AGENT_TYPE == SOURCE || cfg.AGENT_TYPE == CONSTRAINT) begin: c_exclusive_responses
            cp_AW_UNSUPPORTED_EXCLUSIVE: assume property(disable iff (!ARESETn) unsupported_exclusive_access(AWVALID, AWLOCK, EXCLUSIVE))
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
	    ap_AW_SRC_DST_EXIT_RESET: assert property(exit_from_reset(ARESETn, AWVALID))
	      else $error("Violation: AWVALID must be low for the first clock edge",
			  "after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 end

	 // Section A3.2.1: Handshake process
	 ap_AW_SRC_DST_STABLE_AWPROT: assert property(disable iff (!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWPROT))
	   else $error("Violation: Once the master has asserted AWVALID, data and control information",
		       "from master must remain stable [AWPROT] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 ap_AW_SRC_DST_STABLE_AWADDR: assert property(disable iff (!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWADDR))
	   else $error("Violation: Once the master has asserted AWVALID, data and control information",
		       "from master must remain stable [AWADDR] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 ap_AW_SRC_DST_AWVALID_until_AWREADY: assert property(disable iff (!ARESETn) valid_before_handshake(AWVALID, AWREADY))
	   else $error("Violation: Once AWVALID is asserted it must remain asserted until the handshake",
		       "occurs (A3.2.1 Handshake process, pA3-39).");
      end // block: source_properties

      else if(cfg.AGENT_TYPE == DESTINATION || cfg.AGENT_TYPE == CONSTRAINT) begin: destination_properties
	 // Section A3.1.2: Reset
	 if(cfg.OPTIONAL_RESET == 1) begin: optional_reset
	    cp_AW_DST_SRC_EXIT_RESET: assume property(exit_from_reset(ARESETn, AWVALID))
	      else $error("Violation: AWVALID must be low for the first clock edge",
			  "after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 end

	 // Section A3.2.1: Handshake process
	 cp_AW_DST_SRC_STABLE_AWPROT: assume property(disable iff (!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWPROT))
	   else $error("Violation: Once the master has asserted AWVALID, data and control information",
		       "from master must remain stable [AWPROT] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 cp_AW_DST_SRC_STABLE_AWADDR: assume property(disable iff (!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWADDR))
	   else $error("Violation: Once the master has asserted AWVALID, data and control information",
		       "from master must remain stable [AWADDR] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 cp_AW_DST_SRC_AWVALID_until_AWREADY: assume property(disable iff (!ARESETn) valid_before_handshake(AWVALID, AWREADY))
	   else $error("Violation: Once AWVALID is asserted it must remain asserted until the handshake",
		       "occurs  (A3.2.1 Handshake process, pA3-39).");
      end // block: destination_properties
   endgenerate

   // AMBA Recommended property for potential deadlock detection
   generate
      if(cfg.ARM_RECOMMENDED == 1)
	if(cfg.AGENT_TYPE == DESTINATION || cfg.AGENT_TYPE == MONITOR) begin: deadlock_check
	   ap_AW_SRC_DST_READY_MAXWAIT: assert property(disable iff (!ARESETn) handshake_max_wait(AWVALID, AWREADY, cfg.MAXWAIT))
	     else $error("Violation: AWREADY should be asserted within MAXWAIT cycles of AWVALID being asserted (AMBA recommended).");
	end
	else if(cfg.AGENT_TYPE == SOURCE || cfg.AGENT_TYPE == CONSTRAINT) begin: deadlock_cons
	   cp_AW_SRC_DST_READY_MAXWAIT: assume property(disable iff (!ARESETn) handshake_max_wait(AWVALID, AWREADY, cfg.MAXWAIT)) // TODO: hmm, analyse this again.
	     else $error("Violation: RREADY should be asserted within MAXWAIT cycles of RVALID being asserted (AMBA recommended).");
	end
   endgenerate

   // Witnessing scenarios stated in the AMBA AXI4 spec
   generate
      if(cfg.ENABLE_COVER == 1) begin: witness
	 wp_AWVALID_before_AWREADY: cover property(disable iff (!ARESETn) valid_before_ready(AWVALID, AWREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-2 VALID before READY handshake capability.");
	 wp_AWREADY_before_AWVALID: cover property(disable iff (!ARESETn) ready_before_valid(AWVALID, AWREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-3 READY before VALID handshake capability.");
	 wp_AWVALID_with_AWREADY: cover property(disable iff (!ARESETn) valid_with_ready(AWVALID, AWREADY))
	   $info("Witnessed: Handshake process pA3-39, Figure A3-4 VALID with READY handshake capability.");
	 wp_AW_B2B: cover property(disable iff(!ARESETn) axi4_back_to_back(AWVALID, AWREADY))
	   $info("Witnessed: Back to back transaction on AW channel.");
	 wp_AW_WAIT: cover property(disable iff(!ARESETn) axi4_wait_state(AWVALID, AWREADY))
	   $info("Witnessed: Wait state during transaction on AW channel.");
	 wp_AW_NO_WAIT: cover property(disable iff(!ARESETn) axi4_no_wait_state(AWVALID, AWREADY))
	   $info("Witnessed: No wait states during transaction on AW channel.");
      end
   endgenerate
endmodule // amba_axi4_write_address_channel
`default_nettype wire
