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
`default_nettype wire
module amba_axi4_read_data_channel #(parameter DATA_WIDTH=32,
				     parameter MAXWAIT = 16,
				     parameter TYPE = 0, //0 source, 1 dest, [2 mon, 3 cons]
				     )
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
   localparam WDATA_BYTES = STRB_WIDTH;
   logic [DATA_WIDTH-1:0] 	mask_rdata;
   logic [DATA_WIDTH-1:0] 	RDATAvalid;
   logic 			first_point;
   always_ff @(posedge ACLK) begin
      if (!ARESETn) first_point <= 1'b1;
      else          first_point <= 1'b0;
   end
   /* "the master indicates the transfer required and can mask out
    * any unwanted bytes received from the slave".
    * But, since AXI4 does not have read strobes, the mask
    * needs to be calculated. */
   always_comb begin
      genvar n;
      for (n = 0; n < WDATA_BYTES; n++) begin: mask_valid_byte_lanes
	 mask_rdata[(8*n)+7:(8*n)] = {8{\$TODO_calc_mask[n]}};
      end
      RDATAvalid = mask_rdata & WDATA;
   end
   // >> Checker starts here <<
   generate
      if (TYPE == 0) begin: source_properties
	 // Section A3.1.2: Reset
	 assert_R_SRC_DST_EXIT_RESET:   assert property (exit_from_reset(ARESETn, first_point, RVALID))
	   else $error ("Protocol Violation: WVALID must be low for the first clock edge after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 // Section A3.2.1: Handshake process
	 assert_R_SRC_DST_STABLE_RRESP: assert property (disable iff (!ARESETn) stable_before_handshake(RVALID, RREADY, RRESP))
	   else $error ("Protocol Violation: Once the master has asserted RVALID, data and control information from master must remain stable [RRESP] until RREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 assert_R_SRC_DST_STABLE_RDATA: assert property (disable iff (!ARESETn) stable_before_handshake(RVALID, RREADY, RDATAvalid))
	   else $error ("Protocol Violation: Once the master has asserted RWVALID, data and control information from master must remain stable [RDATA] until RREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 assert_R_SRC_DST_RVALID_until_RREADY: assert property (disable iff (!ARESETn) valid_before_handshake(RVALID, RREADY))
	   else $error ("Protocol Violation: Once RVALID is asserted it must remain asserted until the handshake occurs  (A3.2.1 Handshake process, pA3-39).");
	 // Disable iff not ARM recommended
	 assume_R_SRC_DST_READY_MAXWAIT: assume property (disable iff (!ARESETn) handshake_max_wait(RVALID, RREADY, MAXWAIT)) // TODO: hmm, analyse this again
	   else $error ("Protocol Violation: RREADY should be asserted within MAXWAIT cycles of RVALID being asserted.");
      end
      else begin: destination_properties
	 // Section A3.1.2: Reset
	 assume_R_DST_SRC_EXIT_RESET:   assume property (exit_from_reset(ARESETn, first_point, RVALID))
	    else $error ("Protocol Violation: WVALID must be low for the first clock edge after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 // Section A3.2.1: Handshake process
	 assume_R_DST_SRC_STABLE_RRESP: assume property (disable iff (!ARESETn) stable_before_handshake(RVALID, RREADY, RRESP))
	   else $error ("Protocol Violation: Once the master has asserted RVALID, data and control information from master must remain stable [RRESP] until RREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 assume_R_DST_SRC_STABLE_RDATA: assume property (disable iff (!ARESETn) stable_before_handshake(RVALID, RREADY, RDATAvalid))
	   else $error ("Protocol Violation: Once the master has asserted RWVALID, data and control information from master must remain stable [RDATA] until RREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 assume_R_DST_SRC_RVALID_until_RREADY: assume property (disable iff (!ARESETn) valid_before_handshake(RVALID, RREADY))
	   else $error ("Protocol Violation: Once RVALID is asserted it must remain asserted until the handshake occurs  (A3.2.1 Handshake process, pA3-39).");
	 // Disable iff not ARM recommended
	 assert_R_DST_SRC_READY_MAXWAIT: assert property (disable iff (!ARESETn) handshake_max_wait(RVALID, RREADY, MAXWAIT))
	   else $error ("Protocol Violation: RREADY should be asserted within MAXWAIT cycles of RVALID being asserted.");
      end
   endgenerate
endmodule // amba_axi4_read_data_channel
`default_nettype none
