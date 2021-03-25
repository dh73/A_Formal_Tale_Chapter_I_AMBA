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
module amba_axi4_write_address_channel #(parameter ADDRESS_WIDTH=32,
					 parameter MAXWAIT = 16,
					 parameter TYPE = 0) //0 source, 1 dest, [2 mon, 3 cons]
   (input wire                     ACLK,
    input wire 			   ARESETn,
    input wire 			   AWVALID,
    input wire 			   AWREADY,
    input wire [ADDRESS_WIDTH-1:0] AWADDR,
    input wire [2:0] 		   AWPROT);

   // Import the properties in this scope
   import amba_axi4_single_interface_requirements::*;
   // Default clocking for all properties
   default clocking axi4_aclk @(posedge ACLK); endclocking

   logic first_point;
   always_ff @(posedge ACLK) begin
      if (!ARESETn) first_point <= 1'b1;
      else          first_point <= 1'b0;
   end

   // >> Checker starts here <<
   generate
      if (TYPE == 0) begin: source_properties
	 // Section A3.1.2: Reset
	 assert_AW_SRC_DST_EXIT_RESET:   assert property (exit_from_reset(ARESETn, first_point, AWVALID))
	   else $error ("Protocol Violation: AWVALID must be low for the first clock edge after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 // Section A3.2.1: Handshake process
	 assert_AW_SRC_DST_STABLE_AWPROT: assert property (disable iff (!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWPROT))
	   else $error ("Protocol Violation: Once the master has asserted AWVALID, data and control information from master must remain stable [AWPROT] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 assert_AW_SRC_DST_STABLE_AWADDR: assert property (disable iff (!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWADDR))
	   else $error ("Protocol Violation: Once the master has asserted AWVALID, data and control information from master must remain stable [AWADDR] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 assert_AW_SRC_DST_AWVALID_until_AWREADY: assert property (disable iff (!ARESETn) valid_before_handshake(AWVALID, AWREADY))
	   else $error ("Protocol Violation: Once AWVALID is asserted it must remain asserted until the handshake occurs  (A3.2.1 Handshake process, pA3-39).");
	 // Disable iff not ARM recommended
	 assume_AW_SRC_DST_READY_MAXWAIT: assume property (disable iff (!ARESETn) handshake_max_wait(AWVALID, AWREADY, MAXWAIT))
	   else $error ("Protocol Violation: AWREADY should be asserted within MAXWAIT cycles of AWVALID being asserted.");
      end
      else begin: destination_properties
	 // Section A3.1.2: Reset
	 assume_AW_DST_SRC_EXIT_RESET:   assume property (exit_from_reset(ARESETn, first_point, AWVALID))
	   else $error ("Protocol Violation: AWVALID must be low for the first clock edge after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 // Section A3.2.1: Handshake process
	 assume_AW_DST_SRC_STABLE_AWPROT: assume property (disable iff (!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWPROT))
	   else $error ("Protocol Violation: Once the master has asserted AWVALID, data and control information from master must remain stable [AWPROT] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 assume_AW_DST_SRC_STABLE_AWADDR: assume property (disable iff (!ARESETn) stable_before_handshake(AWVALID, AWREADY, AWADDR))
	   else $error ("Protocol Violation: Once the master has asserted AWVALID, data and control information from master must remain stable [AWADDR] until AWREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 assume_AW_DST_SRC_AWVALID_until_AWREADY: assume property (disable iff (!ARESETn) valid_before_handshake(AWVALID, AWREADY))
	   else $error ("Protocol Violation: Once AWVALID is asserted it must remain asserted until the handshake occurs  (A3.2.1 Handshake process, pA3-39).");
	 assert_AW_DST_SRC_READY_MAXWAIT: assert property (disable iff (!ARESETn) handshake_max_wait(AWVALID, AWREADY, MAXWAIT))
	   else $error ("Protocol Violation: AWREADY should be asserted within MAXWAIT cycles of AWVALID being asserted.");
      end
   endgenerate
endmodule // amba_axi4_write_address_channel
`default_nettype none
