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
typedef enum logic [1:0] {OKAY, EXOKAY, SLVERR, DECERR} responses_t;
module amba_axi4_write_response_channel #(parameter MAXWAIT = 16,
					  parameter TYPE = 0) //0 source, 1 dest, [2 mon, 3 cons]
   (input wire ACLK,
    input wire ARESETn,
    input wire BVALID,
    input wire BREADY,
    input wire responses_t BRESP);

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
	 assert_B_SRC_DST_EXIT_RESET:   assert property (exit_from_reset(ARESETn, first_point, BVALID))
	   else $error ("Protocol Violation: BVALID must be low for the first clock edge after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 // Section A3.2.1: Handshake process
	 assert_B_SRC_DST_STABLE_BRESP: assert property (disable iff (!ARESETn) stable_before_handshake(BVALID, BREADY, BRESP))
	   else $error ("Protocol Violation: Once the master has asserted BVALID, data and control information from master must remain stable [BRESP] until BREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 assert_B_SRC_DST_BVALID_until_BREADY: assert property (disable iff (!ARESETn) valid_before_handshake(BVALID, BREADY))
	   else $error ("Protocol Violation: Once BVALID is asserted it must remain asserted until the handshake occurs (A3.2.1 Handshake process, pA3-39).");
	 // Disable iff not ARM recommended
	 assume_B_SRC_DST_READY_MAXWAIT: assume property (disable iff (!ARESETn) handshake_max_wait(BVALID, BREADY, MAXWAIT))
	   else $error ("Protocol Violation: BREADY should be asserted within MAXWAIT cycles of BVALID being asserted.");
      end
      else begin: destination_properties
	 // Section A3.1.2: Reset
	 assume_B_DST_SRC_EXIT_RESET:   assume property (exit_from_reset(ARESETn, first_point, BVALID))
	   else $error ("Protocol Violation: BVALID must be low for the first clock edge after ARESETn goes high (A3.2.1 Reset, pA3-38, Figure A3-1).");
	 // Section A3.2.1: Handshake process
	 assume_B_DST_SRC_STABLE_BRESP: assume property (disable iff (!ARESETn) stable_before_handshake(BVALID, BREADY, BRESP))
	   else $error ("Protocol Violation: Once the master has asserted BVALID, data and control information from master must remain stable [BRESP] until BREADY is asserted (A3.2.1 Handshake process, pA3-39, Figure A3-2).");
	 assume_B_DST_SRC_BVALID_until_BREADY: assume property (disable iff (!ARESETn) valid_before_handshake(BVALID, BREADY))
	   else $error ("Protocol Violation: Once BVALID is asserted it must remain asserted until the handshake occurs (A3.2.1 Handshake process, pA3-39).");
	 // Disable iff not ARM recommended
	 assert_B_DST_SRC_READY_MAXWAIT: assert property (disable iff (!ARESETn) handshake_max_wait(BVALID, BREADY, MAXWAIT))
	   else $error ("Protocol Violation: BREADY should be asserted within MAXWAIT cycles of BVALID being asserted.");
      end
   endgenerate
endmodule // amba_axi4_write_response_channel
`default_nettype none
