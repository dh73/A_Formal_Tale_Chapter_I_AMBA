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
bind AxiLite4FormalComponent amba_axi4_protocol_checker
  spinal_test (.ACLK(clk),
	       .ARESETn(reset),

	       .AWVALID(io_bus_aw_valid),
	       .AWREADY(io_bus_aw_ready),
	       .AWADDR(io_bus_aw_payload_addr),
	       .AWPROT(io_bus_aw_payload_prot),

	       .WVALID(io_bus_w_valid),
	       .WREADY(io_bus_w_ready),
	       .WDATA(io_bus_w_payload_data),
	       .WSTRB(io_bus_w_payload_strb),

	       .BVALID(io_bus_b_valid),
	       .BREADY(io_bus_b_ready),
	       .BRESP(io_bus_b_payload_resp),

	       .ARVALID(io_bus_ar_valid),
	       .ARREADY(io_bus_ar_ready),
	       .ARADDR(io_bus_ar_payload_addr),
	       .ARPROT(io_bus_ar_payload_prot),

	       .RVALID(io_bus_r_valid),
	       .RREADY(io_bus_r_ready),
	       .RDATA(io_bus_r_payload_data),
	       .RRESP(io_bus_r_payload_resp));
