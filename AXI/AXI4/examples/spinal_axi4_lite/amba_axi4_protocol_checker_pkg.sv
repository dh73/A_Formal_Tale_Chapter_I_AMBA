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
`ifndef __AMBA_AXI4_PROTOCOL_CHECKER_PKG__
 `define __AMBA_AXI4_PROTOCOL_CHECKER_PKG__
package amba_axi4_protocol_checker_pkg;
   /* This was originally described as an user defined
    * enum, but to avoid type casting for designs that
    * does not use the same type for BRESP and RRESP,
    * it's better to express this as old-style params. */
   localparam OKAY  = 2'b00, 
              EXOKAY= 2'b01, 
              SLVERR= 2'b10, 
              DECERR= 2'b11;
   
   typedef enum logic [1:0] {SOURCE      = 2'b00, 
			     DESTINATION = 2'b01, 
			     MONITOR     = 2'b10, 
			     CONSTRAINT  = 2'b11} axi4_agent_t;
   
   typedef enum logic [0:0] {AXI4LITE = 1'b0, 
			     AXI4     = 1'b1} axi4_types_t;
   
   // AXI4 Port Related Settings
   localparam unsigned AMBA_AXI4_ADDRESS_WIDTH = 32;
   localparam unsigned AMBA_AXI4_DATA_WIDTH    = 32;
   
   // AXI4 Protocol Checker Configuration
   localparam axi4_agent_t AMBA_AXI4_AGENT_TYPE    = SOURCE;
   localparam axi4_types_t AMBA_AXI4_PROTOCOL_TYPE = AXI4LITE;
   localparam bit AMBA_AXI4_ENABLE_COVERS          = 1;
   localparam bit AMBA_AXI4_ARM_RECOMMENDED        = 1;
   localparam unsigned AMBA_AXI4_MAXWAIT           = 16;
   localparam bit AMBA_AXI4_CHECK_PARAMETERS       = 1;
endpackage // amba_axi4_protocol_checker_pkg
`endif
