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
`ifdef __AMBA_AXI4_PROTOCOL_CHECKER_PKG__
 `define __AMBA_AXI4_PROTOCOL_CHECKER_PKG__
package amba_axi4_protocol_checker_pkg;
   typedef enum logic [1:0] {OKAY, EXOKAY, SLVERR, DECERR} responses_t;
   typedef enum logic [1:0] {SOURCE, DESTINATION, MONITOR, CONSTRAINT} axi4_protocol_t;
   typedef enum logic [0:0] {AXI4LITE, AXI4} axi4_types_t;

   // AXI4 Port Related Settings
   parameter unsigned AMBA_AXI4_ADDRESS_WIDTH        = 32;
   parameter unsigned AMBA_AXI4_DATA_WIDTH           = 64;
   parameter unsigned AMBA_AXI4_MAXWAIT              = 16;
   
   // AXI4 Protocol Checker Configuration
   parameter axi4_protocol_t AMBA_AXI4_AGENT_TYPE    = SOURCE;
   parameter axi4_protocol_t AMBA_AXI4_PROTOCOL_TYPE = AXI4LITE;
   parameter bit AMBA_AXI4_ENABLE_COVERS             = 1;
   parameter bit AMBA_AXI4_ARM_RECOMMENDED           = 1;
   parameter unsigned AMBA_AXI4_MAXWAIT              = 16;
endpackage // amba_axi4_protocol_checker_pkg
`endif