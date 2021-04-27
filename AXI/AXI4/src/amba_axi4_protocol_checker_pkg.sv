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
   localparam OKAY   = 2'b00,
              EXOKAY = 2'b01,
              SLVERR = 2'b10,
              DECERR = 2'b11;

   // AxLOCK values
   localparam NORMAL    = 1'b0,
              EXCLUSIVE = 1'b1;

   /* The AXI VIP can  be configured in four different
    * types of agents, listed below. */
   typedef enum logic [1:0] {SOURCE      = 2'b00,
			     DESTINATION = 2'b01,
			     MONITOR     = 2'b10,
			     CONSTRAINT  = 2'b11} axi4_agent_t;

   /* To configure the VIP to check either AXI4 Full
    * or AXI4 lite (the set of properties are different,
    * being AXI4 Full more complicated than AXI4 Lite). */
   typedef enum logic [0:0] {AXI4LITE = 1'b0,
			     AXI4     = 1'b1} axi4_types_t;

   typedef struct packed {
      // AXI4 Port Related Settings
      int unsigned ID_WIDTH;
      int unsigned ADDRESS_WIDTH;
      int unsigned DATA_WIDTH;
      int unsigned AWUSER_WIDTH;
      int unsigned WUSER_WIDTH;
      int unsigned BUSER_WIDTH;
      int unsigned ARUSER_WIDTH;
      int unsigned RUSER_WIDTH;
      // AXI4 Protocol Checker Configuration
      int unsigned MAXWAIT;
      axi4_agent_t AGENT_TYPE;
      axi4_types_t PROTOCOL_TYPE;
      bit	   ENABLE_COVER;
      bit	   ARM_RECOMMENDED;
      bit	   CHECK_PARAMETERS;
      bit          OPTIONAL_WSTRB;	   
      bit	   OPTIONAL_RESET;
   } axi4_checker_params_t;
endpackage // amba_axi4_protocol_checker_pkg
`endif
