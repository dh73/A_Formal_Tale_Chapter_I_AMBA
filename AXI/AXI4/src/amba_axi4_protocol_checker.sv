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
module amba_axi4_protocol_checker
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter unsigned     ADDRESS_WIDTH   = AMBA_AXI4_ADDRESS_WIDTH,
     parameter unsigned     DATA_WIDTH      = AMBA_AXI4_DATA_WIDTH,
     parameter unsigned     MAXWAIT         = AMBA_AXI4_MAXWAIT,
     parameter axi4_agent_t AGENT_TYPE      = AMBA_AXI4_AGENT_TYPE,
     parameter axi4_types_t PROTOCOL_TYPE   = AMBA_AXI4_PROTOCOL_TYPE,
     parameter bit          ENABLE_COVER    = AMBA_AXI4_ENABLE_COVERS,
     parameter bit          ENABLE_DEADLOCK = AMBA_AXI4_ARM_RECOMMENDED,
     parameter bit          CHECK_PARAMS    = AMBA_AXI4_CHECK_PARAMETERS,
     // Read only
     localparam             STRB_WIDTH      = DATA_WIDTH/8)
   (input wire                     ACLK,
    input wire 			   ARESETn,
    // Write Address Channel (AW)
    input wire 			   AWVALID,
    input wire 			   AWREADY,
    input wire [ADDRESS_WIDTH-1:0] AWADDR,
    input wire [2:0] 		   AWPROT,
    // Write Data Channel (W)
    input wire 			   WVALID,
    input wire 			   WREADY,
    input wire [DATA_WIDTH-1:0]    WDATA,
    input wire [STRB_WIDTH-1:0]    WSTRB,
    // Write Response Channel (B)
    input wire 			   BVALID,
    input wire 			   BREADY,
    input wire [1:0] 		   BRESP,
    // Read Address Channel (AR)
    input wire 			   ARVALID,
    input wire 			   ARREADY,
    input wire [ADDRESS_WIDTH-1:0] ARADDR,
    input wire [2:0] 		   ARPROT,
    // Read Data Channel (R)
    input wire 			   RVALID,
    input wire 			   RREADY,
    input wire [DATA_WIDTH-1:0]    RDATA,
    input wire [1:0] 		   RRESP);

   // Write addres channel properties
   amba_axi4_write_address_channel
     #(.ADDRESS_WIDTH(ADDRESS_WIDTH),
       .AGENT_TYPE(AGENT_TYPE),
       .PROTOCOL_TYPE(PROTOCOL_TYPE),
       .ENABLE_COVER(ENABLE_COVER),
       .ENABLE_DEADLOCK(ENABLE_DEADLOCK),
       .MAXWAIT(MAXWAIT))
   AW_simple_iface_checks (.*);

   // Write data channel properties
   amba_axi4_write_data_channel
     #(.DATA_WIDTH(DATA_WIDTH),
       .AGENT_TYPE(AGENT_TYPE),
       .PROTOCOL_TYPE(PROTOCOL_TYPE),
       .CHECK_PARAMS(CHECK_PARAMS),
       .ENABLE_COVER(ENABLE_COVER),
       .ENABLE_DEADLOCK(ENABLE_DEADLOCK),
       .MAXWAIT(MAXWAIT))
   W_simple_iface_checks (.*);

   // Write response channel properties
   amba_axi4_write_response_channel
     #(.AGENT_TYPE(AGENT_TYPE),
       .PROTOCOL_TYPE(PROTOCOL_TYPE),
       .ENABLE_COVER(ENABLE_COVER),
       .ENABLE_DEADLOCK(ENABLE_DEADLOCK),
       .MAXWAIT(MAXWAIT))
   B_simple_iface_checks (.*);

   // Read address channel properties
   amba_axi4_read_address_channel
     #(.ADDRESS_WIDTH(ADDRESS_WIDTH),
       .AGENT_TYPE(AGENT_TYPE),
       .PROTOCOL_TYPE(PROTOCOL_TYPE),
       .ENABLE_COVER(ENABLE_COVER),
       .ENABLE_DEADLOCK(ENABLE_DEADLOCK),
       .MAXWAIT(MAXWAIT))
   AR_simple_iface_checks (.*);

   // Read data channel properties
   amba_axi4_read_data_channel
     #(.DATA_WIDTH(DATA_WIDTH),
       .AGENT_TYPE(AGENT_TYPE),
       .PROTOCOL_TYPE(PROTOCOL_TYPE),
       .CHECK_PARAMS(CHECK_PARAMS),
       .ENABLE_COVER(ENABLE_COVER),
       .ENABLE_DEADLOCK(ENABLE_DEADLOCK),
       .MAXWAIT(MAXWAIT))
   R_simple_iface_checks (.*);
endmodule // amba_axi4_protocol_checker
`default_nettype wire
