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
   #(parameter unsigned     ID_WIDTH        = AMBA_AXI4_ID_WIDTH,
     parameter unsigned     ADDRESS_WIDTH   = AMBA_AXI4_ADDRESS_WIDTH,
     parameter unsigned     DATA_WIDTH      = AMBA_AXI4_DATA_WIDTH,
     parameter unsigned     AWUSER_WIDTH    = AMBA_AXI4_AWUSER_WIDTH,
     parameter unsigned     WUSER_WIDTH     = AMBA_AXI4_WUSER_WIDTH,
     parameter unsigned     BUSER_WIDTH     = AMBA_AXI4_BUSER_WIDTH,
     parameter unsigned     ARUSER_WIDTH    = AMBA_AXI4_ARUSER_WIDTH,
     parameter unsigned     RUSER_WIDTH     = AMBA_AXI4_RUSER_WIDTH,
     parameter unsigned     MAXWAIT         = AMBA_AXI4_MAXWAIT,
     parameter axi4_agent_t AGENT_TYPE      = AMBA_AXI4_AGENT_TYPE,
     parameter axi4_types_t PROTOCOL_TYPE   = AMBA_AXI4_PROTOCOL_TYPE,
     parameter bit          ENABLE_COVER    = AMBA_AXI4_ENABLE_COVER,
     parameter bit          ENABLE_DEADLOCK = AMBA_AXI4_ARM_RECOMMENDED,
     parameter bit          CHECK_PARAMS    = AMBA_AXI4_CHECK_PARAMETERS,
     // Read only
     localparam unsigned    STRB_WIDTH      = DATA_WIDTH/8)
   (input wire                     ACLK,
    input wire 			   ARESETn,
    // Write Address Channel (AW)
    input wire [ID_WIDTH-1:0] 	   AWID,
    input wire [ADDRESS_WIDTH-1:0] AWADDR,
    input wire [7:0] 		   AWLEN,
    input wire [2:0] 		   AWSIZE,
    input wire [1:0] 		   AWBURST,
    input wire 			   AWLOCK,
    input wire [3:0] 		   AWCACHE,
    input wire [2:0] 		   AWPROT,
    input wire [3:0] 		   AWQOS,
    input wire [3:0] 		   AWREGION,
    input wire [AWUSER_WIDTH-1:0]  AWUSER,
    input wire 			   AWVALID,
    input wire 			   AWREADY,
    // Write Data Channel (W)
    input wire [DATA_WIDTH-1:0]    WDATA,
    input wire [STRB_WIDTH-1:0]    WSTRB,
    input wire 			   WLAST,
    input wire [WUSER_WIDTH-1:0]   WUSER,
    input wire 			   WVALID,
    input wire 			   WREADY,
    // Write Response Channel (B)
    input wire [ID_WIDTH-1:0] 	   BID,
    input wire [1:0] 		   BRESP,
    input wire [BUSER_WIDTH-1:0]   BUSER,
    input wire 			   BVALID,
    input wire 			   BREADY,
    // Read Address Channel (AR)
    input wire [ID_WIDTH-1:0] 	   ARID,
    input wire [ADDRESS_WIDTH-1:0] ARADDR,
    input wire [7:0] 		   ARLEN,
    input wire [2:0] 		   ARSIZE,
    input wire [1:0] 		   ARBURST,
    input wire 			   ARLOCK,
    input wire [3:0] 		   ARCACHE,
    input wire [2:0] 		   ARPROT,
    input wire [3:0] 		   ARQOS,
    input wire [3:0] 		   ARREGION,
    input wire [ARUSER_WIDTH-1:0]  ARUSER,
    input wire 			   ARVALID,
    input wire 			   ARREADY,
    // Read Data Channel (R)
    input wire [ID_WIDTH-1:0] 	   RID,
    input wire [DATA_WIDTH-1:0]    RDATA,
    input wire [1:0] 		   RRESP,
    input wire 			   RLAST,
    input wire [RUSER_WIDTH-1:0]   RUSER,
    input wire 			   RVALID,
    input wire 			   RREADY);

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section A1.3: AXI Architecture                       *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "The AXI protocol is burst-based and defines the   *
    * | \\\V/// |   following ~independent~ transaction channels:  "  *
    * |	 |~~~|	|   Ref: A1.3 AXI Architecture, pA1-24.               *
    * |	 |===|	|                                                     *
    * |	 |A  |	|                                                     *
    * |	 | X |	|						      *
    *  \ |  I| /						      *
    *	\|===|/							      *
    *	 '---'							      */
   /* The amba_axi4_protocol_checker is composed of five checkers,
    * each checker models assertions for the five transaction
    * channels defined in 'A1.3 AXI Architecture'.
    * These checkers are independent of each other as well, honoring
    * the architectural obligation from the AXI spec.
    * In other words, the user can bind this module to excercise the
    * AXI channels at once, or take any of the modules instantiated
    * here to verify a channel in particular. */
   
   // Write addres channel properties
   amba_axi4_write_address_channel
     #(.ID_WIDTH(ID_WIDTH),
       .ADDRESS_WIDTH(ADDRESS_WIDTH),
       .DATA_WIDTH(DATA_WIDTH),
       .AWUSER_WIDTH(AWUSER_WIDTH),
       .AGENT_TYPE(AGENT_TYPE),
       .PROTOCOL_TYPE(PROTOCOL_TYPE),
       .CHECK_PARAMS(CHECK_PARAMS),
       .ENABLE_COVER(ENABLE_COVER),
       .ENABLE_DEADLOCK(ENABLE_DEADLOCK),
       .MAXWAIT(MAXWAIT))
   AW_channel_checker(.*);

   // Write data channel properties
   amba_axi4_write_data_channel
     #(.DATA_WIDTH(DATA_WIDTH),
       .WUSER_WIDTH(WUSER_WIDTH),
       .AGENT_TYPE(AGENT_TYPE),
       .PROTOCOL_TYPE(PROTOCOL_TYPE),
       .CHECK_PARAMS(CHECK_PARAMS),
       .ENABLE_COVER(ENABLE_COVER),
       .ENABLE_DEADLOCK(ENABLE_DEADLOCK),
       .MAXWAIT(MAXWAIT))
   W_channel_checker(.*);

   // Write response channel properties
   amba_axi4_write_response_channel
     #(.ID_WIDTH(ID_WIDTH),
       .BUSER_WIDTH(BUSER_WIDTH),
       .AGENT_TYPE(AGENT_TYPE),
       .PROTOCOL_TYPE(PROTOCOL_TYPE),
       .ENABLE_COVER(ENABLE_COVER),
       .ENABLE_DEADLOCK(ENABLE_DEADLOCK),
       .MAXWAIT(MAXWAIT))
   B_channel_checker(.*);

   // Read address channel properties
   amba_axi4_read_address_channel
     #(.ID_WIDTH(ID_WIDTH),
       .ADDRESS_WIDTH(ADDRESS_WIDTH),
       .ARUSER_WIDTH(ARUSER_WIDTH),
       .AGENT_TYPE(AGENT_TYPE),
       .PROTOCOL_TYPE(PROTOCOL_TYPE),
       .ENABLE_COVER(ENABLE_COVER),
       .ENABLE_DEADLOCK(ENABLE_DEADLOCK),
       .MAXWAIT(MAXWAIT))
   AR_channel_checker(.*);

   // Read data channel properties
   amba_axi4_read_data_channel
     #(.ID_WIDTH(ID_WIDTH),
       .DATA_WIDTH(DATA_WIDTH),
       .RUSER_WIDTH(RUSER_WIDTH),
       .AGENT_TYPE(AGENT_TYPE),
       .PROTOCOL_TYPE(PROTOCOL_TYPE),
       .CHECK_PARAMS(CHECK_PARAMS),
       .ENABLE_COVER(ENABLE_COVER),
       .ENABLE_DEADLOCK(ENABLE_DEADLOCK),
       .MAXWAIT(MAXWAIT))
   R_channel_checker(.*);

endmodule // amba_axi4_protocol_checker
`default_nettype wire
