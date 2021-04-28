`default_nettype none
bind Axi4LitePC amba_axi4_monitor_agent
  axi_compare (.ACLK (ACLK),
	       .ARESETn (ARESETn),
	       .AWADDR (AWADDR),
	       .AWPROT (AWPROT),
	       .AWVALID (AWVALID),
	       .AWREADY (AWREADY),
	       .WDATA (WDATA),
	       .WSTRB (WSTRB),
	       .WVALID (WVALID),
	       .WREADY (WREADY),
	       .BRESP (BRESP),
	       .BVALID (BVALID),
	       .BREADY (BREADY),
	       .ARADDR (ARADDR),
	       .ARPROT (ARPROT),
	       .ARVALID (ARVALID),
	       .ARREADY (ARREADY),
	       .RDATA (RDATA),
	       .RRESP (RRESP),
	       .RVALID (RVALID),
	       .RREADY (RREADY));

module amba_axi4_monitor_agent
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter axi4_checker_params_t cfg =
     '{ID_WIDTH:         4,
       ADDRESS_WIDTH:    32,
       DATA_WIDTH:       32,
       AWUSER_WIDTH:     32,
       WUSER_WIDTH:      32,
       BUSER_WIDTH:      32,
       ARUSER_WIDTH:     32,
       RUSER_WIDTH:      32,
       MAXWAIT:          16,
       AGENT_TYPE:       MONITOR,
       PROTOCOL_TYPE:    AXI4LITE,
       ENABLE_COVER:     1,
       ARM_RECOMMENDED:  1,
       CHECK_PARAMETERS: 1,
       OPTIONAL_WSTRB:   1,
       OPTIONAL_RESET:   0},
     // Read only
     localparam unsigned STRB_WIDTH = cfg.DATA_WIDTH/8)
   (input wire                         ACLK,
    input wire 			       ARESETn,
    // Write Address Channel (AW)
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
    input wire 			       AWREADY,
    // Write Data Channel (W)
    input wire [cfg.DATA_WIDTH-1:0]    WDATA,
    input wire [STRB_WIDTH-1:0]        WSTRB,
    input wire 			       WLAST,
    input wire [cfg.WUSER_WIDTH-1:0]   WUSER,
    input wire 			       WVALID,
    input wire 			       WREADY,
    // Write Response Channel (B)
    input wire [cfg.ID_WIDTH-1:0]      BID,
    input wire [1:0] 		       BRESP,
    input wire [cfg.BUSER_WIDTH-1:0]   BUSER,
    input wire 			       BVALID,
    input wire 			       BREADY,
    // Read Address Channel (AR)
    input wire [cfg.ID_WIDTH-1:0]      ARID,
    input wire [cfg.ADDRESS_WIDTH-1:0] ARADDR,
    input wire [7:0] 		       ARLEN,
    input wire [2:0] 		       ARSIZE,
    input wire [1:0] 		       ARBURST,
    input wire 			       ARLOCK,
    input wire [3:0] 		       ARCACHE,
    input wire [2:0] 		       ARPROT,
    input wire [3:0] 		       ARQOS,
    input wire [3:0] 		       ARREGION,
    input wire [cfg.ARUSER_WIDTH-1:0]  ARUSER,
    input wire 			       ARVALID,
    input wire 			       ARREADY,
    // Read Data Channel (R)
    input wire [cfg.ID_WIDTH-1:0]      RID,
    input wire [cfg.DATA_WIDTH-1:0]    RDATA,
    input wire [1:0] 		       RRESP,
    input wire 			       RLAST,
    input wire [cfg.RUSER_WIDTH-1:0]   RUSER,
    input wire 			       RVALID,
    input wire 			       RREADY);

   amba_axi4_protocol_checker #(.cfg(cfg)) axi4_monitor (.*);

endmodule // amba_axi4_monitor_agent
`default_nettype wire
