`default_nettype none
bind faxil_slave_master amba_axi4_monitor_agent
  axi_compare (.ACLK(i_clk),
	       .ARESETn(i_axi_reset_n),

	       .AWID(),
	       .AWADDR(i_axi_awaddr),
	       .AWLEN(),
	       .AWSIZE(),
	       .AWBURST(),
	       .AWLOCK(),
	       .AWCACHE(i_axi_awcache),
	       .AWPROT(i_axi_awprot),
	       .AWQOS(),
	       .AWREGION(),
	       .AWUSER(),
	       .AWVALID(i_axi_awvalid),
	       .AWREADY(i_axi_awready),

	       .WDATA(i_axi_wdata),
	       .WSTRB(i_axi_wstrb),
	       .WLAST(),
	       .WUSER(),
	       .WVALID(i_axi_wvalid),
	       .WREADY(i_axi_wready),

	       .BID(),
	       .BRESP(i_axi_bresp),
	       .BUSER(),
	       .BVALID(i_axi_bvalid),
	       .BREADY(i_axi_bready),

	       .ARID(),
	       .ARADDR(i_axi_araddr),
	       .ARLEN(),
	       .ARSIZE(),
	       .ARBURST(),
	       .ARLOCK(),
	       .ARCACHE(i_axi_arcache),
	       .ARPROT(i_axi_arprot),
	       .ARQOS(),
	       .ARREGION(),
	       .ARUSER(),
	       .ARVALID(i_axi_arvalid),
	       .ARREADY(i_axi_arready),

	       .RID(),
	       .RDATA(i_axi_rdata),
	       .RRESP(i_axi_rresp),
	       .RLAST(),
	       .RUSER(),
	       .RVALID(i_axi_rvalid),
	       .RREADY(i_axi_rready));

module amba_axi4_monitor_agent
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter axi4_checker_params_t cfg =
     '{ID_WIDTH:         4,
       ADDRESS_WIDTH:    32,
       DATA_WIDTH:       64,
       AWUSER_WIDTH:     32,
       WUSER_WIDTH:      32,
       BUSER_WIDTH:      32,
       ARUSER_WIDTH:     32,
       RUSER_WIDTH:      32,
       MAXWAIT:          16,
       AGENT_TYPE:       SOURCE,
       PROTOCOL_TYPE:    AXI4LITE,
       ENABLE_COVER:     1,
       ARM_RECOMMENDED:  1,
       CHECK_PARAMETERS: 1,
       OPTIONAL_WSTRB:   0,  // disabling optional full wstrb
       OPTIONAL_RESET:   0}, // disabling optional reset
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
   
endmodule // amba_axi4_constraint_agent
