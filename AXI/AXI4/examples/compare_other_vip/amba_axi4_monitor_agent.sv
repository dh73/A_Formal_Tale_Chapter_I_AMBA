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
  #(parameter unsigned     ID_WIDTH        = 1,
    parameter unsigned     ADDRESS_WIDTH   = 28,
    parameter unsigned     DATA_WIDTH      = 32,
    parameter unsigned     AWUSER_WIDTH    = 1,
    parameter unsigned     WUSER_WIDTH     = 1,
    parameter unsigned     BUSER_WIDTH     = 1,
    parameter unsigned     ARUSER_WIDTH    = 1,
    parameter unsigned     RUSER_WIDTH     = 1,
    parameter unsigned     MAXWAIT         = 16,
    parameter axi4_agent_t AGENT_TYPE      = MONITOR,
    parameter axi4_types_t PROTOCOL_TYPE   = AXI4LITE,
    parameter bit          ENABLE_COVER    = 1,
    parameter bit          ENABLE_DEADLOCK = 1,
    parameter bit          CHECK_PARAMS    = 1,
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

   amba_axi4_protocol_checker #(.ID_WIDTH(ID_WIDTH),
				.ADDRESS_WIDTH(ADDRESS_WIDTH),
				.DATA_WIDTH(DATA_WIDTH),
				.AWUSER_WIDTH(AWUSER_WIDTH),
				.WUSER_WIDTH(WUSER_WIDTH),
				.BUSER_WIDTH(BUSER_WIDTH),
				.ARUSER_WIDTH(ARUSER_WIDTH),
				.RUSER_WIDTH(RUSER_WIDTH),
				.MAXWAIT(MAXWAIT),
				.AGENT_TYPE(AGENT_TYPE),
				.PROTOCOL_TYPE(PROTOCOL_TYPE),
				.ENABLE_COVER(ENABLE_COVER),
				.ENABLE_DEADLOCK(ENABLE_DEADLOCK),
				.CHECK_PARAMS(CHECK_PARAMS))
   axi4_monitor (.*);
endmodule // amba_axi4_constraint_agent
