`default_nettype none
module faxil_slave_master
  #(// {{{
    parameter  C_AXI_DATA_WIDTH	= 32,// Fixed, width of the AXI R&W data
    parameter  C_AXI_ADDR_WIDTH	= 28,// AXI Address width (log wordsize)
    // F_OPT_XILINX, Certain Xilinx cores impose additional rules upon AXI
    // write transactions, limiting how far the write and write address
    // can be apart.  If F_OPT_XILINX is set, these rules will be applied
    // here as well.  See in-line for more details.
    parameter [0:0]	F_OPT_XILINX = 1'b0,
    parameter [0:0]	F_OPT_HAS_CACHE = 1'b0,
    // F_OPT_WRITE_ONLY, if set, will assume the master is always idle on
    // te read channel, allowing you to test/focus on the write interface
    parameter [0:0]	F_OPT_WRITE_ONLY  = 1'b0,
    // F_OPT_READ_ONLY, if set, will assume the master is always idle on
    // the write channel, while asserting that all of the associated returns
    // and counters are zero
    parameter [0:0]	F_OPT_READ_ONLY = 1'b0,
    // F_OPT_BRESP: Allow any type of write response.  If set clear, then
    // error responses are disallowed.
    parameter [0:0]	F_OPT_BRESP = 1'b1,
    // F_OPT_RRESP, if cleared, will disallow error responses
    parameter [0:0]	F_OPT_RRESP = 1'b1,
    // F_OPT_ASSUME_RESET, if set, will cause the design to *assume* the
    // existence of a correct reset, rather than asserting it.  It is
    // appropriate anytime the reset logic is outside of the circuit being
    // examined
    parameter [0:0]			F_OPT_ASSUME_RESET = 1'b1,
    parameter [0:0]			F_OPT_NO_RESET = 1'b1,
    //
    // F_OPT_ASYNC_RESET is for those designs that will reset the channels
    // using an asynchronous reset.  In these cases, the stability
    // properties only apply when the async reset is not asserted.
    // Likewise, when F_OPT_ASYNC_RESET is set, the reset assertions are
    // applied *on the same clock cycle*, in addition to one cycle later.
    parameter [0:0]			F_OPT_ASYNC_RESET = 1'b0,
    parameter 			F_OPT_COVER_BURST = 1,
    // F_LGDEPTH is the number of bits necessary to count the maximum
    // number of items in flight.
    parameter			F_LGDEPTH	= 4,
    // F_AXI_MAXWAIT is the maximum number of clock cycles the
    // master should have to wait for a slave to raise its ready flag to
    // accept a request.  Set to zero for no limit.
    parameter			F_AXI_MAXWAIT  = 16,
    // F_AXI_MAXRSTALL is the maximum number of clock cycles the
    // slave should have to wait with a return valid signal high, but
    // while the master's return ready signal is low.  Set to zero for no
    // limit.
    parameter			F_AXI_MAXRSTALL= 16,
    // F_AXI_MAXDELAY is the maximum number of clock cycles between request
    // and response within the slave.  Set this to zero for no limit.
    parameter			F_AXI_MAXDELAY = 16,
    //
    parameter [0:0]			F_OPT_INITIAL = 1'b0,

    //
    localparam DW			= C_AXI_DATA_WIDTH,
    localparam AW			= C_AXI_ADDR_WIDTH
    // }}}
    ) (
       // {{{
       input wire 		    i_clk, // System clock
       input wire 		    i_axi_reset_n,

       // AXI write address channel signals
       input wire 		    i_axi_awready,//Slave is ready to accept
       input wire [AW-1:0] 	    i_axi_awaddr, // Write address
       input wire [3:0] 	    i_axi_awcache, // Write Cache type
       input wire [2:0] 	    i_axi_awprot, // Write Protection type
       input wire 		    i_axi_awvalid, // Write address valid

       // AXI write data channel signals
       input wire 		    i_axi_wready, // Write data ready
       input wire [DW-1:0] 	    i_axi_wdata, // Write data
       input wire [DW/8-1:0] 	    i_axi_wstrb, // Write strobes
       input wire 		    i_axi_wvalid, // Write valid

       // AXI write response channel signals
       input wire [1:0] 	    i_axi_bresp, // Write response
       input wire 		    i_axi_bvalid, // Write reponse valid
       input wire 		    i_axi_bready, // Response ready

       // AXI read address channel signals
       input wire 		    i_axi_arready, // Read address ready
       input wire [AW-1:0] 	    i_axi_araddr, // Read address
       input wire [3:0] 	    i_axi_arcache, // Read Cache type
       input wire [2:0] 	    i_axi_arprot, // Read Protection type
       input wire 		    i_axi_arvalid, // Read address valid

       // AXI read data channel signals
       input wire [1:0] 	    i_axi_rresp, // Read response
       input wire 		    i_axi_rvalid, // Read reponse valid
       input wire [DW-1:0] 	    i_axi_rdata, // Read data
       input wire 		    i_axi_rready, // Read Response ready
       //
       output reg [(F_LGDEPTH-1):0] f_saxi_rd_outstanding,
       output reg [(F_LGDEPTH-1):0] f_saxi_wr_outstanding,
       output reg [(F_LGDEPTH-1):0] f_saxi_awr_outstanding,

       output reg [(F_LGDEPTH-1):0] f_maxi_rd_outstanding,
       output reg [(F_LGDEPTH-1):0] f_maxi_wr_outstanding,
       output reg [(F_LGDEPTH-1):0] f_maxi_awr_outstanding
       );

   faxil_slave #(.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		 .C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		 .F_OPT_XILINX(F_OPT_XILINX),
		 .F_OPT_HAS_CACHE(F_OPT_HAS_CACHE),
		 .F_OPT_WRITE_ONLY(F_OPT_WRITE_ONLY),
		 .F_OPT_READ_ONLY(F_OPT_READ_ONLY),
		 .F_OPT_BRESP(F_OPT_BRESP),
		 .F_OPT_RRESP(F_OPT_RRESP),
		 .F_OPT_ASSUME_RESET(F_OPT_ASSUME_RESET),
		 .F_OPT_NO_RESET(F_OPT_NO_RESET),
		 .F_OPT_ASYNC_RESET(F_OPT_ASYNC_RESET),
		 .F_OPT_COVER_BURST(F_OPT_COVER_BURST),
		 .F_LGDEPTH(F_LGDEPTH),
		 .F_AXI_MAXWAIT(F_AXI_MAXWAIT),
		 .F_AXI_MAXRSTALL(F_AXI_MAXRSTALL),
		 .F_AXI_MAXDELAY(F_AXI_MAXDELAY),
		 .F_OPT_INITIAL(F_OPT_INITIAL)) faxil_slave (.*, // what??, why we need outputs here?
							     .f_axi_rd_outstanding(f_saxi_rd_outstanding),
							     .f_axi_wr_outstanding(f_saxi_wr_outstanding),
   							     .f_axi_awr_outstanding(f_saxi_awr_outstanding));

   faxil_master #(.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		  .C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		  .F_OPT_XILINX(F_OPT_XILINX),
		  .F_OPT_HAS_CACHE(F_OPT_HAS_CACHE),
		  .F_OPT_WRITE_ONLY(F_OPT_WRITE_ONLY),
		  .F_OPT_READ_ONLY(F_OPT_READ_ONLY),
		  .F_OPT_BRESP(F_OPT_BRESP),
		  .F_OPT_RRESP(F_OPT_RRESP),
		  .F_OPT_ASSUME_RESET(F_OPT_ASSUME_RESET),
		  .F_OPT_NO_RESET(F_OPT_NO_RESET),
		  .F_OPT_ASYNC_RESET(F_OPT_ASYNC_RESET),
		  .F_OPT_COVER_BURST(F_OPT_COVER_BURST),
		  .F_LGDEPTH(F_LGDEPTH),
		  .F_AXI_MAXWAIT(F_AXI_MAXWAIT),
		  .F_AXI_MAXRSTALL(F_AXI_MAXRSTALL),
		  .F_AXI_MAXDELAY(F_AXI_MAXDELAY),
		  .F_OPT_INITIAL(F_OPT_INITIAL)) faxil_master (.*, // what??, why we need outputs here?
							       .f_axi_rd_outstanding(f_maxi_rd_outstanding),
							       .f_axi_wr_outstanding(f_maxi_wr_outstanding),
   							       .f_axi_awr_outstanding(f_maxi_awr_outstanding));
endmodule // faxil_slave_master
