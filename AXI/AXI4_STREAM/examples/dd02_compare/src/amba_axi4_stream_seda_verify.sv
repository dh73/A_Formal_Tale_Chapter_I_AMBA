/*
 *  AXI Formal Verification IP 2.0.
 *
 *  Copyright (C) 2020  Diego Hernandez <diego@symbioticeda.com>
 *
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
 *
 */
`default_nettype none
import amba_axi4_stream_seda_pkg::*;

module amba_axi4_stream_seda_verify
  #(parameter AXI_BUS_TYPE    = AXI4_STREAM_AXI_BUS_TYPE, 
    parameter GEN_WITNESS     = AXI4_STREAM_GEN_WITNESS,
    parameter ARM_RECOMMENDED = AXI4_STREAM_ARM_RECOMMENDED,
    parameter MAXWAITS	      = AXI4_STREAM_MAXWAITS,
    parameter CHECK_SETUP     = AXI4_STREAM_CHECK_SETUP,
    parameter RESET_CHECKS    = AXI4_STREAM_RESET_CHECKS,
    parameter CHECK_XPROP     = AXI4_STREAM_CHECK_XPROP,
    parameter VERIFY_VIP      = 1)
   (input wire axi_data_t  TDATA,
    input wire axi_strb_t  TSTRB,
    input wire axi_keep_t  TKEEP,
    input wire axi_last_t  TLAST,
    input wire axi_id_t    TID,
    input wire axi_dest_t  TDEST,
    input wire axi_user_t  TUSER,
    input wire axi_valid_t TVALID,
    input wire axi_ready_t TREADY,
    input wire axi_aclk_t  ACLK,
    input wire axi_arstn_t ARESETn);
   
   generate
      if (AXI_BUS_TYPE == 0) begin: axis_sink
	 faxis_slave #(.F_MAX_PACKET(0),
		       .F_MIN_PACKET(0),
		       .F_MAX_STALL(0),
		       .C_S_AXI_DATA_WIDTH(AXI4_STREAM_DATA_WIDTH_BYTES*8),
		       .C_S_AXI_ID_WIDTH(AXI4_STREAM_ID_WIDTH),
		       .C_S_AXI_ADDR_WIDTH(AXI4_STREAM_DEST_WIDTH), // ???
		       .C_S_AXI_USER_WIDTH(AXI4_STREAM_USER_WIDTH),
		       .F_LGDEPTH(32)) faxis_slave_top
	 (.i_aclk(ACLK), 
	  .i_aresetn(ARESETn),
	  .i_tvalid(TVALID), 
	  .i_tready(TREADY),
	  .i_tdata(TDATA), 
	  .i_tstrb(TSTRB), 
	  .i_tkeep(TKEEP), 
	  .i_tlast(TLAST), 
	  .i_tid(TID),
	  .i_tdest(TDEST), 
	  .i_tuser(TUSER),
	  .f_bytecount(), // free
	  .f_routecheck()); // free
	 if (VERIFY_VIP == 1) begin: axis_helper
	    amba_axi4_stream_seda
	      #(1,
		ARM_RECOMMENDED,
		MAXWAITS,
		CHECK_SETUP,
		RESET_CHECKS,
		CHECK_XPROP) source_checker_helper (.*);
	 end
      end // block: axis_sink
   endgenerate
endmodule // amba_axi4_stream_seda_top

