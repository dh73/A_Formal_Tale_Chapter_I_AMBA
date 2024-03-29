/*
 *  AMBA AXI4-Stream Formal Properties.
 *
 *  Copyright (C) 2021  Diego Hernandez <diego@yosyshq.com>
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
import amba_axi4_stream_pkg::*;
module source2sink #(parameter CHECK_TYPE=0) // 0 -> Verify source; 1 -> Verify sink
   (input wire axi4s_aclk    ACLK,
    input wire axi4s_aresetn ARESETn,
    input wire axi4s_data    TDATA,
    input wire axi4s_strb    TSTRB,
    input wire axi4s_keep    TKEEP,
    input wire axi4s_last    TLAST,
    input wire axi4s_id      TID,
    input wire axi4s_dest    TDEST,
    input wire axi4s_user    TUSER,
    input wire axi4s_valid   TVALID,
    input wire axi4s_ready   TREADY);

   typedef enum logic [0:0] {VERIFY_SINK, VERIFY_SOURCE} task_t;
   localparam task_t TASK1     = VERIFY_SOURCE;
   localparam task_t TASK2     = VERIFY_SINK;

   generate
      if (CHECK_TYPE==0) begin: src_to_dst
	 amba_axi4_stream #(.BUS_TYPE(VERIFY_SINK))
	 constraints(.*);
	 amba_axi4_stream #(.BUS_TYPE(VERIFY_SOURCE))
	 source_check(.*);
      end : src_to_dst
      else begin : dst_to_src
	 amba_axi4_stream #(.BUS_TYPE(VERIFY_SOURCE))
	 constraints(.*);
	 amba_axi4_stream #(.BUS_TYPE(VERIFY_SINK))
	 sink_check(.*);
      end : dst_to_src
      endgenerate
endmodule // source2sink


