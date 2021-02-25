/*
 *  AXI Formal Verification IP 2.0.
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
// Changelog
// 20/11/2020: Removed generate block since faxis_master is not provided as
//             part of the licensed components, therefore I can't select
//             which component to check.
`default_nettype none
import amba_axi4_stream_pkg::*;

module amba_axi4_stream_seda_verify
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
 
   faxis_slave 
     #(.F_MAX_PACKET(0),
       .F_MIN_PACKET(0),
       .F_MAX_STALL(0),
       .C_S_AXI_DATA_WIDTH(AXI4_STREAM_DATA_WIDTH_BYTES*8),
       .C_S_AXI_ID_WIDTH(AXI4_STREAM_ID_WIDTH),
       .C_S_AXI_ADDR_WIDTH(AXI4_STREAM_DEST_WIDTH), // ???
       .C_S_AXI_USER_WIDTH(AXI4_STREAM_USER_WIDTH),
       .F_LGDEPTH(32)) 
   faxis_slave_top
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
   
   // New Symbiotic EDA VIP
   amba_axi4_stream
     #(.BUS_TYPE(1)) 
   source_checker_helper (.*);
   
endmodule // amba_axi4_stream_seda_top

