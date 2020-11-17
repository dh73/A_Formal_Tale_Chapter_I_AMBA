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
`ifndef __AMBA_AXI4_STREAM_SEDA_PKG__
 `define __AMBA_AXI4_STREAM_SEDA_PKG__

/* The Symbiotic EDA AXI Verification IP is configured using
 * the following parameters:
 *       A) AXI_BUS_TYPE: 
 *          When set to 0 acts as sink component.
 *          When set to 1 acts as source component.
 *       B) DATA__WIDTH_BYTES: 
 *          The size of the data bus in BYTES.
 *       C) DEST_WIDTH:
 *          The size of TDEST in BITS.
 *       D) ID_WIDTH:
 *          The size of TID in BITS.
 *       E) USER_WIDTH:
 *          The size of TUSER in BITS.
 *       F) GEN_WITNESS:
 *          Generate witness traces (intended for RTL bringup only).
 *       G) ARM_RECOMMENDED_PROP:
 *          Enable recommended TREADY/TVALID MAXWAIT rule.
 *       H) MAXWAITS:
 *          Configure max clock cycles within a 
 *          TVALID-TREADY handshake.
 *       I) CHECK_SETUP:
 *          Verify simple properties that demonstrate correct
 *          configuration of the AXI VIP.
 *       J) CHECK_XPROP:
 *          Run X-propagation checks with formal, on some
 *          control and data AXI-Stream ports.
 */

package amba_axi4_stream_seda_pkg;
   
   localparam AXI4_STREAM_AXI_BUS_TYPE     =  0;
   localparam AXI4_STREAM_DATA_WIDTH_BYTES =  1; 
   localparam AXI4_STREAM_DEST_WIDTH       =  4; 
   localparam AXI4_STREAM_ID_WIDTH	   =  8;
   localparam AXI4_STREAM_USER_WIDTH       =  0;
   localparam AXI4_STREAM_GEN_WITNESS      =  1; 
   localparam AXI4_STREAM_ARM_RECOMMENDED  =  1; 
   localparam AXI4_STREAM_MAXWAITS	   = 16; 
   localparam AXI4_STREAM_CHECK_SETUP      =  1;
   localparam AXI4_STREAM_RESET_CHECKS     =  1;
   localparam AXI4_STREAM_CHECK_XPROP      =  0;
   // Using the VIP to verify itself
   localparam AXI4_STREAM_VERIFY_VIP       =  0;
   // For X-prop properties
   localparam SEDA_ENABLED_XPROP = 0;
   
   /* NOTE: The following parameters are derived
    * from the user's configuration above.
    * It is not expected that the user should
    * change any of this manually. */
   
   // AXI-Stream port bits definition
   localparam DATA_WIDTH_MAX = (AXI4_STREAM_DATA_WIDTH_BYTES) ? ((AXI4_STREAM_DATA_WIDTH_BYTES * 8) - 1) : 0;
   localparam DEST_WIDTH_MAX = (AXI4_STREAM_DEST_WIDTH) ? ((AXI4_STREAM_DEST_WIDTH) - 1) : 0;
   localparam STRB_WIDTH     = (AXI4_STREAM_DATA_WIDTH_BYTES);
   localparam STRB_WIDTH_MAX = (STRB_WIDTH) ? ((STRB_WIDTH) - 1) : 0;
   localparam KEEP_WIDTH_MAX = (STRB_WIDTH) ? ((STRB_WIDTH) - 1) : 0;
   localparam ID_WIDTH_MAX   = (AXI4_STREAM_ID_WIDTH) ? ((AXI4_STREAM_ID_WIDTH) - 1) : 0;
   localparam USER_WIDTH_MAX = (AXI4_STREAM_USER_WIDTH) ? ((AXI4_STREAM_USER_WIDTH) - 1) : 0;

   // AXI-Stream data types
   typedef logic [USER_WIDTH_MAX : 0] axi_user_t;
   typedef logic [STRB_WIDTH_MAX : 0] axi_strb_t;
   typedef logic [KEEP_WIDTH_MAX : 0] axi_keep_t;
   typedef logic [DATA_WIDTH_MAX : 0] axi_data_t;
   typedef logic [DEST_WIDTH_MAX : 0] axi_dest_t;
   typedef logic [ID_WIDTH_MAX : 0]   axi_id_t;
   typedef logic [0 : 0] 	      axi_ready_t;
   typedef logic [0 : 0] 	      axi_aclk_t;
   typedef logic [0 : 0] 	      axi_arstn_t;
   typedef logic [0 : 0] 	      axi_valid_t;
   typedef logic [0 : 0] 	      axi_last_t;
   
endpackage // amba_axi4_stream_seda_pkg
`endif

