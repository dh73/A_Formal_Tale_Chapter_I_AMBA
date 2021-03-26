`default_nettype none
typedef enum logic [1:0] {OKAY, EXOKAY, SLVERR, DECERR} responses_t;
module amba_axi4_protocol_checker #(parameter ADDRESS_WIDTH=32,
				    parameter DATA_WIDTH=32,
				    parameter MAXWAIT=16,
				    parameter TYPE=0) //0 source, 1 dest, [2 mon, 3 cons]
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
    input wire [2:0] 		   WSTRB,
    // Write Response Channel
    input wire 			   BVALID,
    input wire 			   BREADY,
    input wire 			   responses_t BRESP,
    // Read Address Channel (AR)
    input wire 			   ARVALID,
    input wire 			   ARREADY,
    input wire [ADDRESS_WIDTH-1:0] ARADDR,
    input wire [2:0] 		   ARPROT
    );
   // Write addres channel simple properties
   amba_axi4_write_address_channel 
     #(.ADDRESS_WIDTH(ADDRESS_WIDTH),
       .MAXWAIT(MAXWAIT),
       .TYPE(TYPE)) AW_simple_iface_checks (.*);
   // Write data channel simple properties
   amba_axi4_write_data_channel
     #(.DATA_WIDTH(DATA_WIDTH),
       .MAXWAIT(MAXWAIT),
       .TYPE(TYPE)) W_simple_iface_checks (.*);
   // Write response channel simple properties
   amba_axi4_write_response_channel 
     #(.MAXWAIT(MAXWAIT),
       .TYPE(TYPE)) B_simple_iface_checks (.*);
   // Read address channel simple properties
   amba_axi4_read_address_channel 
     #(.ADDRESS_WIDTH(ADDRESS_WIDTH),
       .MAXWAIT(MAXWAIT),
       .TYPE(TYPE)) AR_simple_iface_checks (.*);
endmodule // amba_axi4_protocol_checker
`default_nettype wire

