`default_nettype none
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
    input wire [2:0] 		   WSTRB);
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
endmodule // amba_axi4_protocol_checker
`default_nettype wire

