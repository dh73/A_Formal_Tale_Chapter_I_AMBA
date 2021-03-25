`default_nettype none
module amba_axi4_protocol_checker #(parameter ADDRESS_WIDTH=32,
				    parameter MAXWAIT = 16,
				    parameter TYPE = 0) //0 source, 1 dest, [2 mon, 3 cons]
   (input wire                     ACLK,
    input wire 			   ARESETn,
    // Write Address Channel (AW)
    input wire 			   AWVALID,
    input wire 			   AWREADY,
    input wire [ADDRESS_WIDTH-1:0] AWADDR,
    input wire [2:0] 		   AWPROT);


   // Write addres channel simple properties
   amba_axi4_write_address_channel #(.ADDRESS_WIDTH(ADDRESS_WIDTH),
				     .MAXWAIT(MAXWAIT),
				     .TYPE(TYPE)) AW_simple_iface_checks (.*);
endmodule // amba_axi4_protocol_checker
`default_nettype wire

