`default_nettype none
import amba_axi4_stream_seda_pkg::*;
typedef enum logic [0:0] {VERIFY_SINK, VERIFY_SOURCE} task_t;

module source2sink #(parameter task_t TASK1    = VERIFY_SOURCE,
		     parameter task_t TASK2    = VERIFY_SINK,
		     parameter GEN_WITNESS     = AXI4_STREAM_GEN_WITNESS,
		     parameter ARM_RECOMMENDED = AXI4_STREAM_ARM_RECOMMENDED,
		     parameter MAXWAITS	       = AXI4_STREAM_MAXWAITS,
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

   amba_axi4_stream_seda #(VERIFY_SINK, ARM_RECOMMENDED, MAXWAITS, CHECK_SETUP, RESET_CHECKS, CHECK_XPROP) axis_sink (.*); // Constraints
   amba_axi4_stream_seda #(VERIFY_SOURCE, ARM_RECOMMENDED, MAXWAITS, CHECK_SETUP, RESET_CHECKS, CHECK_XPROP) axis_source (.*); // Source
endmodule // source2sink



