module top(input ap_clk, input ap_rst,
input  [5:0] nonce_input_V,
input  [15:0] in_port_V,
	
        output [3:0] output_V,
        output output_V_ap_vld);
        
   reg v1_buf;
   wire v1;
   wire [3:0] output1;
   reg [3:0] output1_buf;
   
   reg v2_buf;
   wire v2;
   wire [3:0] output2;
   reg [3:0] output2_buf;
   
   kalman8_4 u1 (
   	.ap_clk(ap_clk), 
   	.ap_rst(ap_rst), .nonce_input_V(nonce_input_V), .in_port_V(in_port_V),
   	.out_port_V(output1), .out_port_V_ap_vld(v1));
   	
   kalman2_3_3 u2 (
   	.ap_clk(ap_clk), 
   	.ap_rst(ap_rst), .nonce_input_V(nonce_input_V), .in_port_V(in_port_V),
   	.out_port_V(output2), .out_port_V_ap_vld(v2));
   	
   always @(posedge ap_clk) begin
     if(ap_rst) begin
       v1_buf <= 0;
       v2_buf <= 0;
     end else begin
       if (v1 && !v1_buf) begin
         v1_buf <= 1;
         output1_buf <= output1;
       end
       if (v2 && !v2_buf) begin
         v2_buf <= 1;
         output2_buf <= output2;
       end       
     end
   end
   
   assert property ( ~(v1_buf && v2_buf) || (output1_buf == output2_buf) );
   
endmodule
