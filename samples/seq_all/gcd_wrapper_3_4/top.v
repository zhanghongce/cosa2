module top(input ap_clk, input ap_rst,
	input  [3:0] x_var_V,
	input  [3:0] y_var_V,
	
        output [3:0] gcd_output_V,
        output gcd_output_V_ap_vld);
        
   reg v1_buf;
   wire v1;
   wire [3:0] gcd_output1;
   reg [3:0] gcd_output1_buf;
   
   reg v2_buf;
   wire v2;
   wire [3:0] gcd_output2;
   reg [3:0] gcd_output2_buf;
   
   gcd3 u1 (
   	.ap_clk(ap_clk), 
   	.ap_rst(ap_rst), .x_var_V(x_var_V), .y_var_V(y_var_V),
   	.gcd_output_V(gcd_output1), .gcd_output_V_ap_vld(v1));
   	
   gcd4 u2 (
   	.ap_clk(ap_clk), 
   	.ap_rst(ap_rst), .x_var_V(x_var_V), .y_var_V(y_var_V),
   	.gcd_output_V(gcd_output2), .gcd_output_V_ap_vld(v2));
   	
   always @(posedge ap_clk) begin
     if(ap_rst) begin
       v1_buf <= 0;
       v2_buf <= 0;
     end else begin
       if (v1 && !v1_buf) begin
         v1_buf <= 1;
         gcd_output1_buf <= gcd_output1;
       end
       if (v2 && !v2_buf) begin
         v2_buf <= 1;
         gcd_output2_buf <= gcd_output2;
       end       
     end
   end
   
   assert property ( ~(v1_buf && v2_buf) || (gcd_output1_buf == gcd_output2_buf) );
   
endmodule
