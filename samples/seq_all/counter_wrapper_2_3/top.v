module top(input ap_clk, input ap_rst,
	      input  [5:0] seed_V,
	
        output [3:0] out_V,
        output out_V_ap_vld);
        
   reg v1_buf;
   wire v1;
   wire [3:0] counter_output1;
   reg [3:0] counter_output1_buf;
   
   reg v2_buf;
   wire v2;
   wire [3:0] counter_output2;
   reg [3:0] counter_output2_buf;
   
   counter2 u1 (
   	.ap_clk(ap_clk), 
   	.ap_rst(ap_rst), .seed_V(seed_V),
   	.out_V(counter_output1), .out_V_ap_vld(v1));
   	
   counter3 u2 (
   	.ap_clk(ap_clk), 
   	.ap_rst(ap_rst), .seed_V(seed_V),
   	.out_V(counter_output2), .out_V_ap_vld(v2));
   	
   always @(posedge ap_clk) begin
     if(ap_rst) begin
       v1_buf <= 0;
       v2_buf <= 0;
     end else begin
       if (v1 && !v1_buf) begin
         v1_buf <= 1;
         counter_output1_buf <= counter_output1;
       end
       if (v2 && !v2_buf) begin
         v2_buf <= 1;
         counter_output2_buf <= counter_output2;
       end       
     end
   end
   
   assert property ( ~(v1_buf && v2_buf) || (counter_output1_buf ==counter_output2_buf) );
   
endmodule
