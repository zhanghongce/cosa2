module top(input ap_clk, input ap_rst,
	      input  [31:0] in_ports_V,
	
        output [31:0] out_V,
        output out_V_ap_vld);
        

   reg v1_buf;
   wire v1;

   wire [31:0] output_1;
   reg [31:0] output1_buf;
   

   reg v2_buf;
   wire v2;

   wire [31:0] output_2;
   reg [31:0] output2_buf;
   
   ellipf4_5_4 u1 (
   	.ap_clk(ap_clk), 
   	.ap_rst(ap_rst), .in_ports_V(in_ports_V),
   	.out_ports_V(output_1),
    .out_ports_V_ap_vld(v1));
   	
   ellipf4_5_5 u2 (
   	.ap_clk(ap_clk), 
   	.ap_rst(ap_rst), .in_ports_V(in_ports_V),
   	.out_ports_V(output_2),
    .out_ports_V_ap_vld(v2));
   	
   always @(posedge ap_clk) begin
     if(ap_rst) begin
       v1_buf <= 0;
       v2_buf <= 0;
     end else begin
       if (v1 && !v1_buf) begin
         v1_buf <= 1;
         output1_buf <= output_1;
       end
       if (v2 && !v2_buf) begin
         v2_buf <= 1;
         output2_buf <= output_2;
       end       
     end
   end
   
   assert property ( ~(v1_buf && v2_buf) || (output1_buf ==output2_buf) );
   
endmodule
