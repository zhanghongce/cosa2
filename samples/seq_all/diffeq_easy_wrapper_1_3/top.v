module top(input ap_clk, input ap_rst,
	      input  [11:0] vars_V,
	
        output [3:0] out_V,
        output out_V_ap_vld);
        
   reg vu_1_buf;
   reg vx_1_buf;
   reg vy_1_buf;
   wire vx_1;
   wire vy_1;
   wire vu_1;
   wire [3:0] outputx_1;
   wire [3:0] outputy_1;
   wire [3:0] outputu_1;
   reg [3:0] outputx_1_buf;
   reg [3:0] outputy_1_buf;
   reg [3:0] outputu_1_buf;
   
   reg vu_2_buf;
   reg vx_2_buf;
   reg vy_2_buf;
   wire vx_2;
   wire vy_2;
   wire vu_2;
   wire [3:0] outputx_2;
   wire [3:0] outputy_2;
   wire [3:0] outputu_2;
   reg [3:0] outputx_2_buf;
   reg [3:0] outputy_2_buf;
   reg [3:0] outputu_2_buf;
   
   diffeq_easy1 u1 (
   	.ap_clk(ap_clk), 
   	.ap_rst(ap_rst), .vars_V(vars_V),
   	.Xoutport_V(outputx_1),
    .Xoutport_V_ap_vld(vx_1),
    .Youtport_V(outputy_1),
    .Youtport_V_ap_vld(vy_1),
    .Uoutport_V(outputu_1),
    .Uoutport_V_ap_vld(vu_1));
   	
   diffeq_easy3 u2 (
   	.ap_clk(ap_clk), 
   	.ap_rst(ap_rst), .vars_V(vars_V),
   	.Xoutport_V(outputx_2),
    .Xoutport_V_ap_vld(vx_2),
    .Youtport_V(outputy_2),
    .Youtport_V_ap_vld(vy_2),
    .Uoutport_V(outputu_2),
    .Uoutport_V_ap_vld(vu_2));
   	
   always @(posedge ap_clk) begin
     if(ap_rst) begin
       vu_1_buf <= 0;
       vu_2_buf <= 0;
       vx_1_buf <= 0;
       vx_2_buf <= 0;
       vy_1_buf <= 0;
       vy_2_buf <= 0;
     end else begin
       if (vu_1 && !vu_1_buf) begin
         vu_1_buf <= 1;
         outputu_1_buf <= outputu_1;
       end
       if (vu_2 && !vu_2_buf) begin
         vu_2_buf <= 1;
         outputu_2_buf <= outputu_2;
       end       
       if (vx_1 && !vx_1_buf) begin
         vx_1_buf <= 1;
         outputx_1_buf <= outputx_1;
       end
       if (vx_2 && !vx_2_buf) begin
         vx_2_buf <= 1;
         outputx_2_buf <= outputx_2;
       end
       if (vy_1 && !vy_1_buf) begin
         vy_1_buf <= 1;
         outputy_1_buf <= outputy_1;
       end
       if (vy_2 && !vy_2_buf) begin
         vy_2_buf <= 1;
         outputy_2_buf <= outputy_2;
       end
     end
   end
   
   assert property ( (~(vu_1_buf && vu_2_buf) || (outputu_1_buf ==outputu_2_buf))&&(~(vx_1_buf && vx_2_buf) || (outputx_1_buf ==outputx_2_buf))&&(~(vy_1_buf && vy_2_buf) || (outputy_1_buf ==outputy_2_buf)) );
   
endmodule
