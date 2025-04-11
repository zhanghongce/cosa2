module top(input ap_clk, input ap_rst,
	      input  [5:0] seed_V,
          input  [2:0] num_V,
        output [3:0] out_V,
        output out_V_ap_vld);
        
   reg v1_buf;
   wire v_1;
   wire eoc_1;
   wire memw_1;
   wire [3:0] data_V_1;
   wire [2:0] addr_V_1;
   reg eoc_1_buf;
   reg memw_1_buf;
   reg [3:0] data_V_1_buf;
   reg [2:0] addr_V_1_buf;
   
   reg v2_buf;
   wire v_2;
   wire eoc_2;
   wire memw_2;
   wire [3:0] data_V_2;
   wire [2:0] addr_V_2;
   reg eoc_2_buf;
   reg memw_2_buf;
   reg [3:0] data_V_2_buf;
   reg [2:0] addr_V_2_buf;
   
   barcode1 u1 (
   	.ap_clk(ap_clk), 
   	.ap_rst(ap_rst), .seed_V(seed_V),
   	.num_V(num_V),
    .vld(v_1),
    .eoc(eoc_1),
    .memw(memw_1),
    .data_V(data_V_1),
    .addr_V(addr_V_1));
   	
   barcode3 u2 (
   	.ap_clk(ap_clk), 
   	.ap_rst(ap_rst), .seed_V(seed_V),
   	.num_V(num_V),
    .vld(v_2),
    .eoc(eoc_2),
    .memw(memw_2),
    .data_V(data_V_2),
    .addr_V(addr_V_2));
   	
   always @(posedge ap_clk) begin
     if(ap_rst) begin
       v1_buf <= 0;
       v2_buf <= 0;
     end else begin
       if (v_1 && !v1_buf) begin
         v1_buf <= 1;
         eoc_1_buf<=eoc_1;
         memw_1_buf <=memw_1;
         data_V_1_buf <= data_V_1;
         addr_V_1_buf <= addr_V_1;
       end
       if (v_2 && !v2_buf) begin
         v2_buf <= 1;
         eoc_2_buf <= eoc_2;
         memw_2_buf <= memw_2;
         data_V_2_buf <= data_V_2;
         addr_V_2_buf <= addr_V_2;
       end       
     end
   end
   
   assert property ( ~(v1_buf && v2_buf) || ((eoc_1_buf ==eoc_2_buf)&&(memw_1_buf==memw_2_buf)&&(data_V_1_buf==data_V_2_buf)));
   
endmodule
