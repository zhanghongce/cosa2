module top(input clk, input rst, input lden,  input pause, input [9:0] ia, input [9:0] ib);

reg [9:0] ra, rb, rai, rbi;

always @(posedge clk) begin
  if(rst) begin
    ra <= 0; rb <= 0; rai <= 0; rbi <= 0;
  end else begin
    if(lden) begin
       ra <= ia; rb <= ib;
       rai<= ia; rbi<= ib;
    end else begin
      if(~pause) begin
        rai <= rai + 1;
        rbi <= rbi + 1;
      end
    end
  end
end

assert property (!(ra ==  1023 && rai == 1022 && rb == 512 && rbi == 0) );

endmodule

