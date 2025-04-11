module top (
    input wire selector,
    input wire clk,
    input wire rst,
    output reg [10:0] x,
    output reg [10:0] y,
    output reg [10:0] i,
    output reg [10:0] n
);



    
    always @(posedge clk) begin
        if(rst)begin
            x<=0;
            y<=0;
            i<=0;
            n<=200;
        end
        else begin
                if (i<n) begin
                    i<=i+1;
                    n<=n;
                    if(selector)begin
                        x<=x+1;
                        y<=y+2;
                    end
                    else begin
                        x<=x+2;
                        y<=y+1;
                    end
                end
                else begin
                    x<=x;
                    y<=y;
                    i<=i;
                    n<=n;                
                end
            end
        end
    
    assert property (n>i||(3*n==x+y));
endmodule