module top (
    input wire selector,
    input wire clk,
    input wire rst,
    output reg [18:0] i,
    output reg [18:0] j,
);


    
    always @(posedge clk) begin
        if(rst)begin
            i<=1;
            j<=800;
        end
        else begin
            if(selector&&(j>=i))begin
                i <= i + 2;
                j <= j - 1;
            end
            else begin
                i  <= i;
                j <= j;
            end
        end
    end
    assert property ((j>=i)||(j==533));
endmodule