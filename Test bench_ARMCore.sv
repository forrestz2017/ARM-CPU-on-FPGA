// Test bench for ARM core
//Programmer: Forrest Zhang
//Last modified: 8/6/2024
//Notes: remember to change the file name for loading test vector instructions

module tb_arm_core();

  reg clk;
  reg reset;
  reg [31:0] instruction_memory [0:255]; // Instruction memory
  reg [31:0] write_data;
  reg [15:0] address;
  reg write_enable;
  reg read_enable;
  wire [31:0] read_data;
  wire ready;

  // Instantiate the ARM core
  ARM_Core dut (
      .clk(clk),
      .reset(reset),
      .instruction_memory(instruction_memory), // Connect the instruction memory
      .write_data(write_data),
      .address(address),
      .write_enable(write_enable),
      .read_enable(read_enable),
      .read_data(read_data),
      .ready(ready)
  );

  initial begin
      // Initialize signals
      clk = 0;
      reset = 0;
      write_enable = 0;
      read_enable = 0;
      address = 16'h0000;
      write_data = 32'hDEADBEEF;

      // Load instructions into the instruction memory from binary file
      $readmemh("test_vector.bin", instruction_memory);

      // Apply reset
      #5 reset = 1;
      #10 reset = 0;

      // Perform write operation
      #20 write_enable = 1;
      #10 write_enable = 0;

      // Perform read operation
      #20 read_enable = 1;
      #10 read_enable = 0;

      // Monitor read/write operation
      #100 $finish;
  end

  always #5 clk = ~clk; // Clock generation

  initial begin
      $dumpfile("tb_arm_core.vcd"); // VCD file for waveform
      $dumpvars(0, tb_arm_core);
  end

  initial begin
      $monitor("Time: %0t | Address: %h | Write Data: %h | Read Data: %h | Write Enable: %b | Read Enable: %b",
               $time, address, write_data, read_data, write_enable, read_enable);
  end

endmodule
