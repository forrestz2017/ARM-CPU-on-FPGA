
//=======================================================
//  This code is generated by Terasic System Builder
//=======================================================

// Forrest Zhang, 8/5/2024: modified to support system mode selection

module DE10_LITE_EEPROM(

	//////////// CLOCK //////////
	input 		          		ADC_CLK_10,
	input 		          		MAX10_CLK1_50,

	//////////// SEG7 //////////
	output		     [7:0]		HEX0,
	output		     [7:0]		HEX1,
	output		     [7:0]		HEX2,
	output		     [7:0]		HEX3,
	output		     [7:0]		HEX4,
	output		     [7:0]		HEX5,

	//////////// KEY //////////
	input 		     [1:0]		KEY,

	//////////// LED //////////
	output		     [9:0]		LEDR,

	//////////// SW //////////
	input 		     [9:0]		SW,

	//////////// GPIO, GPIO connect to GPIO Default //////////
	inout 		    [35:0]		GPIO

	input  [1:0] mode // new input for mode selection - Forrest Zhang, 8/5/2024
);


//=======================================================
//  REG/WIRE declarations
//=======================================================


	logic simClk; // simulation clock
	logic [2:0] state, next_state; // state control variables 
	reg	 CE, OE, WE; // EEPROM control signals
	logic [7:0] WriteData; // data bus output
	logic [14:0] DataAdr, RAMDataAdr; // EEPROM address, A0-A14, and memfile address variables
	reg	Dclk;  // state control clock
	reg	[25:0] SCLK; // intermediate clock variable for clock speed control
	logic [31:0] RAM[127:0]; // array variable for holding instructions to be transferred to EEPROMs
	logic [1:0] byte_address; // variable for selecting byte 0-3 of full word
	logic [3:0] long_state, signals;
	
//=======================================================
//  Structural coding
//=======================================================

	//*** Need to verify correct pins per schematic, JO 3/15/24
	
	assign GPIO[7:0] = WE? 8'bZ:WriteData[7:0]; // data bus input/output D0-D7
	assign GPIO[22:8] = DataAdr[14:0];	// Address bus output A0-A14
	assign GPIO[27] = OE; // EEPROM Output Enable signal confirm OE=RD
	assign GPIO[29] = CE; // EEPROM Chip Enable signal (CE=ROM)
	assign GPIO[30] = WE? 1'bZ:1'b0; // active low EEPROM Write Enable signal w/ pull-up, (off=high impedance, on=low) 
	assign GPIO[35] = Dclk; // State control clock output
	assign long_state = {1'b0, state};
	assign signals = {1'b0, OE, CE, WE};
	
	initial begin		
		simClk <= 0;
		DataAdr <= 15'b0; // starting EEPROM address of 0x0000
		RAMDataAdr <= 15'b0; // starting at array address zero in SDRAM variable
		$readmemh("memfile2.dat", RAM); // *** load ARM program file to SDRAM variable
		WriteData = RAM[RAMDataAdr][7:0]; // load first instruction from SDRAM to data bus output
		SCLK = 50000; // startup delay to give time for EEPROMs to power up
		Dclk = 0;
		byte_address = 2'b00;
	end
	
	always begin  // simulation clock for testing if needed 
		#10; // 100ns per half period = 5MHz
		simClk = !simClk;
	end
	
	always@(posedge MAX10_CLK1_50) begin  // *change MAX10_CLK1_50 to simClk for simulation
	SCLK = SCLK - 1;		 // used to slow clock speed for write cycles
		if (SCLK==0) begin // EEPROMs require up to 5ms between writes
			SCLK <= 25000000;  // 
			Dclk <= ~Dclk;  //
		end
	end
	
		
    always @(posedge Dclk) begin // state control for write cycle operations
                                          // Write cycles run from state 000 (0) to state 101 (5)
        case(state)             // State 110 (6) is idle, address and data values update during state 111 (7)
            3'b000: begin
                next_state = next_state + 1;
                LEDR = 10'b0000000001; // Example: LEDR[0] is '1', others are '0'
                case(byte_address)  // load SDRAM stored value to data bus
                    2'b00: begin
                        WriteData = RAM[RAMDataAdr][7:0];
                        end
                    2'b01: begin
                        WriteData = RAM[RAMDataAdr][15:8];
                        end
                    2'b10: begin
                        WriteData = RAM[RAMDataAdr][23:16];
                        end
                    2'b11: begin
                        WriteData = RAM[RAMDataAdr][31:24];
                        end
                endcase
            
                end
        
            3'b001: begin
                next_state = next_state + 1;
                LEDR = 10'b0000000010; // Example: LEDR[1] is '1', others are '0'
                end
            3'b010: begin
                next_state = next_state + 1;
                LEDR = 10'b0000000100; // Example: LEDR[2] is '1', others are '0'
                end
            3'b011: begin
                next_state = next_state + 1;
                LEDR = 10'b0000001000; // Example: LEDR[3] is '1', others are '0'
                end
            3'b100: begin
                next_state = next_state + 1;
                LEDR = 10'b0000010000; // Example: LEDR[4] is '1', others are '0'
                end
            3'b101: begin
                next_state = next_state + 1;
                LEDR = 10'b0000100000; // Example: LEDR[5] is '1', others are '0'
                end
            3'b110: begin
                next_state = next_state + 1;
                LEDR = 10'b0001000000; // Example: LEDR[6] is '1', others are '0'
                end
            3'b111: begin
                next_state = 0;
                LEDR = 10'b0010000000; // Example: LEDR[6] is '1', others are '0'

                //----- Begin added support for mode selection ----- (Forrest Zhang)
                if (mode == 2'b00) begin // Mode 0: Running system simulation to display functionality
                    if (RAMDataAdr < 128) begin // copies up to the given number of instructions
                        if (byte_address > 2) begin // has byte 3 been written?
                            DataAdr = DataAdr + 1; // increment EEPROM address by 1 byte each write cycle
                            RAMDataAdr = RAMDataAdr + 1; // increment SDRAM address by 1 after all 4 bytes written
                            byte_address = 0; // reset byte address to zero after all 4 bytes written
                        end else begin
                            DataAdr = DataAdr + 1; // increment EEPROM address by 1 byte each write cycle
                            byte_address = byte_address + 1; // increment byte address
                        end
                    end
                end else if (mode == 2'b01) begin // Mode 1: Allow user to run their own source code
                    // Implementation for user to run their own source code
                    if (RAMDataAdr < 128) begin // copies up to the given number of instructions
                        if (byte_address > 2) begin // has byte 3 been written?
                            DataAdr = DataAdr + 1; // increment EEPROM address by 1 byte each write cycle
                            RAMDataAdr = RAMDataAdr + 1; // increment SDRAM address by 1 after all 4 bytes written
                            byte_address = 0; // reset byte address to zero after all 4 bytes written
                        end else begin
                            DataAdr = DataAdr + 1; // increment EEPROM address by 1 byte each write cycle
                            byte_address = byte_address + 1; // increment byte address
                        end
                    end
                end
                //----- End mode selection extension ----- (Forrest Zhang)

            end
            
            default: next_state = 0;
        endcase
        state = next_state;
    end

	sub1 subR(state,Dclk,CE,OE,WE,WriteData,DataAdr); // call module for EEPROM write cycle control
	
	seg7 D5(long_state, HEX5); // current state value
	seg7 D4(signals, HEX4);	// CE,OE,WE
	seg7 D3(DataAdr[7:4], HEX3);	// A7-A4
	seg7 D2(DataAdr[3:0], HEX2);	// A3-A0
	seg7 D1(WriteData[7:4], HEX1);	// D7-D4
	seg7 D0(WriteData[3:0], HEX0);	// D3-D0
	
endmodule


module sub1(input [2:0] state, input clk, output CE, output OE, output WE,
				input writeData, input dataAdr);

	reg chip_enable, output_enable, write_enable, write_active;
	initial write_active = 1; // set to 1 for writes (normal operation)
	
	always @(posedge clk) begin	 
		if (state < 6) begin
			case(state)
				3'b000: begin				// initialize all signals to high (off) at start
						chip_enable = 1;  // of write cycle
						output_enable = 1;
						write_enable = 1;
					end
				3'b001: begin
						chip_enable = 0; // set CE to low (on)
					end
				3'b010: begin
						if (write_active==1) write_enable = 0; // set WE to low (on) to activate EEPROM write
						else output_enable = 0;	// *only used if changing code to perform EEPROM reads
					end
				3'b011: begin
						// wait step, to keep CE and WE on for one clock cycle
					end
				3'b100: begin
						if (write_active==1) write_enable = 1; // set WE to high, EEPROM stores data at this point
						else output_enable = 1; // *only applicable for reads
					end
				3'b101: begin
						chip_enable = 1; // set CE to high (off)
						output_enable = 1; // redundant step to ensure output is still off
					end
			endcase
		end
	end
	assign CE = chip_enable;   // module outputs
	assign OE = output_enable; //
	assign WE = write_enable;  //
endmodule



//=======================================================
//  HEX Displays
//=======================================================

module seg7(input [3:0] hex, output [7:0] segment);
reg [7:0] leds;
always@(*) begin
case(hex)
	0: leds =  8'b00111111;	// 0 image
	1: leds =  8'b00000110;	// 1 image
	2: leds =  8'b01011011;	// 2 image
	3: leds =  8'b01001111;	// 3 image
	4: leds =  8'b01100110;	// 4 image
	5: leds =  8'b01101101;	// 5 image
	6: leds =  8'b01111101;	// 6 image
	7: leds =  8'b00000111;	// 7 image
	8: leds =  8'b01111111;	// 8 image
	9: leds =  8'b01101111;	// 9 image
	10: leds = 8'b01110111;	// A image
	11: leds = 8'b01111100;	// b image
	12: leds = 8'b00111001;	// C image
	13: leds = 8'b01011110;	// d image
	14: leds = 8'b01111001;	// E image
	15: leds = 8'b01110001;	// F image
	endcase
	end
	assign segment = ~leds;		// invert and copy to outputs
endmodule		// end of seg7