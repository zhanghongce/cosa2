
(define-fun |predicate.0| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.ex_wb_val| |dut.ex_alu_result|))

)

(define-fun |predicate.1| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.ex_wb_val| |dut.registers[0]|))

)

(define-fun |predicate.2| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.ex_wb_val| |dut.registers[1]|))

)

(define-fun |predicate.3| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.ex_wb_val| |dut.registers[2]|))

)

(define-fun |predicate.4| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.ex_wb_val| |dut.registers[3]|))

)

(define-fun |predicate.5| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.ex_wb_val| |dut.id_operand1|))

)

(define-fun |predicate.6| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.ex_wb_val| |dut.id_operand2|))

)

(define-fun |predicate.7| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.ex_alu_result| |dut.ex_wb_val|))

)

(define-fun |predicate.8| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.ex_alu_result| |dut.registers[0]|))

)

(define-fun |predicate.9| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.ex_alu_result| |dut.registers[1]|))

)

(define-fun |predicate.10| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.ex_alu_result| |dut.registers[2]|))

)

(define-fun |predicate.11| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.ex_alu_result| |dut.registers[3]|))

)

(define-fun |predicate.12| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.ex_alu_result| |dut.id_operand1|))

)

(define-fun |predicate.13| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.ex_alu_result| |dut.id_operand2|))

)

(define-fun |predicate.14| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[0]| |dut.ex_wb_val|))

)

(define-fun |predicate.15| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[0]| |dut.ex_alu_result|))

)

(define-fun |predicate.16| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[0]| |dut.registers[0]|))

)

(define-fun |predicate.17| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[0]| |dut.registers[1]|))

)

(define-fun |predicate.18| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[0]| |dut.registers[2]|))

)

(define-fun |predicate.19| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[0]| |dut.registers[3]|))

)

(define-fun |predicate.20| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[0]| |dut.id_operand1|))

)

(define-fun |predicate.21| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[0]| |dut.id_operand2|))

)

(define-fun |predicate.22| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[1]| |dut.ex_wb_val|))

)

(define-fun |predicate.23| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[1]| |dut.ex_alu_result|))

)

(define-fun |predicate.24| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[1]| |dut.registers[0]|))

)

(define-fun |predicate.25| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[1]| |dut.registers[1]|))

)

(define-fun |predicate.26| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[1]| |dut.registers[2]|))

)

(define-fun |predicate.27| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[1]| |dut.registers[3]|))

)

(define-fun |predicate.28| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[1]| |dut.id_operand1|))

)

(define-fun |predicate.29| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[1]| |dut.id_operand2|))

)

(define-fun |predicate.30| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[2]| |dut.ex_wb_val|))

)

(define-fun |predicate.31| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[2]| |dut.ex_alu_result|))

)

(define-fun |predicate.32| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[2]| |dut.registers[0]|))

)

(define-fun |predicate.33| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[2]| |dut.registers[1]|))

)

(define-fun |predicate.34| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[2]| |dut.registers[2]|))

)

(define-fun |predicate.35| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[2]| |dut.registers[3]|))

)

(define-fun |predicate.36| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[2]| |dut.id_operand1|))

)

(define-fun |predicate.37| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[2]| |dut.id_operand2|))

)

(define-fun |predicate.38| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[3]| |dut.ex_wb_val|))

)

(define-fun |predicate.39| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[3]| |dut.ex_alu_result|))

)

(define-fun |predicate.40| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[3]| |dut.registers[0]|))

)

(define-fun |predicate.41| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[3]| |dut.registers[1]|))

)

(define-fun |predicate.42| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[3]| |dut.registers[2]|))

)

(define-fun |predicate.43| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[3]| |dut.registers[3]|))

)

(define-fun |predicate.44| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[3]| |dut.id_operand1|))

)

(define-fun |predicate.45| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.registers[3]| |dut.id_operand2|))

)

(define-fun |predicate.46| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.id_operand1| |dut.ex_wb_val|))

)

(define-fun |predicate.47| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.id_operand1| |dut.ex_alu_result|))

)

(define-fun |predicate.48| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.id_operand1| |dut.registers[0]|))

)

(define-fun |predicate.49| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.id_operand1| |dut.registers[1]|))

)

(define-fun |predicate.50| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.id_operand1| |dut.registers[2]|))

)

(define-fun |predicate.51| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.id_operand1| |dut.registers[3]|))

)

(define-fun |predicate.52| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.id_operand1| |dut.id_operand2|))

)

(define-fun |predicate.53| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.id_operand2| |dut.ex_wb_val|))

)

(define-fun |predicate.54| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.id_operand2| |dut.ex_alu_result|))

)

(define-fun |predicate.55| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.id_operand2| |dut.registers[0]|))

)

(define-fun |predicate.56| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.id_operand2| |dut.registers[1]|))

)

(define-fun |predicate.57| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.id_operand2| |dut.registers[2]|))

)

(define-fun |predicate.58| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.id_operand2| |dut.registers[3]|))

)

(define-fun |predicate.59| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) (|dut.ex_wb_val| (_ BitVec 8)) (|dut.ex_alu_result| (_ BitVec 8)) (|dut.registers[0]| (_ BitVec 8)) (|dut.registers[1]| (_ BitVec 8)) (|dut.registers[2]| (_ BitVec 8)) (|dut.registers[3]| (_ BitVec 8)) (|dut.id_operand1| (_ BitVec 8)) (|dut.id_operand2| (_ BitVec 8))) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd |dut.id_operand2| |dut.id_operand1|))

)
