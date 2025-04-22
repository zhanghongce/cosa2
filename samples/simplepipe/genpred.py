tmpl = """
(define-fun |predicate.{predid}| ((|dut.id_ex_operand1| (_ BitVec 8)) (|dut.id_ex_operand2| (_ BitVec 8)) {arg}) Bool (= (bvadd |dut.id_ex_operand1| |dut.id_ex_operand2|)
							(bvadd {op1} {op2}))

)
"""

operands = [
"|dut.ex_wb_val|", 
"|dut.ex_alu_result|", 
"|dut.registers[0]|",
"|dut.registers[1]|",
"|dut.registers[2]|", 
"|dut.registers[3]|",
"|dut.id_operand1|",
"|dut.id_operand2|"
]

arg = ' '.join( ["(" + op + " (_ BitVec 8))" for op in operands] )
predid = 0
fout = open('predicates.smt2','w')
for op1 in operands:
  for op2 in operands:
    if op1 == op2 and 'registers' not in op1:
      continue
    fout.write(tmpl.format(predid=predid,op1=op1,op2=op2,arg=arg))
    predid += 1
  
fout.close()
    
