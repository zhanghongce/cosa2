import os
import subprocess
inst_group = ['instr_lui','instr_auipc','instr_jal','instr_jalr','instr_beq','instr_bne','instr_blt','instr_bge','instr_bltu','instr_bgeu','instr_lb','instr_lh','instr_lw','instr_lbu','instr_lhu','instr_sb',
'instr_sh','instr_sw','instr_addi','instr_slti','instr_sltiu','instr_xori','instr_ori','instr_andi','instr_slli','instr_srli','instr_srai','instr_add','instr_sub','instr_sll','instr_slt','instr_sltu','instr_xor',
'instr_srl','instr_sra','instr_or','instr_and','instr_rdcycle','instr_rdcycleh','instr_rdinstr','instr_rdinstrh','instr_getq','instr_setq','instr_retirq','instr_maskirq','instr_waitirq','instr_timer']
path = "/data/zhiyuany/cosa2/inst.smt2"
init_constraint_path= "/data/zhiyuany/cosa2/inv.smt2"
init_constraint_path_origin= "/data/zhiyuany/cosa2/inv_origin.smt2"
model = '/data/zhiyuany/EnvSynSample/ILAng/PICO/envinvsyn/design.btor'
count = 0
if(os.path.exists(path) == True):
     os.remove(path)
if(os.path.exists(init_constraint_path) == True):
     os.remove(init_constraint_path)
for i in range(len(inst_group)):
     for j in range(i+1,len(inst_group)):
          print("Now the instruction is the ",inst_group[i],inst_group[j])
          with open(path,'w') as f:
               info = "("+"define-fun"+" " + "assertion." + "0" + " " + "(" + "("  + inst_group[i]  + " " + "(_ BitVec 1)" + ")" + " " + "("  + inst_group[j] + " " + "(_ BitVec 1)" + ")" +")" + " Bool " +  "(" + "or "+"("+ "not " +inst_group[i] + ")" + " " + "("+ "not "+ inst_group[j] + ")" + ")" + ")"
               f.write(info)
          subprocess.run(["./build/pono","--vcd" , "{:s}" .format('cex.vcd'),"-e","{:s}" .format("bmc"), "--promote-inputvars" ,"--property-file", "{:s}" .format(path),"{:s}" .format(model)])
          if(os.path.exists("cex.vcd") == False):
               # assump_info = "("+"define-fun"+" " + "assertion." + "0" + " " + "(" + "("  + inst_group[i]  + " " + "(_ BitVec 1)" + ")" + " " + "("  + inst_group[j] + " " + "(_ BitVec 1)" + ")" +")" + " Bool " +  "(" + "or "+"("+ "not " +inst_group[i] + ")" + " " + "("+ "not "+ inst_group[j] + ")" + ")" + ")"
               with open(init_constraint_path,'a') as f:
                    info = "("+"define-fun"+" " + "assumption." + str(count) + " " + "(" + "("  + "RTL." + inst_group[i]  + " " + "(_ BitVec 1)" + ")" + " " + "("  +"RTL."+ inst_group[j] + " " + "(_ BitVec 1)" + ")" +")" + " Bool " +  "(" + "or "+"("+ "not " +"RTL."+inst_group[i] + ")" + " " + "("+ "not "+"RTL." +inst_group[j] + ")" + ")" + ")" +"\n"
                    f.write(info)         
                    # count = count + 1 
               with open(init_constraint_path_origin,'a') as f:
                    info = "("+"define-fun"+" " + "assumption." + str(count) + " " + "(" + "("   + inst_group[i]  + " " + "(_ BitVec 1)" + ")" + " " + "("  + inst_group[j] + " " + "(_ BitVec 1)" + ")" +")" + " Bool " +  "(" + "or "+"("+ "not " +inst_group[i] + ")" + " " + "("+ "not " +inst_group[j] + ")" + ")" + ")" +"\n"
                    f.write(info)         
                    count = count + 1 
          os.remove(path)
          if(os.path.exists("cex.vcd") == True):
               os.remove("cex.vcd")

