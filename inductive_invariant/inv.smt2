(define-fun assumption.0 ((RTL.is_alu_reg_imm (_ BitVec 1)) (RTL.instr_jal (_ BitVec 1)) (RTL.mem_instr (_ BitVec 1)) (RTL.mem_state (_ BitVec 2)) (RTL.cpu_state (_ BitVec 8)) (RTL.mem_do_rdata (_ BitVec 1)) (RTL.decoder_trigger_q (_ BitVec 1)) (RTL.compressed_instr (_ BitVec 1)) (RTL.rvfi_trap (_ BitVec 1)) (RTL.mem_do_wdata (_ BitVec 1)) (RTL.mem_do_rinst (_ BitVec 1)) (RTL.instr_retirq (_ BitVec 1)) (RTL.mem_valid (_ BitVec 1)) (RTL.latched_branch (_ BitVec 1)) (RTL.latched_store (_ BitVec 1))) Bool (and (and true (or (or (not (= ((_ extract 0 0) RTL.mem_state) (_ bv1 1))) (not (= ((_ extract 1 1) RTL.mem_state) (_ bv1 1)))) (not (= ((_ extract 0 0) RTL.mem_valid) (_ bv1 1))))) (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= RTL.mem_instr (_ bv1 1)) (= RTL.cpu_state (_ bv64 8))) (= RTL.is_alu_reg_imm (_ bv1 1))) (= RTL.instr_jal (_ bv0 1))) (= RTL.latched_store (_ bv0 1))) (= RTL.latched_branch (_ bv0 1))) (= RTL.mem_valid (_ bv1 1))) (= RTL.instr_retirq (_ bv0 1))) (= RTL.mem_state (_ bv3 2))) (= RTL.mem_do_rinst (_ bv1 1))) (= RTL.mem_do_wdata (_ bv0 1))) (= RTL.rvfi_trap (_ bv0 1))) (= RTL.compressed_instr (_ bv0 1))) (= RTL.decoder_trigger_q (_ bv0 1))) (= RTL.mem_do_rdata (_ bv0 1))))))
(define-fun assumption.1 ((RTL.decoder_trigger_q (_ BitVec 1)) (RTL.instr_jal (_ BitVec 1)) (RTL.mem_state (_ BitVec 2)) (RTL.trap (_ BitVec 1)) (RTL.do_waitirq (_ BitVec 1)) (RTL.mem_do_rinst (_ BitVec 1)) (RTL.decoded_rd (_ BitVec 5)) (RTL.mem_instr (_ BitVec 1)) (RTL.cpu_state (_ BitVec 8)) (RTL.mem_do_wdata (_ BitVec 1)) (RTL.instr_retirq (_ BitVec 1)) (RTL.mem_valid (_ BitVec 1)) (RTL.latched_branch (_ BitVec 1)) (RTL.latched_rd (_ BitVec 5)) (RTL.mem_do_rdata (_ BitVec 1)) (RTL.latched_store (_ BitVec 1)) (RTL.mem_wordsize (_ BitVec 2)) (RTL.compressed_instr (_ BitVec 1))) Bool (and true (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= RTL.mem_do_rinst (_ bv1 1)) (= RTL.decoded_rd (_ bv0 5))) (= RTL.mem_instr (_ bv1 1))) (= RTL.cpu_state (_ bv64 8))) (= RTL.mem_do_wdata (_ bv0 1))) (= RTL.decoder_trigger_q (_ bv0 1))) (= RTL.instr_jal (_ bv0 1))) (= RTL.mem_state (_ bv0 2))) (= RTL.mem_valid (_ bv1 1))) (= RTL.trap (_ bv0 1))) (= RTL.do_waitirq (_ bv0 1))) (= RTL.compressed_instr (_ bv0 1))) (= RTL.mem_wordsize (_ bv0 2))) (= RTL.latched_store (_ bv0 1))) (= RTL.mem_do_rdata (_ bv1 1))) (= RTL.latched_rd (_ bv31 5))) (= RTL.latched_branch (_ bv0 1))) (= RTL.instr_retirq (_ bv0 1))))))
