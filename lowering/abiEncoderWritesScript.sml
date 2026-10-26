(* Single memory writes preserve enclosing variable freshness on re-entry. *)
Theory abiEncoderWrites
Ancestors
  abiDecoderContract abiDecoderDynamicLoopSetup emitHelperProps exprLoweringProps
  emitHelper compileEnv venomState venomExecSemantics venomInst words list

Theorem abi_encoder_write_observations[simp]:
  (mstore p w s).vs_call_ctx = s.vs_call_ctx /\
  (mstore p w s).vs_data_section = s.vs_data_section /\
  (mstore p w s).vs_allocas = s.vs_allocas /\
  (mstore p w s).vs_alloca_next = s.vs_alloca_next /\
  (mstore p w s).vs_halted = s.vs_halted /\
  (mcopy db sb cnt s).vs_call_ctx = s.vs_call_ctx /\
  (mcopy db sb cnt s).vs_data_section = s.vs_data_section /\
  (mcopy db sb cnt s).vs_allocas = s.vs_allocas /\
  (mcopy db sb cnt s).vs_alloca_next = s.vs_alloca_next /\
  (mcopy db sb cnt s).vs_halted = s.vs_halted
Proof
  simp[mcopy_def, mstore_def, write_memory_with_expansion_def, LET_THM]
QED

Theorem abi_encoder_emit_store:
  emit_void MSTORE [ptr_op;value_op] st = ((),st') /\
  eval_operand ptr_op s = SOME (n2w p) /\ eval_operand value_op s = SOME w /\
  p < dimword (:256) /\ fresh_vars_wrt limit_st s ==>
  run_inst_seq (emitted_insts st st') s = OK (mstore p w s) /\
  fresh_vars_wrt limit_st (mstore p w s) /\ inst_extends st st'
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  asm_simp_tac (srw_ss()) [run_inst_seq_def, Once step_inst_base_def,
    exec_write2_def, mk_inst_def, w2n_n2w] >>
  fs[fresh_vars_wrt_def, lookup_var_def, mstore_def]
QED

Theorem abi_encoder_emit_copy:
  emit_void MCOPY [dst;src;len] st = ((),st') /\
  eval_operand dst s = SOME (n2w db) /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand len s = SOME (n2w cnt) /\
  db < dimword (:256) /\ sb < dimword (:256) /\ cnt < dimword (:256) /\
  fresh_vars_wrt limit_st s ==>
  run_inst_seq (emitted_insts st st') s = OK (mcopy db sb cnt s) /\
  fresh_vars_wrt limit_st (mcopy db sb cnt s) /\ inst_extends st st'
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  asm_simp_tac (srw_ss()) [run_inst_seq_def, Once step_inst_base_def, mk_inst_def, w2n_n2w] >>
  fs[fresh_vars_wrt_def, lookup_var_def, mcopy_def, write_memory_with_expansion_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_WRITES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder writes not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderWrites");
