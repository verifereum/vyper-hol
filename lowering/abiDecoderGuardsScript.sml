(* Shared successful count clamps for bytestring and dynamic-array decoding. *)
Theory abiDecoderGuards
Ancestors
  abiDecoderContract emitHelperProps exprLoweringProps abiEncoder emitHelper
  compileEnv valueEncoding venomExecSemantics venomExecProofs venomInst venomState
  words arithmetic list rich_list

Definition abi_decode_count_guard_def:
  abi_decode_count_guard opc src limit =
    do count_op <- emit_op opc [src];
       too_many <- emit_op GT [count_op; Lit (n2w limit)];
       ok <- emit_op ISZERO [too_many];
       emit_void ASSERT [ok];
       return count_op
    od
End

Theorem abi_decode_pure_emit_frame:
  emit_op opc ops st = (v,st') /\
  (opc = ADD \/ opc = MUL \/ opc = GT \/ opc = LT \/ opc = ISZERO) /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def] >>
  gvs[Once step_inst_base_def, mk_inst_def] >>
  gvs[exec_pure2_def, exec_pure1_def, AllCaseEqs(), update_var_def]
QED

Theorem abi_decode_count_guard_shape:
  abi_decode_count_guard opc src limit st = (count_op,st') ==>
  inst_extends st st'
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  metis_tac[inst_extends_trans]
QED

Theorem abi_decode_sequence_chain:
  inst_extends st st1 /\ inst_extends st1 st2 /\
  run_inst_seq (emitted_insts st st1) s = OK s1 /\
  run_inst_seq (emitted_insts st1 st2) s1 = OK s2 ==>
  run_inst_seq (emitted_insts st st2) s = OK s2 /\ inst_extends st st2
Proof
  strip_tac >> conj_tac
  >- (irule run_inst_seq_compose_ok >> qexistsl_tac [`s1`, `st1`] >> simp[]) >>
  metis_tac[inst_extends_trans]
QED

Theorem abi_decode_count_guard_sequence:
  abi_decode_count_guard opc src limit st = (count_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME p /\
  abi_decode_load opc p s = n2w cnt /\
  cnt <= limit /\ limit < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand count_op t = SOME (n2w cnt) /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [count_op; Lit (n2w limit)] c1 = (too_many,c2)` >>
  rename1 `emit_op ISZERO [too_many] c2 = (ok,c3)` >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand (Lit (n2w limit)) s1 = SOME (n2w limit)` by simp[eval_operand_def] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `cnt < dimword (:256)` by decide_tac >>
  gvs[w2n_n2w, bool_to_word_def] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  gvs[bool_to_word_def] >>
  `(1w:bytes32) <> 0w` by simp[] >>
  drule_all emit_void_ASSERT_ok_full >> simp[] >> strip_tac >> gvs[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `GT`] abi_decode_pure_emit_frame)) >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ISZERO`] abi_decode_pure_emit_frame)) >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `s3` >> simp[] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_GUARDS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder guard not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderGuards");
