(* Successful unsigned upper-bound assertions used by the decoder. *)
Theory abiDecoderGuardLE
Ancestors
  abiDecoderGuards emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState words

Definition abi_decode_le_guard_def:
  abi_decode_le_guard a b =
    do oob <- emit_op GT [a;b];
       ok <- emit_op ISZERO [oob];
       emit_void ASSERT [ok]
    od
End

Theorem abi_decode_le_guard_shape:
  abi_decode_le_guard a b st = ((),st') ==> inst_extends st st'
Proof
  simp[abi_decode_le_guard_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  metis_tac[inst_extends_trans]
QED

Theorem abi_decode_le_guard_sequence:
  abi_decode_le_guard a b st = ((),st') /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  w2n va <= w2n vb /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  simp[abi_decode_le_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [a;b] st = (oob,c1)` >>
  rename1 `emit_op ISZERO [oob] c1 = (ok,c2)` >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[bool_to_word_def] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[bool_to_word_def] >> `(1w:bytes32) <> 0w` by simp[] >>
  drule_all emit_void_ASSERT_ok_full >> simp[] >> strip_tac >> gvs[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `GT`] abi_decode_pure_emit_frame)) >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ISZERO`] abi_decode_pure_emit_frame)) >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `s2` >> simp[] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_GUARD_LE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder upper-bound guard not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderGuardLE");
