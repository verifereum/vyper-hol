(* The dynamic-array decoder's emitted payload-end arithmetic and guard. *)
Theory abiDecoderDynarrayBound
Ancestors
  abiDecoderBytesBound abiDecoderGuardLE abiDecoderGuards emitHelperProps
  exprLoweringProps compileEnv emitHelper venomExecSemantics venomState words arithmetic

Theorem abi_decode_mul_sequence:
  !a b va vb st v st' s.
  emit_op MUL [a;b] st = (v,st') /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand v t = SOME (va * vb) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  rpt strip_tac >> drule_all emit_op_MUL_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `MUL`] abi_decode_pure_emit_frame)) >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >> qexists_tac `t` >> simp[]
QED

Definition abi_decode_dynarray_end_def:
  abi_decode_dynarray_end src cnt abi_sz =
    do payload_sz <- emit_op MUL [cnt; Lit (n2w abi_sz)];
       payload_plus_hdr <- emit_op ADD [payload_sz; Lit 32w];
       emit_op ADD [src; payload_plus_hdr]
    od
End

Theorem abi_decode_dynarray_end_sequence:
  abi_decode_dynarray_end src cnt abi_sz st = (end_op,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand cnt s = SOME (n2w n) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand end_op t = SOME (n2w (sb + 32 + n * abi_sz)) /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  simp[abi_decode_dynarray_end_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt; Lit (n2w abi_sz)] st = (payload,c1)` >>
  rename1 `emit_op ADD [payload; Lit 32w] c1 = (plus_hdr,c2)` >>
  `eval_operand (Lit (n2w abi_sz)) s = SOME (n2w abi_sz)` by simp[eval_operand_def] >>
  drule_all abi_decode_mul_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[word_mul_n2w] >>
  `eval_operand (Lit 32w) s1 = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand src s2 = SOME (n2w sb)` by metis_tac[] >>
  qspecl_then [`src`, `plus_hdr`, `n2w sb`, `(n2w (n * abi_sz) : bytes32) + 32w`,
    `c2`, `end_op`, `st'`, `s2`] mp_tac abi_decode_add_sequence >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 st') s2 = OK t` >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  qexists_tac `t` >>
  gvs[word_mul_n2w, word_add_n2w] >> metis_tac[]
QED

Definition abi_decode_dynarray_end_guard_def:
  abi_decode_dynarray_end_guard src cnt abi_sz hi =
    if hi = Lit 0w then return ()
    else do end_op <- abi_decode_dynarray_end src cnt abi_sz;
            abi_decode_le_guard end_op hi
         od
End

Theorem abi_decode_dynarray_end_guard_sequence:
  abi_decode_dynarray_end_guard src cnt abi_sz hi st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand cnt s = SOME (n2w n) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     sb + 32 + n * abi_sz <= h /\ h < dimword (:256)) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  Cases_on `hi = Lit 0w`
  >- (simp[abi_decode_dynarray_end_guard_def, comp_return_def] >> strip_tac >>
      gvs[] >> qexists_tac `s` >> simp[emitted_insts_def, run_inst_seq_def,
        inst_extends_refl]) >>
  simp[abi_decode_dynarray_end_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_dynarray_end src cnt abi_sz st = (end_op,c1)` >>
  rename1 `eval_operand hi s = SOME (n2w h)` >>
  drule_all abi_decode_dynarray_end_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand hi s1 = SOME (n2w h)` by metis_tac[] >>
  `sb + 32 + n * abi_sz < dimword (:256)` by decide_tac >>
  `w2n (n2w (sb + 32 + n * abi_sz) : bytes32) <= w2n (n2w h : bytes32)` by
    simp[w2n_n2w] >>
  drule_all abi_decode_le_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  drule abi_decode_le_guard_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >> qexists_tac `t` >>
  gvs[] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_DYNARRAY_BOUND_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI dynamic-array endpoint not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderDynarrayBound");
