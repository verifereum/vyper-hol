Theory abiDecoderGuard
Ancestors
  abiDecoderRange abiDecoderGuards emitHelperProps exprLoweringProps compileEnv emitHelper venomExecSemantics
  venomState words

(* ===== Lower Bound ===== *)

(* Successful unsigned no-wrap assertions used by bounded-memory decoding. *)

Definition abi_decode_ge_guard_def:
  abi_decode_ge_guard a b =
    do underflow <- emit_op LT [a;b];
       ok <- emit_op ISZERO [underflow];
       emit_void ASSERT [ok]
    od
End

Theorem abi_decode_ge_guard_shape:
  abi_decode_ge_guard a b st = ((),st') ==> inst_extends st st'
Proof
  simp[abi_decode_ge_guard_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  metis_tac[inst_extends_trans]
QED

Theorem abi_decode_ge_guard_sequence:
  abi_decode_ge_guard a b st = ((),st') /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  w2n vb <= w2n va /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  simp[abi_decode_ge_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op LT [a;b] st = (underflow,c1)` >>
  rename1 `emit_op ISZERO [underflow] c1 = (ok,c2)` >>
  drule_all emit_op_LT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[bool_to_word_def] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[bool_to_word_def] >> `(1w:bytes32) <> 0w` by simp[] >>
  drule_all emit_void_ASSERT_ok_full >> simp[] >> strip_tac >> gvs[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `LT`] abi_decode_pure_emit_frame)) >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ISZERO`] abi_decode_pure_emit_frame)) >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `s2` >> simp[] >> metis_tac[]
QED

(* ===== Upper Bound ===== *)

(* Successful unsigned upper-bound assertions used by the decoder. *)

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

Theorem abi_decode_ge_guard_revert:
  abi_decode_ge_guard a b st = ((),st') /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  w2n va < w2n vb /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[abi_decode_ge_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op LT [a;b] st = (underflow,c1)` >>
  rename1 `emit_op ISZERO [underflow] c1 = (ok,c2)` >>
  drule_all emit_op_LT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[bool_to_word_def] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c1 st'` by metis_tac[inst_extends_trans] >>
  drule_all (Q.SPECL [`c1`, `c2`, `st'`]
    run_inst_seq_emit_extend) >> simp[] >> strip_tac >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts c1 st') s1` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  simp[]
QED

Theorem abi_decode_le_guard_revert:
  abi_decode_le_guard a b st = ((),st') /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  w2n vb < w2n va /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[abi_decode_le_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [a;b] st = (oob,c1)` >>
  rename1 `emit_op ISZERO [oob] c1 = (ok,c2)` >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[bool_to_word_def] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c1 st'` by metis_tac[inst_extends_trans] >>
  drule_all (Q.SPECL [`c1`, `c2`, `st'`]
    run_inst_seq_emit_extend) >> simp[] >> strip_tac >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts c1 st') s1` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  simp[]
QED

(* Exact-size branch of lower_abi_decode, independently of later allocation. *)
Theorem abi_decode_exact_guard_revert:
  (do valid <- emit_op EQ [a;b]; emit_void ASSERT [valid] od) st = ((),st') /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  va <> vb /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op EQ [a;b] st = (valid,c1)` >>
  drule_all emit_op_EQ_correct >> strip_tac >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all (Q.SPECL [`st`, `c1`, `st'`] run_inst_seq_emit_extend) >>
  simp[] >> strip_tac >> goal_assum (drule_at Any)
QED

(* The non-exact size branch evaluates both bounds before the assertion. *)
Theorem abi_decode_interval_guard_revert:
  (do lt_min <- emit_op LT [a;lo];
      ge_min <- emit_op ISZERO [lt_min];
      gt_max <- emit_op GT [a;hi];
      le_max <- emit_op ISZERO [gt_max];
      valid <- emit_op AND [ge_min;le_max];
      emit_void ASSERT [valid] od) st = ((),st') /\
  eval_operand a s = SOME va /\ eval_operand lo s = SOME vlo /\
  eval_operand hi s = SOME vhi /\
  (w2n va < w2n vlo \/ w2n vhi < w2n va) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op LT [a;lo] st = (lt_min,c1)` >>
  rename1 `emit_op ISZERO [lt_min] c1 = (ge_min,c2)` >>
  rename1 `emit_op GT [a;hi] c2 = (gt_max,c3)` >>
  rename1 `emit_op ISZERO [gt_max] c3 = (le_max,c4)` >>
  rename1 `emit_op AND [ge_min;le_max] c4 = (valid,c5)` >>
  drule_all emit_op_LT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand a s2 = SOME va /\ eval_operand hi s2 = SOME vhi` by metis_tac[] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 c4) s3 = OK s4` >>
  `eval_operand ge_min s4 =
    SOME (bool_to_word (bool_to_word (w2n va < w2n vlo) = 0w))` by metis_tac[] >>
  drule_all emit_op_AND_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c4 c5) s4 = OK s5` >>
  gvs[bool_to_word_def, WORD_AND_CLAUSES] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c4 st'` by metis_tac[inst_extends_trans] >>
  `inst_extends c3 st'` by metis_tac[inst_extends_trans] >>
  `inst_extends c2 st'` by metis_tac[inst_extends_trans] >>
  `inst_extends c1 st'` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts c1 st') s1` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  `run_inst_seq (emitted_insts c1 st') s1 =
   run_inst_seq (emitted_insts c2 st') s2` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  `run_inst_seq (emitted_insts c2 st') s2 =
   run_inst_seq (emitted_insts c3 st') s3` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  `run_inst_seq (emitted_insts c3 st') s3 =
   run_inst_seq (emitted_insts c4 st') s4` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  `run_inst_seq (emitted_insts c4 st') s4 =
   run_inst_seq (emitted_insts c5 st') s5` by
    (irule run_inst_seq_emit_extend >> simp[]) >> simp[]
QED

(* Rejection counterpart of the bounded decoder's range sequence. *)
Theorem abi_decode_range_check_revert:
  compile_abi_decode_range_check src e hi st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand e s = SOME q /\
  eval_operand hi s = SOME h /\
  (w2n q < w2n p \/ w2n h < w2n q) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[abiEncoderTheory.compile_abi_decode_range_check_def] >>
  metis_tac[abi_decode_interval_guard_revert]
QED
