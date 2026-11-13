(* Typed rounding suffix certificates, before expression-post assembly. *)
Theory bodyPtrWordBuiltinsRoundingCases
Ancestors bodyPtrWordBuiltinsRounding bodyPtrWordBuiltinsRoundingPost
  bodyPtrWordBuiltinsRoundingSource bodyPtrWordBuiltinsIntervalGhost
  exprSimWordBuiltins exprSimWordArgs fragGasFresh exprLoweringProps
  bodyPtrDefs ptrDiscipline compileEnv fragExec freshWrites
  venomState venomExecSemantics list finite_map valueEncoding integer_word
  fragGasPathPtr gasSummary fragGasSeqAbort varsExt

Theorem word_round_typed_outcome:
  (if up then compile_ceil else compile_floor) v 10000000000 sa = (op,sb) /\
  within_int_bound (Signed 168) i /\
  (!z. v = Var z ==> not_fresh_at sa z) /\ eval_operand v s = SOME (i2w i) /\
  op_prov G v = NONE /\ op_taint tn v = {} /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sc /\ sc.cs_next_var <= sa.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (\ee. (builtin_result cx ee.accounts ann (if up then Ceil else Floor) ts [DecimalV i],ee))
    (es,s,G,tn)
    (\r ee G' tn' u.
      r = INL (IntV ((if up then i + (10000000000-1) else i) / 10000000000)) /\
      ee = es with gas_obs := [] /\ stmt_state_rel ctx func cenv cx es u /\
      eval_operand op u = SOME (i2w ((if up then i + (10000000000-1) else i) / 10000000000)) /\
      (!z a. not_fresh_at sa z /\ lookup_var z s = SOME a ==> lookup_var z u = SOME a) /\
      (!aid bl. FLOOKUP s.vs_allocas aid = SOME bl ==> FLOOKUP u.vs_allocas aid = SOME bl) /\
      u.vs_memory = s.vs_memory /\ ~u.vs_halted /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx es G' tn' u /\ ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\
      op_taint tn' op = {} /\ op_prov G' op = NONE) R
Proof
  strip_tac >>
  `straight_fresh ((if up then compile_ceil else compile_floor) v 10000000000)` by
    (Cases_on `up` >> simp[straight_fresh_ceil, straight_fresh_floor]) >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand v (drop_fresh sa s) = SOME (i2w i)` by simp[eval_operand_drop_fresh] >>
  drule_all word_round_clean_run >> strip_tac >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all word_round_actual_post >> strip_tac >>
  `allocas_from 0 s` by simp[allocas_from_def] >>
  drule_all word_round_counted_normal_post >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule word_round_cursor_length >> strip_tac >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def, gas_explicit_def, word_round_source] >>
  qexistsl_tac [`INL (IntV ((if up then i + (10000000000-1) else i) / 10000000000))`,
    `es`, `H`, `th`, `OK (t' with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  gvs[word_interval_ghost_inv_index, word_round_decimal_result]
QED
