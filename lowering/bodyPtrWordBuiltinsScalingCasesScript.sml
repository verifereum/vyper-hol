(* Typed unsigned-scaling suffixes, including the identity multiplier. *)
Theory bodyPtrWordBuiltinsScalingCases
Ancestors bodyPtrWordBuiltinsScaling bodyPtrWordBuiltinsScalingPost
  bodyPtrWordBuiltinsScalingSource bodyPtrWordBuiltinsIntervalGhost
  exprSimWordBuiltins exprSimWordArgs fragGasFresh exprLoweringProps
  bodyPtrDefs ptrDiscipline compileEnv fragExec freshWrites
  venomState venomExecSemantics list finite_map valueEncoding integer_word words
  fragGasPathPtr gasSummary fragGasSeqAbort varsExt exprSimDefs

Theorem word_scale_typed_normal_outcome:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  w2n w * denomination_multiplier dn < dimword (:256) /\
  (!z. v = Var z ==> not_fresh_at sa z) /\ eval_operand v s = SOME w /\
  op_prov G v = NONE /\ op_taint tn v = {} /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sc /\ sc.cs_next_var <= sa.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (\ee. (builtin_result cx ee.accounts ann (AsWeiValue dn) ts [IntV (&w2n w)],ee))
    (es,s,G,tn)
    (\r ee G' tn' u.
      r = INL (IntV (&(w2n w * denomination_multiplier dn))) /\
      ee = es with gas_obs := [] /\ stmt_state_rel ctx func cenv cx es u /\
      eval_operand op u = SOME (w * n2w (denomination_multiplier dn)) /\
      (!z a. not_fresh_at sa z /\ lookup_var z s = SOME a ==> lookup_var z u = SOME a) /\
      (!aid bl. FLOOKUP s.vs_allocas aid = SOME bl ==> FLOOKUP u.vs_allocas aid = SOME bl) /\
      u.vs_memory = s.vs_memory /\ ~u.vs_halted /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx es G' tn' u /\ ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\
      op_taint tn' op = {} /\ op_prov G' op = NONE) R
Proof
  strip_tac >>
  `0 < denomination_multiplier dn /\ denomination_multiplier dn < dimword (:256)` by
    (qspec_then `dn` mp_tac denomination_multiplier_bounds >> simp[dimword_def]) >>
  `straight_fresh (compile_as_wei_value_int v (denomination_multiplier dn) F)` by
    simp[straight_fresh_as_wei_value_int] >>
  `eval_operand v (drop_fresh sa s) = SOME w` by simp[eval_operand_drop_fresh] >>
  drule_all compile_as_wei_value_int_run >> strip_tac >>
  `?t0. run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t0 /\
        eval_operand op t0 = SOME (w * n2w (denomination_multiplier dn))` by metis_tac[] >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all word_scale_actual_post >> strip_tac >>
  `allocas_from 0 s` by simp[allocas_from_def] >>
  drule_all word_scale_counted_normal_post >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule word_scale_cursor_length >> strip_tac >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def, gas_explicit_def, word_scale_source_words] >>
  qexistsl_tac [`INL (IntV (&(w2n w * denomination_multiplier dn)))`,
    `es`, `H`, `th`, `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  gvs[word_interval_ghost_inv_index]
QED

Theorem word_scale_typed_abort_outcome:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  ~(w2n w * denomination_multiplier dn < dimword (:256)) /\
  (!z. v = Var z ==> not_fresh_at sa z) /\ eval_operand v s = SOME w /\
  op_prov G v = NONE /\ op_taint tn v = {} /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sc /\ sc.cs_next_var <= sa.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (\ee. (builtin_result cx ee.accounts ann (AsWeiValue dn) ts [IntV (&w2n w)],ee))
    (es,s,G,tn) Q (\res fin gt r. expr_exit res r)
Proof
  strip_tac >>
  `0 < denomination_multiplier dn /\ denomination_multiplier dn < dimword (:256)` by
    (qspec_then `dn` mp_tac denomination_multiplier_bounds >> simp[dimword_def]) >>
  drule_all compile_as_wei_value_int_run >> strip_tac >>
  `?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t` by metis_tac[] >>
  `allocas_from 0 s` by simp[allocas_from_def] >>
  drule_all word_scale_counted_abort >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `REPLICATE n F` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "ewv bound"))`, `es`, `H`, `th`,
    `Abort Revert_abort (t with vs_inst_idx := j)`] >>
  simp[word_scale_source_words, expr_exit_def, exit_result_def]
QED
