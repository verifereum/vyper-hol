(* Typed rounding suffix certificates, before expression-post assembly. *)
Theory bodyPtrWordBuiltinsRoundingCases
Ancestors fragGasSeqPtr bodyPtrWordBuiltinsRounding bodyPtrWordBuiltinsRoundingPost
  bodyPtrWordBuiltinsRoundingSource bodyPtrWordBuiltinsIntervalGhost
  exprSimWordBuiltins exprSimWordArgs fragGasFresh exprLoweringProps
  bodyPtrDefs ptrDiscipline compileEnv fragExec freshWrites
  venomState venomExecSemantics list finite_map valueEncoding integer_word
  fragGasPathPtr gasSummary fragGasSeqAbort varsExt
  gasStorage vyperStorageFootprint vyperStorageTrace

Theorem word_round_typed_outcome:
  (if up then compile_ceil else compile_floor) v 10000000000 sa = (op,sb) /\
  within_int_bound (Signed 168) i /\
  (!z. v = Var z ==> not_fresh_at sa z) /\ eval_operand v s = SOME (i2w i) /\
  op_prov G v = NONE /\ op_taint tn v = {} /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv H d cenv cx es G tn s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sc /\ sc.cs_next_var <= sa.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) ==>
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (\ee. (builtin_result cx ee.accounts ann (if up then Ceil else Floor) ts [DecimalV i],ee))
    (es,s,G,tn)
    (\H r ee G' tn' u.
      r = INL (IntV ((if up then i + (10000000000-1) else i) / 10000000000)) /\
      ee = es with gas_obs := [] /\ stmt_state_rel H ctx func cenv cx es u /\
      eval_operand op u = SOME (i2w ((if up then i + (10000000000-1) else i) / 10000000000)) /\
      (!z a. not_fresh_at sa z /\ lookup_var z s = SOME a ==> lookup_var z u = SOME a) /\
      (!aid bl. FLOOKUP s.vs_allocas aid = SOME bl ==> FLOOKUP u.vs_allocas aid = SOME bl) /\
      u.vs_memory = s.vs_memory /\ ~u.vs_halted /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv H d cenv cx es G' tn' u /\ ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\
      op_taint tn' op = {} /\ op_prov G' op = NONE) R
Proof
  strip_tac >>
  reverse (Cases_on `?H0. valid_horizon cx st0 H0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >>
      simp[storage_trace_frame_def, storage_trace_domain_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `stmt_state_rel H0 ctx func cenv cx es s /\
   ghost_inv H0 d cenv cx es G tn s` by metis_tac[] >>
  `straight_fresh ((if up then compile_ceil else compile_floor) v 10000000000)` by
    (Cases_on `up` >> simp[straight_fresh_ceil, straight_fresh_floor]) >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand v (drop_fresh sa s) = SOME (i2w i)` by simp[eval_operand_drop_fresh] >>
  drule_all word_round_clean_run >> strip_tac >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` strip_assume_tac)) >>
  `allocas_from 0 s` by simp[allocas_from_def] >>
  drule_all word_round_emitted_checked >>
  disch_then (qspecl_then [`func`, `PG`, `D ARB`] strip_assume_tac) >>
  drule word_round_cursor_length >> strip_tac >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  simp[gas_summary_ptr_at_def, gas_explicit_def, word_round_source] >>
  qexistsl_tac [`INL (IntV ((if up then i + (10000000000-1) else i) / 10000000000))`,
    `es`, `HG`, `th`, `OK (actual with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[] >> gen_tac >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es s /\
   ghost_inv H d cenv cx es G tn s` by metis_tac[] >>
  drule_all (Q.INST [`H` |-> `H`] word_round_emitted_checked) >>
  disch_then (qspecl_then [`func`, `PG`, `D H`]
    (qx_choose_then `GH` (qx_choose_then `tnH` strip_assume_tac))) >>
  `GH = HG /\ tnH = th` by metis_tac[inst_seq_ptr_ghost_unique] >> gvs[] >>
  `stmt_state_rel H ctx func cenv cx es s` by metis_tac[] >>
  drule_all word_round_actual_post >> strip_tac >>
  drule_all word_round_code_prefix >> strip_tac >>
  drule word_round_emitted_shape >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >>
  gvs[word_interval_ghost_inv_index, word_round_decimal_result] >> metis_tac[]
QED
