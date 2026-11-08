Theory bodyPtrTypeBuiltinsScalarContinuation
Ancestors
  bodyPtrTypeBuiltinsScalarRawOutcome bodyPtrTypeBuiltinsScalarCountedDispatch
  bodyPtrSignedConvertSourceFrame bodyPtrDefs fragGasPathPtr
  exprLowering compileEnv venomState venomExecSemantics loweringPosts
  gasSummary exprSimDefs fragExec exprSimConvert exprSimHash exprLoweringProps
  stmtFragPtr exprSimExtract32Post

Theorem scalar_convert_counted_ghost_frame:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  conv = (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) /\
  compile_type_convert x conv sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    ghost_inv d cenv cx es H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
    ghost_kept cenv es0 s0a G0 tn0 s0 H th /\
    (t with vs_vars := s.vs_vars) = s /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all scalar_convert_counted_success >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all scalar_convert_runtime_frame >> strip_tac >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `(t with vs_vars := _) = s` (fn eq => once_rewrite_tac[GSYM eq]) >> simp[]) >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_memory = s.vs_memory` by
    (qpat_x_assum `t = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]) >>
  `ghost_inv d cenv cx es H th
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (irule ghost_inv_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at sa`,`s`,`tn`] >>
     simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `ghost_kept cenv es0 s0a G0 tn0 s0 H th` by
    (irule ghost_kept_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at sa`,`tn`] >> simp[] >>
     fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qexistsl_tac [`H`,`th`] >> simp[]
QED

Theorem scalar_convert_suffix_outcome_ptr:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  evaluate_type (get_tenv cx) src = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v /\
  (!name n. FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
    cenv.ce_flag_n_members (nsid_to_string name) = n) /\
  conv = (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) /\
  compile_type_convert x conv sa = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ fresh_vars_wrt sa s /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!t vout H th. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx src dst v = INL vout /\ expr_val_rel cx dst vout out t /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    ghost_inv d cenv cx es H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
    ghost_kept cenv es0 s0a G0 tn0 s0 H th /\
    (t with vs_vars := s.vs_vars) = s /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p)) ==>
    Q (INL vout) (es with gas_obs := []) H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (\st. (convert_result cx src dst v,st)) (es,s,G,tn) Q
    (\res fin gt r. expr_exit res r)
Proof
  strip_tac >>
  `(?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
      convert_result cx src dst v = INL vout /\ expr_val_rel cx dst vout out t) \/
    (?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t /\
      expr_exit (convert_result cx src dst v) (Abort err t))` by
    (irule scalar_raw_actual_outcome >> metis_tac[]) >>
  pop_assum strip_assume_tac
  >- (drule_all scalar_convert_counted_ghost_frame >>
      disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
      simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_ptr_at_def] >>
      qexistsl_tac [`INL vout`,`es`,`H`,`th`,
        `OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))`] >>
      gvs[]) >>
  drule_all scalar_convert_counted_abort >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `REPLICATE steps F` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`convert_result cx src dst v`,`es`,`H`,`th`,
    `Abort err (t with vs_inst_idx := j)`] >>
  gvs[oneline expr_exit_def, AllCaseEqs(), exit_result_def]
QED

Theorem scalar_convert_parent_post:
  expr_post ctx fn cenv cx e es ca sa s0 ee v x s /\
  stmt_state_rel ctx fn cenv cx ee s /\ local_ptrs_reserved cenv sa /\
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s) /\
  expr_val_rel cx dst vout out t /\ is_word_type dst /\
  ca.cs_next_var <= sa.cs_next_var ==>
  expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e]) es ca sb s0
    ee vout out (t with vs_inst_idx := j)
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx ee t` by
    (irule hash_readonly_state_rel >> metis_tac[]) >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `(t with vs_vars := _) = s` (fn eq => once_rewrite_tac[GSYM eq]) >> simp[]) >>
  irule expr_post_convert >>
  simp[stmt_state_rel_inst_idx] >> conj_tac
  >- (fs[expr_val_rel_def] >> metis_tac[hash_eval_operand_inst_idx]) >>
  qexistsl_tac [`sa`,`s`,`v`,`x`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> fs[lookup_var_def]) >>
  qpat_x_assum `t = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]
QED

Theorem scalar_convert_success_post:
  expr_post ctx fn cenv cx e es ca sa s0 ee v x s /\
  stmt_state_rel ctx fn cenv cx ee s /\ local_ptrs_reserved cenv sa /\
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s) /\
  expr_val_rel cx dst vout out t /\ is_word_type dst /\
  ca.cs_next_var <= sa.cs_next_var /\
  s.vs_current_bb = sb.cs_current_bb /\
  ghost_inv d cenv cx ee H th (t with vs_inst_idx := j) /\
  j = LENGTH sb.cs_current_insts /\
  op_prov H out = NONE /\ op_taint th out = {} /\
  ghost_kept cenv es ca G0 tn0 s0 H th ==>
  expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e]) es ca sb s0
    (ee with gas_obs := []) vout out (t with vs_inst_idx := j) /\
  (t with vs_inst_idx := j).vs_current_bb = sb.cs_current_bb /\
  (t with vs_inst_idx := j).vs_inst_idx = LENGTH sb.cs_current_insts /\
  ghost_inv d cenv cx (ee with gas_obs := []) H th (t with vs_inst_idx := j) /\
  ptr_val_ok cx (post_value_type cenv (TypeBuiltin dst Convert dst [e])) vout out H th
    (t with vs_inst_idx := j) /\
  (~is_word_type (post_value_type cenv (TypeBuiltin dst Convert dst [e])) ==>
    ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) out H (t with vs_inst_idx := j)) /\ 
  ghost_kept cenv es ca G0 tn0 s0 H th
Proof
  strip_tac >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `(t with vs_vars := _) = s` (fn eq => once_rewrite_tac[GSYM eq]) >> simp[]) >>
  simp[extract32_expr_post_end_gas_obs, ghost_inv_gas_obs, ptr_val_ok_def, vyperASTTheory.expr_type_def] >>
  conj_tac >- (irule scalar_convert_parent_post >> metis_tac[]) >>
  qpat_x_assum `t = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]
QED

Theorem scalar_convert_modern_outcome_ptr:
  valid_conversion (expr_type e) dst /\ ~is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v /\
  (!name n. FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
    cenv.ce_flag_n_members (nsid_to_string name) = n) /\
  conv = (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op (expr_type e) dst) /\
  compile_type_convert x conv sa = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ fresh_vars_wrt sa s /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  expr_post ctx fn cenv cx e es ca sa s0 ee v x s /\
  stmt_state_rel ctx fn cenv cx ee s /\ local_ptrs_reserved cenv sa /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es ca G0 tn0 s0 G tn /\
  ca.cs_next_var <= sa.cs_next_var /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (\st. (convert_result cx (expr_type e) dst v,st)) (ee,s,G,tn)
    (\res fin H th u. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e]) es ca sb s0 fin vout out u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th u /\
      ptr_val_ok cx (post_value_type cenv (TypeBuiltin dst Convert dst [e])) vout out H th u /\
      (~is_word_type (post_value_type cenv (TypeBuiltin dst Convert dst [e])) ==>
        ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) out H u) /\
      ghost_kept cenv es ca G0 tn0 s0 H th)
    (\res fin gt r. expr_exit res r)
Proof
  strip_tac >>
  `is_word_type dst` by (irule (cj 2 bodyPtrTypeBuiltinsScalarSemanticTheory.scalar_source_word_types) >>
    metis_tac[optionTheory.IS_SOME_DEF]) >>
  irule scalar_convert_suffix_outcome_ptr >>
  simp[] >> rpt (goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `out` >> (reverse conj_tac >- gvs[]) >> rpt gen_tac >> strip_tac >>
  `!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s` by metis_tac[] >>
  fs[] >> drule_all scalar_convert_success_post >> simp[]
QED
