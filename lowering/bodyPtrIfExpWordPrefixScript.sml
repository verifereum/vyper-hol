Theory bodyPtrIfExpWordPrefix
Ancestors
  ifJumpPtr bodyPtrDefs gasSummaryComposePtr fragGasPathPtr fragGasSeqPtr
  exprSimDefs loweringPosts exprSimIfExp emitHelperProps fragExec
  vyperInterpreter vyperState vyperAST valueEncoding compileEnv vyperValue gasExemptCert

Theorem ifexp_eval_forced:
  eval_expr cx (IfExp t c a b) =
  bind (bind (eval_expr cx c) (read_result cx))
    (\v. if v = BoolV T then bind (eval_expr cx a) (conditional_result cx)
         else if v = BoolV F then bind (eval_expr cx b) (conditional_result cx)
         else raise (Error (TypeError "not BoolV")))
Proof
  simp[Once evaluate_def, switch_BoolV_def, bind_assoc] >>
  simp[FUN_EQ_THM, bind_def] >> gen_tac >>
  Cases_on `eval_expr cx c x` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `read_result cx captured st` >>
  Cases_on `read_result cx captured st` >> rename1 `_ = (forced,sf)` >>
  Cases_on `forced` >> simp[] >> rpt IF_CASES_TAC >>
  simp[raise_def, bind_def]
QED

Theorem ifexp_jnz_path_ptr:
  expr_post ctx fn cenv cx c es sa sc s0 mid (BoolV sel) cop u /\
  expr_type c = BaseT BoolT /\ ptr_val_ok cx (expr_type c) (BoolV sel) cop G tn u /\
  emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
  fn_has_code sj sn fn /\ sj.cs_current_bb = sc.cs_current_bb /\
  sj.cs_current_insts = sc.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
  u.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  gas_path_ptr D 0 ctx fn PG G tn u 0 G tn
    (OK (jump_to (if sel then tl else el) u))
Proof
  strip_tac >> irule if_jnz_zero_path_ptr >> simp[] >>
  qexistsl_tac [`cop`,`sj`,`sn`] >> simp[] >>
  drule emit_inst_extends >> strip_tac >> simp[] >>
  fs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def,
     typed_val_to_w256_def, val_to_w256_def, ptr_val_ok_def]
QED

Theorem ifexp_selected_outcome_prefix_ptr:
  gas_marked_exec_ptr D (ctx,fn) PG (bind (eval_expr cx c) (read_result cx))
    (es,s0,G0,tn0) marks (INL (BoolV sel)) mid G1 tn1 (OK u) /\
  gas_path_ptr D 0 ctx fn PG G1 tn1 u 0 G2 tn2 (OK v) /\
  gas_outcome_ptr D tops (ctx,fn) PG
    (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    (mid with gas_obs := [],v,G2,tn2) Q R ==>
  gas_outcome_ptr D tops (ctx,fn) PG (eval_expr cx (IfExp t c a b))
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  `gas_outcome_ptr D tops (ctx,fn) PG
    (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    (mid with gas_obs := [],u,G1,tn1) Q R` by
    (irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
     qexists_tac `0` >> simp[]) >>
  rewrite_tac[ifexp_eval_forced] >>
  irule gas_outcome_ptr_bind_normal >> goal_assum (drule_at Any) >>
  simp[] >> Cases_on `sel` >> gvs[] >>
  rpt strip_tac >> irule gas_exempt_cert_bind_value >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ifexp_condition_exit_ptr:
  gas_marked_exec_ptr D (ctx,fn) PG (bind (eval_expr cx c) (read_result cx))
    (es,s0,G0,tn0) marks res mid G tn r /\ expr_exit res r ==>
  gas_outcome_ptr D tops (ctx,fn) PG (eval_expr cx (IfExp t c a b))
    (es,s0,G0,tn0) Q (\res ee gt r. expr_exit res r)
Proof
  Cases_on `res` >> simp[] >> strip_tac >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR y`,`mid`,`G`,`tn`,`r`] >> simp[] >> conj_tac
  >- (rewrite_tac[ifexp_eval_forced] >>
      irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
  Cases_on `r` >> fs[expr_exit_def, exit_result_def] >>
  Cases_on `y` >> fs[expr_exit_def] >>
  rename1 `Error er` >> Cases_on `er` >> fs[expr_exit_def]
QED

Theorem ifexp_condition_exempt_ptr:
  gas_exempt_cert F tops (ctx,fn)
    (ignore_bind (bind (eval_expr cx c) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,fstate) ==>
  gas_outcome_ptr D tops (ctx,fn) PG (eval_expr cx (IfExp t c a b))
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >> simp[gas_outcome_ptr_def] >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`fstate`] >>
  rewrite_tac[ifexp_eval_forced] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED
