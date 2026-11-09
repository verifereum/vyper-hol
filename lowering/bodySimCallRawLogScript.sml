(* Piece of bodySimCallCases.body_raw_log_case. *)

Theory bodySimCallRawLog
Ancestors
  bodySimExprCases bodySimRawLog bodySimRawLogTopics gasOutcome gasSummaryCompose gasExemptCert
  bodySimRawLogBodySource bodySimRawLogTails bodySimRawLogSource
  gasSummary fragGasMode fragGasPath stmtSimDeclCompose
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph
  exprSimSend vyperTypeSystem exprSimAggregateSource vyperValue
  exprSimWordArgs exprLowering compileEnv loweringStateRelDefs emitHelper venomExecSemantics
  exprLoweringProps venomState venomMemDefs exprSimDefs exprSimStack loweringPosts exprSimHypsDefs exprSimSource vyperEvent
  fragExec venomInst exprSimHash exprSimBuffer exprSimPrecompiles emitHelperProps
  ASCIInumbers exprSimRawLog
Libs
  pairLib

(* HELD for the post-16 bodySim child-closure wave: the elements of a
   MakeArray operand (raw_log's topic list) are body_expr_ok in order.
   s1-ops-widened-expr holds the same fact as body_make_array_children_ok. *)
Theorem raw_log_make_array_children_ok:
  !cx a t n elems.
    body_expr_ok cx (Builtin a (MakeArray t n) elems) /\
    builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
    body_exprs_ok cx elems
Proof
  cheat
QED

Theorem raw_log_outcome_bind_core[local]:
  gas_outcome memory tops (ctx,func) a (es,s0) P E /\
  (!marks rr mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks rr mid (OK t) /\
    P rr (mid with gas_obs := []) t ==>
    ?v. rr = INL v /\ gas_outcome memory tops (ctx,func) (k v)
      (mid with gas_obs := [],t) Q R) /\
  (!rr mid r. E rr mid r ==> ?exc. rr = INR exc /\ R (INR exc) mid r) /\
  (!marks err ee leaf finish.
    gas_exempt_cert memory tops (ctx,func) (ignore_bind a (return ()))
      (es,s0) marks (err,ee) (leaf,finish) ==>
    gas_exempt_cert memory tops (ctx,func) (ignore_bind (bind a k) (return ()))
      (es,s0) marks (err,ee) (leaf,finish)) /\
  (!left v mid t right err ee leaf finish.
    gas_marked_exec memory (ctx,func) a (es,s0) left (INL v) mid (OK t) /\
    gas_exempt_cert memory tops (ctx,func) (ignore_bind (k v) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,finish) ==>
    gas_exempt_cert memory tops (ctx,func) (ignore_bind (bind a k) (return ()))
      (es,s0) (left ++ right) (err,ee) (leaf,finish)) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ a _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  strip_tac
  >- (gvs[] >>
      qpat_x_assum `!marks rr mid t. _` (drule_all_then strip_assume_tac) >>
      gvs[] >>
      qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
      >- (drule_all gas_marked_exec_bind_normal >> metis_tac[])
      >- (drule_all gas_marked_exec_bind_normal >> metis_tac[])
      >> metis_tac[])
  >- (qpat_x_assum `!rr mid r. _` drule >> strip_tac >> gvs[] >>
      drule gas_marked_exec_bind_exception >> metis_tac[])
  >> metis_tac[]
QED

Theorem raw_log_unitize_bind[local]:
  ignore_bind (bind a k) (return ()) =
  bind a (\v. ignore_bind (k v) (return ()))
Proof
  simp[ignore_bind_def, bind_assoc]
QED

Theorem raw_log_outcome_bind_values[local]:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> (value list) evaluation_result) (es,s0) P E /\
  (!marks rr mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks rr mid (OK t) /\
    P rr (mid with gas_obs := []) t ==>
    ?v. rr = INL v /\ gas_outcome memory tops (ctx,func) (k v)
      (mid with gas_obs := [],t) Q R) /\
  (!rr mid r. E rr mid r ==> ?exc. rr = INR exc /\ R (INR exc) mid r) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >> irule raw_log_outcome_bind_core >>
  conj_tac
  >- (simp[raw_log_unitize_bind] >> rpt strip_tac >>
      irule gas_exempt_cert_bind_values >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (simp[raw_log_unitize_bind] >> rpt strip_tac >>
      irule gas_exempt_cert_error_values >> simp[]) >>
  qexistsl_tac [`E`, `P`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem raw_log_outcome_bind_value[local]:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> value evaluation_result) (es,s0) P E /\
  (!marks rr mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks rr mid (OK t) /\
    P rr (mid with gas_obs := []) t ==>
    ?v. rr = INL v /\ gas_outcome memory tops (ctx,func) (k v)
      (mid with gas_obs := [],t) Q R) /\
  (!rr mid r. E rr mid r ==> ?exc. rr = INR exc /\ R (INR exc) mid r) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >> irule raw_log_outcome_bind_core >>
  conj_tac
  >- (simp[raw_log_unitize_bind] >> rpt strip_tac >>
      irule gas_exempt_cert_bind_value >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (simp[raw_log_unitize_bind] >> rpt strip_tac >>
      irule gas_exempt_cert_error_value >> simp[]) >>
  qexistsl_tac [`E`, `P`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem raw_log_outcome_bind_unit[local]:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> unit evaluation_result) (es,s0) P E /\
  (!marks rr mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks rr mid (OK t) /\
    P rr (mid with gas_obs := []) t ==>
    ?v. rr = INL v /\ gas_outcome memory tops (ctx,func) (k v)
      (mid with gas_obs := [],t) Q R) /\
  (!rr mid r. E rr mid r ==> ?exc. rr = INR exc /\ R (INR exc) mid r) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >> irule raw_log_outcome_bind_core >>
  conj_tac
  >- (simp[raw_log_unitize_bind] >> rpt strip_tac >>
      irule gas_exempt_cert_bind_unit >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (simp[raw_log_unitize_bind] >> rpt strip_tac >>
      irule gas_exempt_cert_error_unit >> simp[]) >>
  qexistsl_tac [`E`, `P`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!marks rr mid t. _` (drule_all_then strip_assume_tac) >>
  gvs[]
QED

Theorem expr_body_pre_make_array_arg[local]:
  expr_body_pre cenv cx env (Builtin ann (MakeArray t b) args) es /\
  MEM e args /\ expr_sim_inv cenv cx env es' ==>
  expr_body_pre cenv cx env e es'
Proof
  strip_tac >> drule expr_body_pre_builtin_arg >> disch_then irule >> simp[]
QED

Theorem raw_log_dynamic_frag:
  body_inv tops ctx cenv cx /\ body_exprs_ok cx args /\
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es /\
  (?a elem bd topics data cap.
    args = [Builtin a (MakeArray elem bd) topics; data] /\
    expr_type data = BaseT (BytesT (Dynamic cap))) /\
  compile_expr cenv ty (Call ann RawLog args dflt) sa = (StackValue ann (Lit 0w),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx (Call ann RawLog args dflt)) (read_result cx))
    expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx (Call ann RawLog args dflt)) (read_result cx)) (es,s0)
    (\rr ee t. ?v. rr = INL v /\
      expr_post ctx func cenv cx (Call ann RawLog args dflt)
        es sa sb s0 ee v (Lit 0w) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee r. expr_exit rr r)
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule raw_log_body_pre_shape >> strip_tac >> gvs[] >>
  drule_all raw_log_literal_typed >> strip_tac >> gvs[] >>
  `body_exprs_ok cx topics` by
    (qpat_assum `body_exprs_ok cx [_;_]`
       (strip_assume_tac o REWRITE_RULE [body_exprs_ok_def]) >>
     drule_all raw_log_make_array_children_ok >> simp[]) >>
  `!arg s. MEM arg topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env arg s /\ expr_type arg = BaseT (BytesT (Fixed 32))` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
         qpat_x_assum `MEM arg topics` mp_tac >>
         qpat_x_assum `expr_sim_inv _ _ _ s` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         metis_tac[expr_body_pre_raw_log_arg, expr_body_pre_make_array_arg, MEM]) >>
     fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_raw_log_stages] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `lower_word_args cenv expr_type topics sa = (ops,sm)` >>
  rename1 `lower_value compile_expr cenv _ data sm = (data_op,sn)` >>
  rename1 `emit_op MLOAD [data_op] sn = (len_op,sl)` >>
  rename1 `emit_op ADD [data_op; Lit 32w] sl = (ptr_op,sp)` >>
  rename1 `emit_inst LOG _ [] sp = ((),sb)` >>
  `!s. expr_sim_inv cenv cx env s ==>
       expr_body_pre cenv cx env data s` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[expr_body_pre_raw_log_arg, MEM]) >>
  qmatch_asmsub_abbrev_tac `expr_body_pre cenv cx env call es` >>
  qpat_x_assum `well_typed_expr env (Builtin _ _ _)` kall_tac >>
  qpat_x_assum `well_typed_expr env data` kall_tac >>
  qpat_x_assum `EVERY _ (MAP expr_type topics)` kall_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sn /\ sm.cs_next_var <= sn.cs_next_var /\
   sm.cs_next_id <= sn.cs_next_id` by
    (drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> simp[]) >>
  `cs_extends sn sl /\ cs_extends sl sp /\ cs_extends sp sb` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `emit_inst LOG _ _ _ = _` mp_tac >>
     simp[emit_op_def, emit_inst_def, comp_bind_def, comp_return_def, comp_ignore_bind_def,
          fresh_var_def, fresh_id_def, emit_def, cs_extends_def] >>
     rpt strip_tac >> gvs[] >> simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends sm sb /\ cs_extends sn sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `!z. data_op = Var z ==> not_fresh_at sn z` by
    (drule exprOperandVarTheory.compile_lower_value_var >> simp[]) >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  simp[Abbr `call`] >>
  drule_all raw_log_forced_source_eval >>
  simp[SF ETA_ss] >> disch_then (fn th => rewrite_tac[th]) >>
  drule_all raw_log_body_topics_sim >>
  disch_then (mp_then Any irule raw_log_outcome_bind_values) >>
  reverse conj_tac >- (Cases >> simp[wb_args_exit_def]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all raw_log_topics_marked_post >> strip_tac >>
  drule_all raw_log_marked_data_ready >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    fs[wb_args_post_def] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
     drule gas_path_normal >> simp[]) >>
  `expr_body_pre cenv cx env data (mid with gas_obs := [])` by metis_tac[] >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  `lower_value compile_expr cenv (expr_type data) data sm = (data_op,sn)` by simp[] >>
  drule_all expr_sim_apply >>
  disch_then (mp_then Any irule raw_log_outcome_bind_value) >>
  reverse conj_tac >- (Cases >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `expr_post ctx func cenv cx call` >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     disch_then (mp_then Any mp_tac
       vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom) >> simp[]) >>
  qpat_x_assum `body_inv _ _ _ _` kall_tac >>
  qpat_x_assum `body_exprs_ok cx [_;_]` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ call _` kall_tac >>
  qpat_x_assum `gas_admissible _ _ es` kall_tac >>
  qpat_x_assum `body_exprs_ok cx topics` kall_tac >>
  qpat_x_assum `!arg s. _` kall_tac >>
  `expr_body_pre cenv cx env data
    (mid with gas_obs := gas_explicit marks' t.vs_gas_readings)` by simp[] >>
  `bind (eval_expr cx data) (read_result cx)
     (mid with gas_obs := gas_explicit marks' t.vs_gas_readings) =
     (INL v, mid' with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all (SRULE [SF ETA_ss] expr_body_pre_base_result) >> strip_tac >>
  `?bs. v = BytesV bs` by
    (qpat_x_assum `!v'. INL v = _ ==> _` mp_tac >>
     simp[] >> Cases_on `v` >> simp[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by simp[] >>
  drule_all raw_log_data_post_transport >> strip_tac >>
  `evaluate_type (get_tenv cx) (expr_type data) =
     SOME (BaseTV (BytesT (Dynamic cap)))` by
    (`expr_body_pre cenv cx env data mid` by simp[] >>
     drule expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  drule_all raw_log_dynamic_data_view >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (mid' with gas_obs := []) t'` by fs[expr_post_def] >>
  `~t'.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def, gas_marked_path_def] >>
     simp[] >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `LENGTH vs = LENGTH topics` by fs[typed_args_post_def] >>
  `eval_operands ops t' = SOME (MAP event_value_to_word vs)` by
    (qpat_x_assum `LIST_REL _ ops vs` mp_tac >>
     rpt (pop_assum kall_tac) >> qid_spec_tac `vs` >>
     Induct_on `ops` >> Cases_on `vs` >>
     simp[eval_operands_def, e2eDefsTheory.event_value_to_word_eq_val_to_w256] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `EVERY (\op. !z. op = Var z ==> not_fresh_at sn z) ops` by
    (fs[EVERY_MEM] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `LENGTH ops <= 4 /\ LENGTH vs <= 4 /\ sa.cs_next_var <= sn.cs_next_var` by decide_tac >>
  `expr_type call = NoneT` by simp[Abbr `call`, expr_type_def] >>
  `post_value_type cenv call = expr_type call` by simp[Abbr `call`] >>
  `fn_has_code sn sb func` by metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans] >>
  qpat_assum `LENGTH ops = LENGTH topics`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  drule_all raw_log_dynamic_tail_counted >> strip_tac >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  irule raw_log_tail_summary >>
  simp[dest_BytesV_def, raw_log_post_gas_obs] >>
  qexists_tac `t''` >> gvs[]
QED

Theorem raw_log_alloc_args_post[local]:
  wb_args_post ctx func cenv cx es0 sa s0 es ops vals t /\
  stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es0 sa s0 u /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sm x) /\
              (!l. op <> Label l)) ops /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t) ==>
  wb_args_post ctx func cenv cx es0 sa s0 es ops vals u
Proof
  simp[wb_args_post_def] >> strip_tac >> simp[] >>
  qpat_x_assum `LIST_REL _ ops vals` mp_tac >>
  qpat_x_assum `EVERY _ ops` mp_tac >>
  qid_spec_tac `vals` >> Induct_on `ops` >> simp[] >>
  gen_tac >> Cases_on `vals` >> simp[] >> rpt strip_tac
  >- (Cases_on `h` >> gvs[eval_operand_def] >> metis_tac[]) >>
  first_x_assum irule >> simp[]
QED

Theorem raw_log_fixed32_body_frag:
  body_inv tops ctx cenv cx /\ body_exprs_ok cx args /\
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es /\
  (?a elem bd topics data.
    args = [Builtin a (MakeArray elem bd) topics; data] /\
    expr_type data = BaseT (BytesT (Fixed 32))) /\
  compile_expr cenv ty (Call ann RawLog args dflt) sa = (StackValue ann (Lit 0w),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx (Call ann RawLog args dflt)) (read_result cx))
    expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx (Call ann RawLog args dflt)) (read_result cx)) (es,s0)
    (\rr ee t. ?v. rr = INL v /\
      expr_post ctx func cenv cx (Call ann RawLog args dflt)
        es sa sb s0 ee v (Lit 0w) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee r. expr_exit rr r)
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule raw_log_body_pre_shape >> strip_tac >> gvs[] >>
  drule_all raw_log_literal_typed >> strip_tac >> gvs[] >>
  `body_exprs_ok cx topics` by
    (qpat_assum `body_exprs_ok cx [_;_]`
       (strip_assume_tac o REWRITE_RULE [body_exprs_ok_def]) >>
     drule_all raw_log_make_array_children_ok >> simp[]) >>
  `!arg s. MEM arg topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env arg s /\ expr_type arg = BaseT (BytesT (Fixed 32))` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
         qpat_x_assum `MEM arg topics` mp_tac >>
         qpat_x_assum `expr_sim_inv _ _ _ s` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         metis_tac[expr_body_pre_raw_log_arg, expr_body_pre_make_array_arg, MEM]) >>
     fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  `!s. expr_sim_inv cenv cx env s ==>
       expr_body_pre cenv cx env data s` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[expr_body_pre_raw_log_arg, MEM]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_raw_log_stages] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `lower_word_args cenv expr_type topics sa = (ops,sm)` >>
  rename1 `compile_alloc_buffer 32 sm = (buf,sk)` >>
  rename1 `lower_value compile_expr cenv _ data sk = (data_op,sn)` >>
  rename1 `emit_void MSTORE _ sn = (u,sp)` >>
  rename1 `emit_inst LOG _ [] sp = (u,sb)` >>
  qmatch_asmsub_abbrev_tac `expr_body_pre cenv cx env call es` >>
  qpat_x_assum `well_typed_expr env (Builtin _ _ _)` kall_tac >>
  qpat_x_assum `well_typed_expr env data` kall_tac >>
  qpat_x_assum `EVERY _ (MAP expr_type topics)` kall_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sk /\ sm.cs_next_var <= sk.cs_next_var /\
   sm.cs_next_id <= sk.cs_next_id` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_inst_def,
         comp_bind_def, comp_return_def, comp_ignore_bind_def,
         fresh_var_def, fresh_id_def, emit_def, cs_extends_def] >>
     rpt strip_tac >> gvs[] >> simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends sk sn /\ sk.cs_next_var <= sn.cs_next_var /\
   sk.cs_next_id <= sn.cs_next_id` by
    (drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> simp[]) >>
  `cs_extends sn sp /\ cs_extends sp sb` by
    (qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
     qpat_x_assum `emit_inst LOG _ _ _ = _` mp_tac >>
     simp[emit_void_def, emit_inst_def, comp_bind_def, comp_return_def,
          fresh_id_def, emit_def, cs_extends_def] >>
     rpt strip_tac >> gvs[] >> simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends sm sb /\ cs_extends sk sb /\ cs_extends sn sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sk func /\ fn_has_code sk sn func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sk /\
   local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  simp[Abbr `call`] >>
  drule_all raw_log_forced_source_eval >>
  simp[SF ETA_ss] >> disch_then (fn th => rewrite_tac[th]) >>
  drule_all raw_log_body_topics_sim >>
  disch_then (mp_then Any irule raw_log_outcome_bind_values) >>
  reverse conj_tac >- (Cases >> simp[wb_args_exit_def]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all raw_log_topics_marked_post >> strip_tac >>
  drule_all raw_log_marked_data_ready >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t /\
   wb_frame cenv es sa s0 t` by fs[wb_args_post_def] >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def, gas_marked_path_def] >>
     simp[] >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all raw_log_alloc_counted >> strip_tac >>
  `wb_args_post ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t'` by
    (irule raw_log_alloc_args_post >> simp[] >> qexistsl_tac [`sm`, `t`] >> simp[]) >>
  qpat_x_assum `wb_args_post _ _ _ _ _ _ _ _ _ _ t` kall_tac >>
  irule gas_outcome_zero_prefix >> qexists_tac `t'` >> simp[] >>
  `expr_body_pre cenv cx env data (mid with gas_obs := [])` by
    (qpat_x_assum `!s. expr_sim_inv _ _ _ _ ==> expr_body_pre _ _ _ data _` irule >> simp[]) >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  `lower_value compile_expr cenv (expr_type data) data sk = (data_op,sn)` by simp[] >>
  drule_all expr_sim_apply >>
  disch_then (mp_then Any irule raw_log_outcome_bind_value) >>
  reverse conj_tac >- (Cases >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `expr_post ctx func cenv cx call` >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     disch_then (mp_then Any mp_tac
       vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom) >> simp[]) >>
  qpat_x_assum `body_inv _ _ _ _` kall_tac >>
  qpat_x_assum `body_exprs_ok cx [_;_]` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ call _` kall_tac >>
  qpat_x_assum `gas_admissible _ _ es` kall_tac >>
  qpat_x_assum `body_exprs_ok cx topics` kall_tac >>
  `expr_body_pre cenv cx env data
    (mid with gas_obs := gas_explicit marks' t'.vs_gas_readings)` by
    (qpat_x_assum `!s. expr_sim_inv _ _ _ _ ==> expr_body_pre _ _ _ data _` irule >> simp[]) >>
  `bind (eval_expr cx data) (read_result cx)
     (mid with gas_obs := gas_explicit marks' t'.vs_gas_readings) =
     (INL v, mid' with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all (SRULE [SF ETA_ss] expr_body_pre_base_result) >> strip_tac >>
  `?bs. v = BytesV bs` by
    (qpat_x_assum `!v'. INL v = _ ==> _` mp_tac >>
     simp[] >> Cases_on `v` >> simp[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by simp[] >>
  `sa.cs_next_var <= sk.cs_next_var /\ sa.cs_next_id <= sk.cs_next_id` by decide_tac >>
  `EVERY (\op. (!z. op = Var z ==> not_fresh_at sk z) /\ (!l. op <> Label l)) ops` by
    (fs[EVERY_MEM] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  drule_all raw_log_data_post_transport >> strip_tac >>
  `MAP FDOM mid.scopes = MAP FDOM mid'.scopes` by
    (qpat_assum `bind (eval_expr _ _) _ _ = _` mp_tac >>
     disch_then (mp_then Any mp_tac
       (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `lookup_var p t' = SOME w` by fs[eval_operand_def] >>
  `MAP FDOM (mid with gas_obs := []).scopes =
   MAP FDOM (mid' with gas_obs := []).scopes` by simp[] >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t'` by simp[stmt_state_rel_gas_obs] >>
  `!n b sz. local_region cenv (mid with gas_obs := []).scopes t' n b sz ==>
     regions_disjoint (w2n w) 32 b sz` by
    (simp[] >> rpt strip_tac >>
     qpat_x_assum `!name b len. local_region _ mid.scopes t' _ _ _ ==> _` irule >>
     goal_assum (drule_at Any)) >>
  `sa.cs_next_id <= sm.cs_next_id` by simp[] >>
  drule_all raw_log_fixed_buffer_after_data >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (mid' with gas_obs := []) t''` by fs[expr_post_def] >>
  `~t''.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def, gas_marked_path_def] >>
     simp[] >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `LENGTH vs = LENGTH topics` by fs[typed_args_post_def] >>
  `eval_operands ops t'' = SOME (MAP event_value_to_word vs)` by
    (qpat_x_assum `LIST_REL _ ops vs` mp_tac >>
     rpt (pop_assum kall_tac) >> qid_spec_tac `vs` >>
     Induct_on `ops` >> Cases_on `vs` >>
     simp[eval_operands_def, e2eDefsTheory.event_value_to_word_eq_val_to_w256] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `LENGTH ops <= 4 /\ LENGTH vs <= 4` by decide_tac >>
  `expr_type call = NoneT` by simp[Abbr `call`, expr_type_def] >>
  `post_value_type cenv call = expr_type call` by simp[Abbr `call`] >>
  `fn_has_code sn sb func` by metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans] >>
  `LENGTH bs = 32` by fs[vyperTypingTheory.value_has_type_def] >>
  `evaluate_type (get_tenv cx) (expr_type data) =
     SOME (BaseTV (BytesT (Fixed 32)))` by simp[vyperValueTheory.evaluate_type_def] >>
  `eval_operand data_op t'' = SOME
     (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs))` by
    (`post_value_type cenv data = expr_type data` by
       (irule post_value_type_word >> simp[is_word_type_def]) >>
     qpat_assum `expr_post _ _ _ _ data _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[expr_post_def, expr_val_at_def] >>
     asm_simp_tac std_ss [post_value_type_word, is_word_type_def] >> strip_tac >>
     drule exprBopSimPropsTheory.expr_val_rel_typed >>
     simp[is_word_type_def] >> disch_then irule >> gvs[]) >>
  `TAKE 32 (word_to_bytes_be
     (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs))) = bs` by
    (qpat_assum `LENGTH bs = 32` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     qpat_assum `LENGTH bs = 32`
       (fn th => CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV (GSYM th))))) >>
     irule typed_bytes_prefix >> simp[]) >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  qpat_assum `LENGTH ops = LENGTH topics`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  `MAP FDOM es.scopes = MAP FDOM (mid' with gas_obs := []).scopes` by simp[] >>
  ` (mk_inst sm.cs_next_id ALLOCA [Lit (n2w 32)]
       [STRING #"%" (toString sm.cs_next_var)]).inst_opcode = ALLOCA /\
    (mk_inst sm.cs_next_id ALLOCA [Lit (n2w 32)]
       [STRING #"%" (toString sm.cs_next_var)]).inst_id = sm.cs_next_id` by simp[mk_inst_def] >>
  `FLOOKUP t''.vs_allocas
    (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString sm.cs_next_var)]).inst_id = SOME (w2n w,32)` by simp[mk_inst_def] >>
  drule_all raw_log_fixed_tail_counted >> strip_tac >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  irule raw_log_tail_summary >>
  simp[dest_BytesV_def, raw_log_post_gas_obs] >>
  qexists_tac `t'''` >> gvs[]
QED

Theorem raw_log_body_expr_ok:
  !cx v20 es v21.
    body_exprs_ok cx es ==> body_expr_ok cx (Call v20 RawLog es v21)
Proof
  rpt gen_tac >> strip_tac >> irule body_expr_ok_intro >> conj_tac >~ [`_ <> Subscript _ _ _`] >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim ctx func cenv cx ty (Call v20 RawLog es v21) es'` by
    (simp[expr_sim_def] >> rpt strip_tac >>
     drule_all raw_log_body_lower_value >> strip_tac >> gvs[] >>
     drule raw_log_body_pre_shape >> strip_tac >> gvs[]
     >- (irule raw_log_fixed32_body_frag >> goal_assum (drule_at Any) >>
         simp[] >> metis_tac[]) >>
     irule raw_log_dynamic_frag >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  irule expr_vv_sim_stack >> simp[] >>
  conj_tac >- (drule raw_log_body_compile_stack >> metis_tac[]) >>
  drule raw_log_body_pre_shape >> strip_tac >> gvs[] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def,
       lift_option_type_def, type_check_def, check_not_static_def,
       assert_def, raise_def, push_log_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED
