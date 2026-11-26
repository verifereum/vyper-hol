(* One linked execution of the flat word-valued RawLog topic list. *)
Theory bodyRawLogTopicsRunMods
Ancestors
  bodyFullPostsMods bodyForcedStorageFrameMods bodyMemoryDefs bodyFullIfExpReach
  bodyInvSplit bodyFullShadowBodyInv
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasOutcomeFullPostPathMods
  fragGasOriginPtr gasExemptCertMods
  gasShadowCompileStmtHelpers gasShadowCompileHelpers gasShadowCompileBase gasShadow gasShadowState
  exprSimWordArgs wordArgsPtr exprSimProps exprLoweringProps bodyPtrDefs
  loweringPosts loweringShapeDefs compileEnv exprLowering fragExec vyperEvent valueEncoding
  vyperStorageFootprint vyperStorageTrace haltExitProj vyperTyping vyperValue
  vyperInterpreter vyperState vyperAST venomState list
Libs pairLib

Definition raw_log_topics_post_mods_def[nocompute]:
  raw_log_topics_post_mods DF lo d ctx func cenv cx rest ops sa sb es s G0 tn0
      H (res : value list + exception) ee G tn t <=>
    ?vs. res = INL vs /\ LENGTH rest = LENGTH vs /\ LENGTH ops = LENGTH vs /\
      EVERY (value_has_type (BaseTV (BytesT (Fixed 32)))) vs /\
      LIST_REL (\op v. eval_operand op t = SOME (event_value_to_word v)) ops vs /\
      EVERY (\op. op_taint tn op = {}) ops /\
      stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      wb_frame cenv es ee sa s t /\
      (~EXISTS expr_has_effect rest ==> pure_frame cenv func es sa s t) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s G tn /\
      EVERY (\op. (!x. op = Var x ==> not_fresh_at sb x) /\ (!l. op <> Label l)) ops
End

Theorem topics_word_matches[local]:
  expr_type e = BaseT (BytesT (Fixed 32)) /\
  value_has_type (BaseTV (BytesT (Fixed 32))) v /\
  expr_post H ctx func cenv cx e es sa sm s mid v op u ==>
  eval_operand op u = SOME (event_value_to_word v)
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_word >> simp[is_word_type_def]) >>
  fs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def] >>
  qpat_x_assum `!tv. _` (qspec_then `BaseTV (BytesT (Fixed 32))` mp_tac) >>
  simp[evaluate_type_def, is_word_type_def] >> strip_tac >>
  Cases_on `v` >>
  gvs[value_has_type_def, typed_val_to_w256_def, event_value_to_word_def]
QED

Theorem topics_kept_word[local]:
  eval_operand op u = SOME w /\ op_taint tn1 op = {} /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  sm.cs_next_var <= sb.cs_next_var /\
  wb_frame cenv mid ee sm u t /\ ghost_kept_at lo cenv mid sm G1 tn1 u G tn ==>
  eval_operand op t = SOME w /\ op_taint tn op = {} /\
  (!x. op = Var x ==> not_fresh_at sb x) /\ (!l. op <> Label l)
Proof
  Cases_on `op` >>
  simp[eval_operand_def] >- simp[ptrDisciplineTheory.op_taint_def] >>
  strip_tac >> fs[wb_frame_def, ghost_kept_at_def] >>
  irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]
QED

Theorem topics_replay_cons[local]:
  (!gs. eval_exprs cx pre (orig with gas_obs := xs ++ gs) =
      (INL vs,es with gas_obs := gs)) /\
  (!gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := ys ++ gs) =
      (INL v,mid with gas_obs := gs)) ==>
  !gs. eval_exprs cx (pre ++ [e]) (orig with gas_obs := (xs ++ ys) ++ gs) =
      (INL (vs ++ [v]),mid with gas_obs := gs)
Proof
  `!xs ys cx. eval_exprs cx (xs ++ ys) =
     bind (eval_exprs cx xs) (\vs. bind (eval_exprs cx ys) (\ws. return (vs ++ ws)))` by
    (Induct
     >- (simp[FUN_EQ_THM,eval_exprs_nil,bind_def,return_def] >>
         rpt gen_tac >> Cases_on `eval_exprs cx ys x` >> Cases_on `q` >> simp[]) >>
     simp[eval_exprs_cons_action,bind_assoc,bind_return]) >>
  strip_tac >> gen_tac >>
  qpat_x_assum `!xs ys cx. _`
    (qspecl_then [`pre`,`[e]`,`cx`] SUBST1_TAC) >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  qpat_x_assum `!gs. eval_exprs _ pre _ = _`
    (qspec_then `ys ++ gs` assume_tac) >>
  qpat_x_assum `!gs. bind _ _ _ = _` (qspec_then `gs` assume_tac) >>
  pure_once_rewrite_tac[bind_def] >> pure_asm_rewrite_tac[] >>
  simp_tac bool_ss [sumTheory.sum_case_def] >>
  pure_once_rewrite_tac[bind_def] >>
  pure_rewrite_tac[eval_exprs_cons_action,eval_exprs_nil] >>
  pure_once_rewrite_tac[bind_def] >> pure_asm_rewrite_tac[] >>
  simp[eval_exprs_nil,bind_def,return_def]
QED

Theorem topics_compile_cons[local]:
  compile_multi_exprs compile_expr cenv (e::rest) sa = (ops,sb) ==>
  ?op more sm.
    ops = op::more /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    compile_multi_exprs compile_expr cenv rest sm = (more,sb) /\
    ci_mono sa sm /\ ci_mono sm sb
Proof
  simp[Once compile_multi_exprs_def,comp_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  conj_tac
  >- (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac
        ci_mono_lower_value_compile_expr >> simp[]) >>
  rename1 `compile_multi_exprs _ _ rest sm = _` >>
  qspecl_then [`compile_expr`,`cenv`,`rest`,`sm`] mp_tac
    ci_mono_compile_multi_exprs >> simp[compile_expr_ci_mono]
QED

Theorem topics_paired_cons[local]:
  compile_multi_exprs compile_expr cenv (e::rest) sa = (ops,sb) /\
  compile_multi_exprs compile_expr (gas_shadow_env T cenv)
    (MAP gas_shadow_expr (e::rest)) sha = (ops,shb) /\
  gas_shadow_state sa sha /\
  fn_has_code sa sb func /\ fn_has_code sha shb shadow_func ==>
  ?op more sm shm.
    ops = op::more /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) sha = (op,shm) /\
    compile_multi_exprs compile_expr cenv rest sm = (more,sb) /\
    compile_multi_exprs compile_expr (gas_shadow_env T cenv)
      (MAP gas_shadow_expr rest) shm = (more,shb) /\
    gas_shadow_state sm shm /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code sha shm shadow_func /\ fn_has_code shm shb shadow_func /\
    ci_mono sa sm /\ ci_mono sm sb
Proof
  simp[MAP] >> strip_tac >>
  qpat_assum `compile_multi_exprs _ _ (e::rest) sa = _`
    (strip_assume_tac o MATCH_MP topics_compile_cons) >>
  qpat_assum `compile_multi_exprs _ _ (gas_shadow_expr e::_) sha = _`
    (strip_assume_tac o MATCH_MP topics_compile_cons) >>
  gvs[gas_shadow_expr_type] >>
  rename1 `lower_value _ _ _ e sa = (op,sm)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) sha = (op,shm)` >>
  `gas_shadow_state sm shm` by
    (mp_tac (Q.INST [`sd` |-> `T`, `cenv` |-> `cenv`,
         `ty` |-> `expr_type e`, `e` |-> `e`] gas_shadow_stmt_lower_value_env) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`sha`] mp_tac) >> simp[]) >>
  simp[] >>
  fs[ci_mono_def] >> metis_tac[fn_has_code_split]
QED

Theorem topics_post_cons[local]:
  expr_type e = BaseT (BytesT (Fixed 32)) /\
  value_has_type (BaseTV (BytesT (Fixed 32))) v /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ ci_mono sa sm /\ ci_mono sm sb /\
  expr_post H ctx func cenv cx e es sa sm s mid v op u /\
  ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 u /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s G1 tn1 /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  raw_log_topics_post_mods DF lo d ctx func cenv cx rest ops sm sb mid u G1 tn1
    H (INL vs) ee G tn t ==>
  raw_log_topics_post_mods DF lo d ctx func cenv cx (e::rest) (op::ops) sa sb es s G0 tn0
    H (INL (v::vs)) ee G tn t
Proof
  simp[raw_log_topics_post_mods_def,ci_mono_def] >> strip_tac >>
  drule_then assume_tac expr_post_frame >>
  `eval_operand op u = SOME (event_value_to_word v)` by
    (irule topics_word_matches >> qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (irule_at Any) >> simp[]) >>
  `op_taint tn1 op = {}` by
    (`post_value_type cenv e = expr_type e` by
      (irule post_value_type_word >> simp[is_word_type_def]) >>
     fs[ptr_val_ok_def,is_word_type_def]) >>
  drule_all_then strip_assume_tac topics_kept_word >>
  drule_all_then assume_tac wb_frame_trans >>
  simp[] >> rpt conj_tac
  >- (strip_tac >>
      irule pure_frame_trans >> drule_all_then assume_tac expr_post_pure_frame >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`mid`,`sm`,`u`] >> fs[wb_frame_def]) >>
  metis_tac[ghost_kept_at_wb_trans]
QED

Theorem topics_post_nil[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  immutable_frame_mods func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ghost_inv_at_mods (DF H) lo d cenv cx es G tn s ==>
  raw_log_topics_post_mods DF lo d ctx func cenv cx [] [] sa sa es s G tn
    H (INL []) (es with gas_obs := []) G tn s
Proof
  strip_tac >>
  `immutable_frame_mods func cenv cx (es with gas_obs := []) s =
   immutable_frame_mods func cenv cx es s` by
    (POP_ASSUM_LIST (K all_tac) >>
     simp[immutable_frame_mods_def,immutables_rel_mods_def,
         immutable_alloca_sep_mods_def,immutable_alloca_sep_def,
         loweringStateRelDefsTheory.immutables_rel_def]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G tn s =
   ghost_inv_at_mods (DF H) lo d cenv cx es G tn s` by (POP_ASSUM_LIST (K all_tac) >> simp[ghost_inv_at_mods_def]) >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H) =
   storage_well_formed_on cx es (FST H)` by (irule storage_well_formed_on_backends >> simp[]) >>
  simp[raw_log_topics_post_mods_def,wb_frame_gas_obs,wb_frame_def,
       pure_frame_def,ghost_kept_at_def]
QED

Definition raw_log_topics_exit_mods_def[nocompute]:
  raw_log_topics_exit_mods ctx cx H res ee (gt : (string |-> num # num) # taint) r <=>
    expr_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)
End

Definition raw_log_topics_cut_mods_def[nocompute]:
  raw_log_topics_cut_mods DF lo d ctx func cenv cx st0 sa es s G tn <=>
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!fn inst t. frag_reachable ctx func s fn inst t ==> dalloca_fmp_headroom inst t) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
         storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ local_ptrs_reserved cenv sa /\
    return_buf_frame d cenv sa s /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)
End

Theorem topics_nil[local]:
  raw_log_topics_cut_mods DF lo d ctx func cenv cx st0 sa es s G tn ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (eval_exprs cx []) (es,s,G,tn)
    (raw_log_topics_post_mods DF lo d ctx func cenv cx [] [] sa sa es s G tn)
    (raw_log_topics_exit_mods ctx cx)
Proof
  simp[raw_log_topics_cut_mods_def] >> strip_tac >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G`,`es`,`INL []`,`s`,`tn`] >>
  simp[eval_exprs_nil,gas_origin_ptr_path_rules] >>
  rpt strip_tac >> irule topics_post_nil >> first_x_assum drule >> simp[]
QED

Theorem topics_return_cons[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (eval_exprs cx rest) (mid,u,G1,tn1)
    (raw_log_topics_post_mods DF lo d ctx func cenv cx rest ops sm sb mid u G1 tn1)
    (raw_log_topics_exit_mods ctx cx) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    expr_post H ctx func cenv cx e es sa sm s mid v op u /\
    ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 u /\
    s.vs_alloca_next <= u.vs_alloca_next /\ ghost_kept_at lo cenv es sa G0 tn0 s G1 tn1) /\
  expr_type e = BaseT (BytesT (Fixed 32)) /\
  value_has_type (BaseTV (BytesT (Fixed 32))) v /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (bind (eval_exprs cx rest) (\vs. return (v::vs))) (mid,u,G1,tn1)
    (raw_log_topics_post_mods DF lo d ctx func cenv cx (e::rest) (op::ops) sa sb es s G0 tn0)
    (raw_log_topics_exit_mods ctx cx)
Proof
  strip_tac >> irule gas_outcome_full_mods_bind_all >> BETA_TAC >>
  conj_tac >- simp[storage_trace_frame_return] >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_values >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_values >> simp[]) >>
  conj_tac >- simp[cj 6 evaluate_storage_trace_frame] >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ Tail _` >>
  qexists_tac `\H res ee G tn t. Tail H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      goal_assum (drule_at Any) >> simp[] >>
      simp[raw_log_topics_exit_mods_def] >> rpt gen_tac >> Cases_on `res` >>
      simp[exprSimDefsTheory.expr_exit_INL]) >>
  suspend "return_cons"
QED

Resume topics_return_cons[return_cons]:
  qx_genl_tac [`marks`,`res`,`ee`,`G2`,`tn2`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp_tac bool_ss [Abbr `Tail`,raw_log_topics_post_mods_def] >>
  strip_tac >> gvs[] >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G2`,`ee`,`INL (v::vs)`,`t`,`tn2`] >>
  simp[return_def,gas_origin_ptr_path_rules] >>
  gen_tac >> strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `!tail. eval_exprs cx rest _ = _`
       (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
     drule_at (Pos (el 2)) valid_horizon_frame >>
     simp[cj 6 evaluate_storage_trace_frame] >> disch_then drule >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H` (drule_then assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  irule topics_post_cons >> simp[] >>
  qexistsl_tac [`G1`,`mid`,`sm`,`tn1`,`u`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Finalise topics_return_cons

(* The head's post retains only the pointwise facts needed to restart or
   to re-anchor the post of the suffix. *)
Definition topics_head_post_def[nocompute]:
  topics_head_post DF lo d ctx func cenv cx e sa sm es s G0 tn0 op
    H (res : value + exception) mid G tn u <=>
    ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sm s mid v op u /\
      stmt_state_rel H ctx func cenv cx mid u /\ immutable_frame_mods func cenv cx mid u /\
      storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx mid G tn u /\
      u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s.vs_alloca_next <= u.vs_alloca_next /\ ptr_val_ok cx (post_value_type cenv e) v op G tn u /\
      ghost_kept_at lo cenv es sa G0 tn0 s G tn /\
      (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t)
End

Theorem topics_head[local]:
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  raw_log_topics_cut_mods DF lo d ctx func cenv cx st0 sa es s G tn /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha = (op,shm) /\
  gas_shadow_state sa sha /\ gas_shadow_state sm shm /\
  fn_has_code sa sm func /\ fn_has_code sha shm shadow_func /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (topics_head_post DF lo d ctx func cenv cx e sa sm es s G tn op)
    (raw_log_topics_exit_mods ctx cx)
Proof
  simp[raw_log_topics_cut_mods_def] >> strip_tac >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE[expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`sha`,`shm`,`op`,`s`,`G`,`tn`] mp_tac) >>
  simp[] >>
  (impl_tac >- (rpt strip_tac >> first_x_assum drule >> simp[])) >>
  disch_then (assume_tac o REWRITE_RULE[GSYM raw_log_topics_exit_mods_def,ETA_AX]) >>
  irule gas_outcome_full_mods_post_path >> goal_assum (drule_at Any) >>
  simp[topics_head_post_def] >> rpt strip_tac >> gvs[expr_post_mods_def] >>
  reverse (rpt conj_tac)
  >- metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom] >>
  fs[expr_post_def]
QED

Theorem topics_head_horizon[local]:
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
     (INL v,mid with gas_obs := tail)) /\ valid_horizon cx st0 H mid.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >>
  qpat_x_assum `!tail. _` (qspec_then `[]` assume_tac) >>
  drule_at (Pos (el 2)) valid_horizon_frame >>
  simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame] >> disch_then drule >> simp[]
QED

Theorem topics_cut_cons[local]:
  raw_log_topics_cut_mods DF lo d ctx func cenv cx st0 sa es s G tn /\ ci_mono sa sm /\
  ~u.vs_halted /\ storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    topics_head_post DF lo d ctx func cenv cx e sa sm es s G tn op H (INL v) mid G1 tn1 u) ==>
  raw_log_topics_cut_mods DF lo d ctx func cenv cx st0 sm mid u G1 tn1
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> topics_head_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp_tac (srw_ss()) [topics_head_post_def] >> strip_tac >>
  fs[raw_log_topics_cut_mods_def,ci_mono_def] >>
  rpt conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `fn` >> simp[])
  >- (gen_tac >> disch_tac >> qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `H` (drule_then (strip_assume_tac o REWRITE_RULE[topics_head_post_def,sumTheory.INL_11]))) >> gvs[])
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[])
  >- (irule return_buf_frame_frame >>
      qexistsl_tac [`cenv`,`s`,`sa`] >> fs[expr_post_def]) >>
  rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]
QED

(* Readiness is requested only after replay of the actual source prefix.
   The callback separates the RawLog source premises from machine composition. *)
Definition raw_log_topics_ready_mods_def[nocompute]:
  raw_log_topics_ready_mods P cenv cx orig topics <=>
    !pre e rest xs vs es.
      topics = pre ++ e::rest /\
      (!tail. eval_exprs cx pre (orig with gas_obs := xs ++ tail) =
              (INL vs,es with gas_obs := tail)) ==>
      expr_type e = BaseT (BytesT (Fixed 32)) /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      expr_sim_full_mods P cenv cx (expr_type e) e es /\
      (!sa sm op. lower_value compile_expr cenv (expr_type e) e sa = (op,sm) ==>
        (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l)) /\
      (!ys v mid. bind (eval_expr cx e) (read_result cx) (es with gas_obs := ys) =
         (INL v,mid) ==>
         value_has_type (BaseTV (BytesT (Fixed 32))) v /\
         MAP FDOM es.scopes = MAP FDOM mid.scopes)
End

Theorem topics_run_suffix[local]:
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  raw_log_topics_ready_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx orig topics ==>
  !rest pre xs vs sa sb sha shb ops es s G tn.
    topics = pre ++ rest /\
    (!tail. eval_exprs cx pre (orig with gas_obs := xs ++ tail) =
            (INL vs,es with gas_obs := tail)) /\
    compile_multi_exprs compile_expr cenv rest sa = (ops,sb) /\
    compile_multi_exprs compile_expr (gas_shadow_env T cenv)
      (MAP gas_shadow_expr rest) sha = (ops,shb) /\
    gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
    raw_log_topics_cut_mods DF lo d ctx func cenv cx st0 sa es s G tn ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (eval_exprs cx rest) (es,s,G,tn)
      (raw_log_topics_post_mods DF lo d ctx func cenv cx rest ops sa sb es s G tn)
      (raw_log_topics_exit_mods ctx cx)
Proof
  strip_tac >> Induct
  >- (simp[compile_multi_exprs_def,comp_return_def] >> rpt strip_tac >> gvs[] >>
      irule topics_nil >> simp[]) >>
  qx_gen_tac `e` >> rpt gen_tac >> strip_tac >>
  qhdtm_assum `raw_log_topics_ready_mods`
    (qspecl_then [`pre`,`e`,`rest`,`xs`,`vs`,`es`] mp_tac o REWRITE_RULE[raw_log_topics_ready_mods_def]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all_then strip_assume_tac topics_paired_cons >>
  rename1 `ops = op::more` >>
  qpat_x_assum `ops = op::more` SUBST_ALL_TAC >>
  rename1 `lower_value _ _ _ e sa = (op,sm)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) sha = (op,shm)` >>
  `(!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l)` by
    (qpat_assum `!sa sm op. lower_value _ _ _ _ _ = _ ==> _` drule >> simp[]) >>
  qabbrev_tac `Head = topics_head_post DF lo d ctx func cenv cx e sa sm es s G tn op` >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
      Head (raw_log_topics_exit_mods ctx cx)` by
    (simp[Abbr `Head`] >> irule topics_head >> simp[] >>
     qexistsl_tac [`sha`,`shadow_func`,`shm`] >>
     qpat_assum `expr_type e = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >> simp[]) >>
  rewrite_tac[eval_exprs_cons_action] >> irule gas_outcome_full_mods_bind_all >> BETA_TAC >>
  conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[cj 6 evaluate_storage_trace_frame,storage_trace_frame_return]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[]) >>
  conj_tac >- simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame] >>
  qexists_tac `\H res mid G1 tn1 u. Head H res mid G1 tn1 u /\ ~u.vs_halted /\ mid.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >> goal_assum (drule_at Any) >> simp[] >>
      simp[raw_log_topics_exit_mods_def] >> rpt gen_tac >> Cases_on `res` >>
      simp[exprSimDefsTheory.expr_exit_INL,
           stmtSimPropsTheory.expr_exit_INR_type,exprSimDefsTheory.halt_exit_def]) >>
  suspend "head_next"
QED

Resume topics_run_suffix[head_next]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`u`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp_tac bool_ss [Abbr `Head`,topics_head_post_def] >> strip_tac >> gvs[] >>
  rename1 `ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 u` >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE[APPEND_NIL])) >>
     pure_asm_rewrite_tac[] >> simp[]) >>
  qpat_assum `!ys v mid. bind _ _ _ = _ ==> _` (drule_then strip_assume_tac) >>
  `raw_log_topics_cut_mods DF lo d ctx func cenv cx st0 sm mid u G1 tn1` by
    (irule topics_cut_cons >>
     qpat_assum `raw_log_topics_cut_mods _ _ _ _ _ _ _ _ sa _ _ _ _` (irule_at Any) >>
     qexistsl_tac [`v`,`op`,`e`] >> simp[]) >>
  `!tail. eval_exprs cx (pre ++ [e])
     (orig with gas_obs := (xs ++ gas_explicit marks s.vs_gas_readings) ++ tail) =
     (INL (vs ++ [v]),mid with gas_obs := tail)` by
    (irule topics_replay_cons >> simp[] >> qexists_tac `es` >> simp[]) >>
  irule topics_return_cons >>
  qpat_assum `ci_mono sa sm` (irule_at Any) >> simp[] >>
  conj_tac >- suspend "earlier_horizon" >>
  suspend "tail_ih"
QED

Resume topics_run_suffix[tail_ih]:
  first_x_assum irule >>
  qpat_assum `compile_multi_exprs _ _ (MAP gas_shadow_expr rest) shm = _` (irule_at Any) >>
  qexistsl_tac [`xs ++ gas_explicit marks s.vs_gas_readings`,`vs ++ [v]`] >>
  simp[APPEND_ASSOC]
QED

Resume topics_run_suffix[earlier_horizon]:
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (irule topics_head_horizon >>
     qexistsl_tac [`e`,`mid`,`v`,`gas_explicit marks s.vs_gas_readings`] >> simp[]) >>
  qpat_assum `raw_log_topics_cut_mods _ _ _ _ _ _ _ _ sa _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[raw_log_topics_cut_mods_def]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` (drule_then (strip_assume_tac o REWRITE_RULE[topics_head_post_def,sumTheory.INL_11]))) >>
  gvs[]
QED

Finalise topics_run_suffix

Theorem raw_log_topics_run_mods:
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  raw_log_topics_ready_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx es topics /\
  compile_multi_exprs compile_expr cenv topics sa = (ops,sb) /\
  compile_multi_exprs compile_expr (gas_shadow_env T cenv)
    (MAP gas_shadow_expr topics) sha = (ops,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
  raw_log_topics_cut_mods DF lo d ctx func cenv cx st0 sa es s G tn ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_exprs cx topics) (es,s,G,tn)
    (raw_log_topics_post_mods DF lo d ctx func cenv cx topics ops sa sb es s G tn)
    (raw_log_topics_exit_mods ctx cx)
Proof
  strip_tac >> irule topics_run_suffix >>
  qpat_assum `raw_log_topics_ready_mods _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_multi_exprs _ _ (MAP gas_shadow_expr topics) sha = _` (irule_at Any) >>
  simp[] >> qexistsl_tac [`[]`,`[]`] >> simp[eval_exprs_nil]
QED
