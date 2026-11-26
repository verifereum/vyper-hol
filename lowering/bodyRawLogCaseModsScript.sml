(* Join the RawLog topic execution and the selected data continuation. *)
Theory bodyRawLogCaseMods
Ancestors
  bodyRawLogSourceCutsMods bodyRawLogOperandShapeMods bodyRawLogTopicsRunMods
  bodyRawLogFixedDataMods bodyRawLogDynamicDataMods bodyActionStackVVMods
  bodyFullRawLogLayout bodyFullRawLogJoinPost bodyCreateCtorRowsReplayMods
  bodyForcedStorageFrameMods bodyFullIfExpReach bodyFullHashKeccakFixed
  bodyMemoryDefs bodyExtKeywordScalarTypingMods logArgumentTypeEval exprSafeOperand
  exprSimSliceCompose exprSimFullBundleProps gasOutcomeFullPostMods
  bodyFullPredsMods bodyFullPostsMods bodyInvSplit bodyFullShadowBodyInv
  exprBodyPreProps exprBodyPreTypingProps bodyWriteSubscriptSourceMods
  gasShadowCompileStmtHelpers gasShadowCompileHelpers gasShadowCompile
  exprCallbackContracts exprSimWordArgs vyperEvalExprPreservesScopesDom
  vyperStorageTrace vyperStorageFootprint vyperTypeInvariants
  exprLoweringProps exprSimDefs exprSimProps loweringPosts loweringShapeDefs
  fragGasOriginPtr venomState venomExecSemantics unitTransformDefs
  stmtSimForRounds gasContext compileEnv exprSimExtCallCase
  vyperInterpreter vyperState exprLowering
  vyperAST vyperValue vyperTyping vyperEvent words list finite_map
Libs pairLib monadsyntax

val raw_log_next = ``\vs. bind (bind (eval_expr cx data) (read_result cx))
  (\v. do bs <- lift_option_type (dest_BytesV v) "raw_log data";
          type_check (LENGTH vs <= 4) "raw_log too many topics";
          check_not_static cx;
          push_log (encode_raw_event_values cx.txn.target vs bs);
          return NoneV od)``;

Theorem raw_log_child_value[local]:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es
Proof
  strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _` drule_all >> simp[]
QED

Theorem raw_log_eval_exprs_append[local]:
  !xs ys. eval_exprs cx (xs ++ ys) =
    bind (eval_exprs cx xs) (\vs. bind (eval_exprs cx ys) (\ws. return (vs ++ ws)))
Proof
  Induct
  >- (simp[FUN_EQ_THM, eval_exprs_nil, bind_def, return_def] >>
      rpt gen_tac >> Cases_on `eval_exprs cx ys x` >> Cases_on `q` >> simp[]) >>
  simp[APPEND] >> gen_tac >> once_rewrite_tac[eval_exprs_cons_action] >>
  simp[bind_assoc, vyperStateTheory.bind_return]
QED

Theorem raw_log_head_admissible[local]:
  gas_admissible (bind (eval_exprs cx topics) next) expr_res_ok orig /\
  topics = pre ++ e::rest /\
  (!tail. eval_exprs cx pre (orig with gas_obs := xs ++ tail) =
       (INL vs,es with gas_obs := tail)) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >>
  qpat_x_assum `gas_admissible _ _ orig` mp_tac >>
  asm_rewrite_tac[raw_log_eval_exprs_append, bind_assoc, vyperStateTheory.bind_return] >>
  disch_tac >>
  drule_all_then mp_tac (REWRITE_RULE [gas_admissible_gas_obs] gas_admissible_bind_tail) >>
  simp[eval_exprs_cons_action, bind_assoc, vyperStateTheory.bind_return] >> strip_tac >>
  qpat_x_assum `gas_admissible _ _ es` mp_tac >>
  pure_rewrite_tac[GSYM bind_assoc, gas_admissible_def] >>
  disch_tac >> rpt gen_tac >> strip_tac >> Cases_on `res`
  >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[bind_assoc, bind_def] >> metis_tac[]
QED

Theorem raw_log_topic_shapes[local]:
  (!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty) /\
  well_typed_expr env e /\ expr_type e = BaseT (BytesT (Fixed 32)) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sm) ==>
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l)
Proof
  strip_tac >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all_then strip_assume_tac exprWordOperandTheory.lower_value_word_shape >>
  simp[]
QED

Theorem raw_log_topics_ready[local]:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  gas_admissible (bind (eval_exprs cx topics) next) expr_res_ok orig /\
  (!pre rest obs vs mid.
     topics = pre ++ rest /\ eval_exprs cx pre (orig with gas_obs := obs) = (INL vs,mid) ==>
     expr_sim_inv_mods mods cenv cx env mid /\
     body_const_cells_agree_mods mods cx env mid /\
     body_exprs_full_ok_mods mods exps cx rest /\
     (rest <> [] ==> expr_body_pre_mods mods cenv cx env (HD rest) mid)) /\
  EVERY (\e. well_typed_expr env e /\ expr_type e = BaseT (BytesT (Fixed 32))) topics ==>
  raw_log_topics_ready_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx orig topics
Proof
  strip_tac >> simp[raw_log_topics_ready_mods_def] >> rpt gen_tac >> strip_tac >>
  `eval_exprs cx pre (orig with gas_obs := xs) = (INL vs,es with gas_obs := [])` by
    (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  qpat_assum `!pre rest obs vs mid. _ ==> _`
    (qspecl_then [`pre`,`e::rest`,`xs`,`vs`,`es with gas_obs := []`] mp_tac) >>
  (impl_tac >- fs[]) >>
  simp[Once body_exprs_full_ok_mods_def] >> strip_tac >>
  `well_typed_expr env e /\ expr_type e = BaseT (BytesT (Fixed 32))` by
    (qpat_assum `EVERY _ topics` mp_tac >>
     qpat_assum `topics = _` (fn eq => rewrite_tac[eq]) >> simp[EVERY_APPEND]) >>
  `expr_sim_inv_mods mods cenv cx env es` by simp[] >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `expr_body_pre_mods mods cenv cx env e es` by simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >> rpt conj_tac
  >- (irule raw_log_head_admissible >>
      qpat_assum `gas_admissible _ _ orig` (irule_at Any) >>
      qexistsl_tac [`xs`,`vs`,`rest`,`pre`] >> fs[])
  >- (irule raw_log_child_value >>
      qpat_assum `expr_body_pre_mods _ _ _ _ _ _` (irule_at Any) >> simp[] >>
      qexistsl_tac [`tops`,`src`,`exps`] >> simp[])
  >- (rpt gen_tac >> strip_tac >> irule raw_log_topic_shapes >>
      goal_assum (drule_at Any) >> simp[] >> qexists_tac `env` >>
      simp[] >> rpt strip_tac >> drule_all_then ACCEPT_TAC consistent_variable_type_well_formed) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (`expr_body_pre_mods mods cenv cx env e (es with gas_obs := ys)` by simp[] >>
      `is_word_type (expr_type e)` by simp[is_word_type_def] >>
      qpat_assum `expr_body_pre_mods _ _ _ _ _ (_ with gas_obs := _)`
        (mp_then (Pos hd) mp_tac expr_body_pre_mods_word_value) >>
      disch_then drule >> simp[evaluate_type_def]) >>
  drule (REWRITE_RULE [ETA_AX] forced_eval_expr_preserves_scopes_dom) >> simp[]
QED

(* The final post and the relative suffix post differ only in their entry. *)
val log_post = ``\H (res:value + exception) ee G tn t. ?v. res = INL v /\
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee v (Lit 0w) t /\
  expr_store_bound cx (post_value_type cenv e) v (Lit 0w) t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF (H:(bool # bytes32 # type_value) list # num list)) lo d cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v (Lit 0w) G tn t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e (Lit 0w) G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

val log_relative_post = Q.INST [`es` |-> `mid`, `sa` |-> `sm`, `s0` |-> `u`,
                               `G0` |-> `Gm`, `tn0` |-> `tnm`] (REFL log_post)
                        |> concl |> rhs;

Theorem raw_log_reanchor_post[local]:
  e = Call NoneT RawLog [Builtin a (MakeArray elem bd) topics;data] NONE /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ ci_mono sa sm /\
  raw_log_topics_post_mods DF lo d ctx func cenv cx topics ops sa sm es s0 G0 tn0
    H (INL vals) mid Gm tnm u /\
  (^log_relative_post) H res ee G tn t ==>
  (^log_post) H res ee G tn t
Proof
  BETA_TAC >> strip_tac >> gvs[expr_post_mods_def] >>
  qpat_x_assum `raw_log_topics_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [raw_log_topics_post_mods_def]) >>
  fs[ci_mono_def,post_value_type_def,expr_type_def] >>
  `expr_has_effect (Call NoneT RawLog [Builtin a (MakeArray elem bd) topics;data] NONE)` by
    simp[expr_has_effect_thm] >>
  drule_then assume_tac expr_post_frame >>
  `wb_frame cenv es ee sa s0 t` by
    (drule_all_then ACCEPT_TAC wb_frame_trans) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` by
    metis_tac[wordArgsPtrTheory.ghost_kept_at_wb_trans] >>
  simp[] >> fs[expr_post_def, wb_frame_def] >> conj_tac
  >- (irule expr_val_at_start_mono >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[]
QED

Theorem raw_log_next_frame[local]:
  !vs. storage_trace_frame (^raw_log_next vs)
Proof
  gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
  reverse conj_tac >- MATCH_ACCEPT_TAC (GEN_ALL bodyForcedStorageFrameModsTheory.bop_forced_storage_frame) >>
  gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_lifts] >> gen_tac >> BETA_TAC >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_check_not_static] >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_state_updates,storage_trace_frame_return]
QED

Theorem raw_log_eval_operands[local]:
  !ops vals. LIST_REL (\op v. eval_operand op t = SOME (event_value_to_word v)) ops vals ==>
    eval_operands ops t = SOME (MAP event_value_to_word vals)
Proof
  Induct >> Cases_on `vals` >> simp[venomStateTheory.eval_operands_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem raw_log_compile_stack[local]:
  !sa. ?vt op sb. compile_expr cenv ty
    (Call ann RawLog [Builtin a (MakeArray elem bd) topics;data] dflt) sa =
      (StackValue vt op,sb)
Proof
  gen_tac >> pure_once_rewrite_tac [CONJUNCT1 compile_expr_raw_def] >>
  pure_rewrite_tac [compile_expr_body_def, expr_type_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[compile_call_child_calls, compile_call_def, raw_log_topic_exprs_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[] >> rpt (pairarg_tac >> simp[])
QED

Theorem raw_log_eval_value[local]:
  eval_expr cx (Call ann RawLog args dflt) es = (INL tv, es') ==>
  tv = Value NoneV
Proof
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       type_check_def, assert_def, raise_def, lift_option_type_def,
       lift_option_def, push_log_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem body_raw_log_case_full_mods:
  body_exprs_full_ok_mods mods exps cx args ==>
  body_expr_full_ok_mods mods exps cx (Call ann RawLog args dflt)
Proof
  strip_tac >> once_rewrite_tac[body_expr_full_ok_mods_def] >> simp[] >>
  qx_genl_tac [`DF`,`lo`,`d`,`PG`,`src`,`tops`,`ctx`,`shadow_ctx`,`func`,
    `shadow_func`,`cenv`,`env`,`ty`,`es`] >> strip_tac >>
  drule_all_then (qx_choosel_then [`n`,`topics`,`data`]
    (map_every assume_tac o CONJUNCTS)) raw_log_source_cuts_mods >>
  rpt BasicProvers.VAR_EQ_TAC >>
  conj_asm1_tac >- (qmatch_goalsub_abbrev_tac `expr_sim_full_mods _ _ _ _ e _` >> suspend "forced") >>
  match_mp_tac action_stack_vv_full_mods >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ _` (irule_at Any) >>
  simp[raw_log_compile_stack] >>
  rpt strip_tac >> drule_then SUBST1_TAC raw_log_eval_value >> simp[]
QED

Resume body_raw_log_case_full_mods[forced]:
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  `!ce ty arg. gas_shadow_compiles (lower_value compile_expr ce ty arg)
     (lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr arg))` by
    (rpt gen_tac >> irule gas_shadow_stmt_lower_value_env) >>
  `!ce xs. gas_shadow_compiles (compile_multi_exprs compile_expr ce xs)
    (compile_multi_exprs compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr xs))` by
    (rpt gen_tac >>
     irule (SIMP_RULE bool_ss [] (Q.INST [`sd` |-> `T`, `sh` |-> `T`]
       (MATCH_MP gas_shadow_compiles_multi_exprs_env (CONJUNCT1 gas_shadow_compile_expr_env))))) >>
  qunabbrev_tac `e` >>
  drule_all_then (fn th =>
    assume_tac (CONJUNCT1 th) >>
    qx_choosel_then [`ops`,`sm`,`shadow_sm`,`sd`,`shadow_sd`,`value`,`sn`,`shadow_sn`]
      (map_every assume_tac o CONJUNCTS) (CONJUNCT2 (CONJUNCT2 th)))
    (Q.INST [`shadow_defaults` |-> `T`] raw_log_full_layout_shadow) >>
  qpat_x_assum `op = Lit 0w` SUBST_ALL_TAC >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >> qexists_tac `func` >> simp[]) >>
  `gas_admissible (bind (eval_exprs cx topics) ^raw_log_next) expr_res_ok es` by
    (qpat_assum `bind (eval_expr cx (Call _ _ _ _)) _ = _` (fn th => fs[th])) >>
  `raw_log_topics_ready_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx es topics` by
    (irule raw_log_topics_ready >>
     qpat_assum `gas_admissible (bind (eval_exprs _ _) _) _ _` (irule_at Any) >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
     qexists_tac `env` >> simp[] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!pre rest obs vs mid. _ ==> _`
       (qspecl_then [`pre`,`rest`,`obs`,`vs`,`mid`] mp_tac) >> simp[]) >>
  `raw_log_topics_cut_mods DF lo d ctx func cenv cx st0 sa es s0 G0 tn0` by
    (simp[raw_log_topics_cut_mods_def] >> conj_tac
     >- first_assum ACCEPT_TAC >> rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  drule_all_then assume_tac raw_log_topics_run_mods >>
  qpat_assum `bind (eval_expr cx _) _ = _` (fn th => rewrite_tac[th]) >>
  irule create_ctor_rows_replay_bind_mods >> BETA_TAC >> rpt conj_tac
  >~ [`storage_trace_frame _`] >- MATCH_ACCEPT_TAC (GEN_ALL (BETA_RULE raw_log_next_frame)) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (eval_exprs _ _) _ TopicQ _` >>
  qexists_tac `TopicQ` >> rpt conj_tac
  >- suspend "data_cut"
  >- (rpt gen_tac >> simp[Abbr `TopicQ`, raw_log_topics_post_mods_def] >>
      strip_tac >> qexists_tac `vs` >> simp[]) >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_exprs _ _) _ TopicQ _` (irule_at Any) >>
  BETA_TAC >> simp[raw_log_topics_exit_mods_def]
QED

Resume body_raw_log_case_full_mods[data_cut]:
  qx_genl_tac [`marks`,`vals`,`mid`,`Gm`,`tnm`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qunabbrev_tac `TopicQ` >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid u /\ immutable_frame_mods func cenv cx mid u /\
     storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx mid Gm tnm u` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> raw_log_topics_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     qpat_assum `valid_horizon _ _ H mid.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[raw_log_topics_post_mods_def]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> raw_log_topics_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
      (strip_assume_tac o SIMP_RULE bool_ss [raw_log_topics_post_mods_def, sumTheory.INL_11] o UNDISCH)) >>
  `eval_exprs cx topics (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL vals,mid with gas_obs := [])` by
    (qpat_assum `!tail. eval_exprs _ _ _ = _`
      (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))) >>
  qpat_x_assum `!pre rest obs vs mid. _ ==> _`
    (qspecl_then [`topics`,`[]`,`gas_explicit marks s0.vs_gas_readings`,`vals`,`mid with gas_obs := []`] mp_tac) >>
  simp[] >> strip_tac >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type data) data mid` by
    (irule raw_log_child_value >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
     qexists_tac `env` >> simp[]) >>
  suspend "suffix"
QED

Resume body_raw_log_case_full_mods[suffix]:
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ (eval_exprs _ _) _ _ _` kall_tac >>
  `gas_admissible (^raw_log_next vals) expr_res_ok mid` by
    (qpat_assum `gas_admissible (bind (eval_exprs _ _) _) _ _` (mp_then (Pos hd) mp_tac
      (REWRITE_RULE [gas_admissible_gas_obs] gas_admissible_bind_tail)) >>
     BETA_TAC >> disch_then irule >> goal_assum (drule_at Any)) >>
  `gas_admissible (bind (eval_expr cx data) (read_result cx)) expr_res_ok mid` by
    (qpat_assum `gas_admissible _ _ mid` (mp_tac o BETA_RULE) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     disch_then (mp_then (Pos hd) mp_tac slice_gas_admissible_bind_head) >>
     simp[expr_res_ok_def]) >>
  `eval_operands ops u = SOME (MAP event_value_to_word vals)` by
    (irule raw_log_eval_operands >> first_assum ACCEPT_TAC) >>
  `LENGTH vals <= 4 /\ LENGTH ops < dimword (:256)` by
    (simp[dimword_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[ci_mono_def] >>
     fs[ci_mono_def]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    (rpt conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     fs[ci_mono_def]) >>
  `return_buf_frame d cenv sm u` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
     fs[ci_mono_def, wb_frame_def]) >>
  `!fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_fmp_headroom inst s` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` (assume_tac o UNDISCH)) >>
     rpt strip_tac >> irule gas_origin_ptr_path_dalloca_fmp_headroom >>
     qpat_assum `gas_origin_ptr_path _ _ _ _` (irule_at Any) >>
     goal_assum (drule_at Any) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qmatch_goalsub_abbrev_tac `expr_post_mods _ _ _ _ _ e _ _ _ _ _ _ _ _` >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 (^raw_log_next vals) (mid,u,Gm,tnm) ^log_relative_post
     (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))` by
    (BETA_TAC >>
     qpat_x_assum `_ \/ (expr_type data <> BaseT (BytesT (Fixed 32)) /\ _)` strip_assume_tac
     >- suspend "fixed" >> suspend "dynamic") >>
  suspend "reanchor"
QED

Resume body_raw_log_case_full_mods[fixed]:
  simp_tac bool_ss [Abbr `e`] >>
  irule (GEN_ALL raw_log_fixed_data_run_mods) >>
  qpat_assum `expr_sim_full_mods _ _ _ _ data mid` (irule_at Any) >>
  qpat_assum `compile_alloc_buffer 32 sm = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr cenv _ data sd = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr _ _ (gas_shadow_expr data) _ = _` (irule_at Any) >>
  qpat_assum `eval_operands ops u = _` (irule_at Any) >>
  qpat_assum `expr_body_pre_mods _ _ _ _ data mid` (irule_at Any) >>
  qpat_assum `compile_alloc_buffer 32 shadow_sm = _` (irule_at Any) >>
  qpat_assum `emit_inst LOG _ _ _ = ((),sb)` (irule_at Any) >>
  `emit_void MSTORE [buf.buf_operand;value] sn = ((),s1)` by
    (qpat_assum `emit_inst MSTORE _ _ sn = ((),s1)` mp_tac >>
     simp_tac bool_ss [emitHelperTheory.emit_inst_def, emitHelperTheory.emit_void_def]) >>
  `post_value_type cenv data = expr_type data` by
    (irule post_value_type_word >> asm_simp_tac bool_ss [is_word_type_def] >> simp[]) >>
  asm_simp_tac bool_ss [expr_sim_full_code_def, expr_type_def, post_value_type_def, expr_has_effect_thm] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_raw_log_case_full_mods[dynamic]:
  qpat_x_assum `sd = sm` SUBST_ALL_TAC >>
  qpat_x_assum `shadow_sd = shadow_sm` SUBST_ALL_TAC >>
  qpat_x_assum `expr_type data = BaseT (BytesT (Fixed 32)) \/ _` strip_assume_tac >>
  `well_formed_type (get_tenv cx) (expr_type data)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ data mid`
       (fn th => assume_tac (MATCH_MP expr_body_pre_mods_well_typed th) >>
                 assume_tac (MATCH_MP expr_sim_inv_mods_env (MATCH_MP expr_body_pre_mods_inv th))) >>
     drule_then SUBST1_TAC (GSYM (SPEC_ALL vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv)) >>
     irule well_typed_expr_type_well_formed >> goal_assum (drule_at Any) >>
     rpt strip_tac >> drule_all_then ACCEPT_TAC consistent_variable_type_well_formed) >>
  `evaluate_type (get_tenv cx) (expr_type data) = SOME (BaseTV (BytesT (Dynamic m)))` by
    (qpat_assum `expr_type data = BaseT (BytesT (Dynamic _))` (mp_tac) >>
     qpat_assum `well_formed_type _ _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [vyperTypeSystemTheory.well_formed_type_def] >>
     rpt strip_tac >> asm_simp_tac bool_ss [evaluate_type_def] >>
     qpat_x_assum `IS_SOME _` mp_tac >> asm_simp_tac bool_ss [evaluate_type_def] >>
     simp_tac (srw_ss()) [LET_THM] >> IF_CASES_TAC >> simp[]) >>
  `post_value_type cenv data = expr_type data` by
    (irule post_value_type_bytestring >> asm_simp_tac bool_ss [is_bytestring_type_def] >> simp[]) >>
  asm_simp_tac bool_ss [Abbr `e`, post_value_type_def, expr_type_def] >>
  irule (GEN_ALL (SIMP_RULE bool_ss [post_value_type_def, expr_type_def]
    (Q.INST [`ann` |-> `NoneT`] raw_log_dynamic_data_run_mods))) >>
  qpat_assum `expr_sim_full_mods _ _ _ _ data mid` (irule_at Any) >>
  qpat_assum `lower_value compile_expr cenv _ data sm = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr _ _ (gas_shadow_expr data) _ = _` (irule_at Any) >>
  qpat_assum `emit_op MLOAD _ sn = _` (irule_at Any) >>
  qpat_assum `emit_op ADD _ _ = _` (irule_at Any) >>
  qpat_assum `emit_inst LOG _ _ _ = ((),sb)` (irule_at Any) >>
  asm_simp_tac bool_ss [expr_has_effect_thm] >>
  qexists_tac `m` >> simp_tac bool_ss [] >>
  rpt conj_tac >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
  qpat_assum `LENGTH vals <= (4:num)` (fn bnd =>
    qpat_assum `gas_admissible _ _ mid`
      (fn th => FIRST [ACCEPT_TAC (REWRITE_RULE [bnd] (BETA_RULE th)), NO_TAC]))
QED

Resume body_raw_log_case_full_mods[reanchor]:
  qpat_assum `LENGTH vals <= (4:num)` (fn bnd =>
    qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ (mid,u,Gm,tnm) _ _`
      (assume_tac o REWRITE_RULE [bnd] o BETA_RULE)) >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ (mid,u,Gm,tnm) _ _` (irule_at Any) >>
  BETA_TAC >> simp_tac bool_ss [] >>
  qx_genl_tac [`H`,`res`,`ee`,`G`,`tn`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (`storage_trace_frame (^raw_log_next vals)` by MATCH_ACCEPT_TAC (GEN_ALL raw_log_next_frame) >>
     qpat_x_assum `?xs. !tail. _ = (res,ee with gas_obs := tail)`
       (qx_choose_then `xs` (qspec_then `[]` assume_tac)) >>
     qpat_assum `LENGTH vals <= (4:num)` (fn bnd =>
       qpat_assum `storage_trace_frame _`
         (mp_then (Pos hd) mp_tac valid_horizon_frame o REWRITE_RULE [bnd] o BETA_RULE)) >>
     disch_then (drule_at (Pat `_ = (res,_)`)) >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`storage_trace_frame (eval_exprs cx topics)` by simp[evaluate_storage_trace_frame] >>
     qpat_assum `storage_trace_frame (eval_exprs _ _)`
       (mp_then (Pos hd) mp_tac valid_horizon_frame) >>
     disch_then (drule_at (Pat `eval_exprs _ _ _ = _`)) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> raw_log_topics_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
    (qspec_then `H` (assume_tac o UNDISCH)) >>
  qunabbrev_tac `e` >>
  simp_tac bool_ss [expr_type_def, post_value_type_def] >>
  match_mp_tac (GEN_ALL (SIMP_RULE bool_ss [expr_type_def, post_value_type_def]
    (BETA_RULE (Q.INST [`e` |-> `Call NoneT RawLog args NONE`] raw_log_reanchor_post)))) >>
  qpat_assum `raw_log_topics_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
    (irule_at Any) >>
  asm_simp_tac bool_ss [vyperASTTheory.expr_11] >>
  qpat_assum `?v. res = INL v /\ expr_post_mods _ _ _ _ _ _ mid _ _ u _ _ _ _ /\ _`
    (ACCEPT_TAC o SIMP_RULE bool_ss [expr_type_def, post_value_type_def])
QED

Finalise body_raw_log_case_full_mods
