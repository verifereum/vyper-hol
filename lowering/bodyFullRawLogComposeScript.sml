Theory bodyFullRawLogCompose
Ancestors
  bodyFullRawLogLayout bodyFullRawLogJoinPost bodyFullRawLogTopics
  bodyFullRawLogReadiness bodyFullRawLogFixed bodyFullRawLogDynamic
  bodyFullExprGeneric bodyFullPreds vyperTypeArgFits exprWordOperand
  gasOutcomeFullCompose exprSimHypsDefs exprLoweringProps bodySimFull
  vyperTypeSystem vyperAST vyperValue vyperContext list vyperInterpreter
  vyperStorageTrace vyperStorageFootprint stmtSimDefs loweringStateRelDefs
  gasOutcomeFull gasExemptCert exprSimDefs vyperState stmtSimProps
  vyperTypeInvariants exprLowering compileEnv vyperEvalExprPreservesScopesDom
Libs pairLib

Theorem raw_log_topics_operands_shape[local]:
  expr_body_pre cenv cx env
    (Call ann RawLog [Builtin a (MakeArray elem bd) topics; data] dflt) es /\
  EVERY (\e. MEM e topics) suffix /\
  compile_multi_exprs compile_expr cenv suffix sa = (ops,sm) ==>
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sm x) /\
               (!l. op <> Label l)) ops
Proof
  strip_tac >>
  `EVERY (well_typed_expr env) topics /\
   EVERY (\e. is_word_type (expr_type e)) topics` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, Once well_typed_expr_def] >> strip_tac >>
     gvs[well_typed_expr_def, expr_type_def] >>
     Cases_on `elem` >>
     gvs[well_typed_builtin_app_def] >>
     (conj_tac
      >- (qpat_x_assum `well_typed_exprs env topics` mp_tac >>
          qid_spec_tac `topics` >> Induct >> simp[well_typed_expr_def])) >>
     fs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     `expr_type e = BaseT (BytesT (Fixed 32))` by
       (irule arg_type_fits_prim_word >>
        simp[is_prim_word_type_def] >> metis_tac[]) >>
     simp[is_word_type_def]) >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
     well_formed_type env.type_defs t` by
    (fs[expr_body_pre_def, expr_sim_inv_def, well_formed_type_def] >>
     `env.type_defs = get_tenv cx` by
       gvs[env_consistent_def, env_context_consistent_def] >>
     rpt strip_tac >>
     fs[env_consistent_def, env_scopes_consistent_def] >>
     Cases_on `lookup_scopes id es.scopes` >> gvs[] >>
     metis_tac[optionTheory.IS_SOME_DEF]) >>
  qpat_x_assum `compile_multi_exprs _ _ _ _ = _` mp_tac >>
  qpat_x_assum `EVERY (\e. MEM e topics) suffix` mp_tac >>
  map_every qid_spec_tac [`sm`,`ops`,`sa`,`suffix`] >>
  Induct >> simp[compile_multi_exprs_def, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  `well_typed_expr env h /\ is_word_type (expr_type h)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all lower_value_word_shape >> strip_tac >>
  `ci_mono cs' (SND (compile_multi_exprs compile_expr cenv suffix cs'))` by
    (irule ci_mono_compile_multi_exprs >> simp[compile_expr_ci_mono]) >>
  gvs[ci_mono_def] >> simp[] >>
  conj_tac >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
              qexists_tac `cs'` >> metis_tac[]) >>
  metis_tac[]
QED

Theorem raw_log_expr_sim_full:
  (!ce ty e. gas_shadow_compiles (lower_value compile_expr ce ty e)
    (lower_value compile_expr ce ty (gas_shadow_expr e))) /\
  (!ce xs. gas_shadow_compiles (compile_multi_exprs compile_expr ce xs)
    (compile_multi_exprs compile_expr ce (MAP gas_shadow_expr xs))) /\
  body_exprs_full_ok cx args /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Call ann RawLog args dflt) es
Proof
  strip_tac >>
  `?a elem bd topics data n.
    args = [Builtin a (MakeArray elem bd) topics; data] /\
    ann = NoneT /\ dflt = NONE /\ LENGTH topics <= 4 /\
    a = ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n) /\ n <= 4 /\
    well_typed_expr env (Builtin a (MakeArray elem bd) topics) /\
    well_typed_expr env data /\
    (expr_type data = BaseT (BytesT (Fixed 32)) \/
     ?m. expr_type data = BaseT (BytesT (Dynamic m)))` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, Once well_typed_expr_def] >> strip_tac >>
     gvs[LENGTH_EQ_NUM_compute] >> Cases_on `h` >> gvs[] >>
     rename1 `Builtin a b topics` >> Cases_on `b` >>
     gvs[expr_type_def, well_typed_expr_def] >> metis_tac[]) >>
  gvs[] >>
  `elem = SOME (BaseT (BytesT (Fixed 32))) /\ bd = Dynamic n /\
   LENGTH topics <= n` by
    (Cases_on `elem` >>
     gvs[well_typed_expr_def, well_typed_builtin_app_def,
         compatible_bound_def, builtin_args_length_ok_def]) >> gvs[] >>
  rewrite_tac[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all raw_log_full_layout_shadow >> strip_tac >>
  `EVERY (\op. (!x. op = Var x ==> not_fresh_at sm x) /\
                 (!l. op <> Label l)) ops` by
    (irule raw_log_topics_operands_shape >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[EVERY_MEM]) >> gvs[] >>
  (irule gas_outcome_full_initial_domain >>
   conj_tac >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
                    storage_trace_frame_read_result] >>
   conj_tac >- first_assum ACCEPT_TAC >>
   disch_tac >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `~cx.txn.is_static` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `H0` mp_tac) >> simp[stmt_state_rel_def, state_rel_def]) >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full cfg ct cx st0 source initial Q R` >>
  `source = bind (eval_exprs cx topics)
     (\vs. bind (bind (eval_expr cx data) (read_result cx))
       (\dv. do bs <- lift_option_type (dest_BytesV dv) "raw_log data";
                type_check (LENGTH vs <= 4) "raw_log too many topics";
                push_log (encode_raw_event_values cx.txn.target vs bs);
                return NoneV od))` by
    (simp[Abbr `source`, FUN_EQ_THM] >> gen_tac >>
     simp[Once evaluate_def] >>
     simp[Once evaluate_def] >>
     simp[Once evaluate_def] >>
     simp[Once evaluate_def] >>
     simp[bind_def, ignore_bind_def, read_result_def,
          return_def, type_check_def, assert_def, lift_option_type_def] >>
     simp[Once evaluate_def, builtin_args_length_ok_def, compatible_bound_def,
          get_accounts_def, evaluate_builtin_def, evaluate_type_def,
          make_array_value_def, lift_sum_def, bind_def, return_def] >>
     Cases_on `eval_exprs cx topics x` >> rename1 `_ = (rr, ee)` >>
     Cases_on `rr` >> simp[read_result_def, return_def, dest_ArrayV_def] >>
     Cases_on `eval_expr cx data ee` >> rename1 `_ = (dr, ds)` >>
     Cases_on `dr` >> simp[] >>
     rename1 `read_result cx tv ds` >>
     Cases_on `read_result cx tv ds` >> rename1 `_ = (vr, ds')` >>
     Cases_on `vr` >> simp[dest_ArrayV_def, return_def] >>
     rename1 `dest_BytesV dv` >> Cases_on `dest_BytesV dv` >>
     simp[return_def, raise_def, read_result_def] >>
     Cases_on `LENGTH x' <= 4` >> simp[read_result_def, return_def]) >>
  mp_tac raw_log_topics_full >>
  (impl_tac >- MATCH_ACCEPT_TAC raw_log_full_data_reached_ready) >>
  disch_then drule_all >>
  disch_then (qspec_then `PG` assume_tac) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (fn th => assume_tac th) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ topicQ topicR` >>
  simp[Abbr `cfg`, Abbr `ct`, Abbr `initial`, Abbr `R`] >>
  qpat_assum `source = _` (fn th => rewrite_tac[th]) >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_values >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_values >> simp[])
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >> reverse conj_tac
      >- (irule storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
      gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts] >> gen_tac >> BETA_TAC >>
      irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_state_updates, storage_trace_frame_return]) >>
  qexists_tac `\H res ee G' tn' t. topicQ H res ee G' tn' t /\
                   ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "continuation" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `topicR`] >> rpt strip_tac >>
  Cases_on `res` >- fs[expr_exit_def] >>
  simp[] >> metis_tac[expr_exit_INR_type])
QED

Resume raw_log_expr_sim_full[continuation]:
  markerLib.RESUME_TAC >> (
  rename1 `compile_multi_exprs compile_expr cenv topics sa = (ops,sm)` >>
  rename1 `compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr topics)
    shadow_sa = (ops,shadow_sm)` >>
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  fs[Abbr `topicQ`] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  `LENGTH vs <= 4` by decide_tac >>
  qexists_tac `vs` >> conj_tac >- first_assum ACCEPT_TAC >>
  BETA_TAC >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ tail_source _ _ _` >>
  `gas_admissible tail_source expr_res_ok mid` by
    (qpat_assum `gas_admissible (bind (eval_exprs cx topics) _) _ es` mp_tac >>
     pure_rewrite_tac[gasContextTheory.gas_admissible_def] >>
     disch_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
     qpat_assum `!tail. eval_exprs cx topics _ = _` (qspec_then `gs` assume_tac) >>
     fs[Abbr `tail_source`, bind_def] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env mid` by fs[expr_body_pre_def] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `!tail. eval_exprs cx topics _ = _`
       (qspec_then `[]` assume_tac) >>
     drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  `storage_trace_frame tail_source` by
    (simp[Abbr `tail_source`] >>
     irule storage_trace_frame_bind_all >> reverse conj_tac
     >- (irule storage_trace_frame_bind_all >>
         simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
     gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_lifts] >> gen_tac >> BETA_TAC >>
     irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
     irule storage_trace_frame_ignore_bind >>
     simp[storage_trace_frame_state_updates, storage_trace_frame_return]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type data) data mid` by
    (qpat_assum `body_expr_full_ok cx data`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [Once body_expr_full_ok_def]) >>
     disch_then drule_all >> metis_tac[]) >>
  FIRST [qpat_assum `expr_type data = BaseT (BytesT (Fixed 32))`
           (K all_tac) >> suspend "fixed_data",
         suspend "dynamic_data"])
QED

Resume raw_log_expr_sim_full[fixed_data]:
  qpat_assum `compile_call _ _ _ _ RawLog _ _ _ = _`
    (mp_then (Pat `compile_call _ _ _ _ RawLog _ _ _ = _`) mp_tac raw_log_fixed_data_full) >>
  disch_then (fn th => qpat_assum `compile_alloc_buffer 32 sm = _`
    (mp_then (Pat `compile_alloc_buffer 32 _ = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `expr_type data = _` (fn eq =>
    qpat_assum `lower_value _ _ _ data sd = _`
      (mp_then (Pat `lower_value _ _ _ data _ = _`) mp_tac (REWRITE_RULE [eq] th)))) >>
  disch_then (drule_at (Pat `lower_value _ _ _ (gas_shadow_expr data) _ = _`)) >>
  disch_then (fn th => qpat_assum `emit_inst MSTORE _ _ sn = _`
    (mp_then (Pat `emit_inst MSTORE _ _ _ = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_inst LOG _ _ s1 = _`
    (mp_then (Pat `emit_inst LOG _ _ _ = _`) mp_tac (REWRITE_RULE [APPEND] th))) >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ (Call _ RawLog _ _) _`)) >>
  disch_then (drule_at (Pat `gas_shadow_function _ _`)) >>
  disch_then (fn th => qpat_assum `expr_type data = _` (fn eq =>
    qpat_assum `expr_sim_full _ _ _ _ data mid`
      (mp_then (Pat `expr_sim_full _ _ _ _ _ _`) mp_tac th o REWRITE_RULE [eq]))) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (fn th => qpat_assum `gas_shadow_state sm shadow_sm`
    (mp_then (Pat `gas_shadow_state _ _`) mp_tac th)) >>
  disch_then (qspecl_then [`t`, `G1`, `tn1`, `st0`, `vs`] mp_tac) >>
  (impl_tac >- (simp[MEM, expr_type_def, loweringPostsTheory.post_value_type_def,
     loweringPostsTheory.expr_has_effect_thm, evaluate_type_def] >>
     rpt conj_tac
     >~ [`local_ptrs_reserved cenv sm`]
     >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
         fs[ci_mono_def])
     >~ [`!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x`]
     >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> fs[ci_mono_def])
     >~ [`!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x`]
     >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> fs[ci_mono_def])
     >~ [`!H. valid_horizon _ _ H _ ==> eval_operands ops t = SOME (MAP event_value_to_word vs)`]
     >- (simp[] >>
         qpat_assum `LIST_REL _ ops vs` mp_tac >>
         qid_spec_tac `vs` >> qid_spec_tac `ops` >>
         Induct >> simp[venomStateTheory.eval_operands_def] >>
         rpt strip_tac >> gvs[] >> first_x_assum drule >>
         disch_then (qspec_then `H` mp_tac) >> simp[])
     >~ [`gas_admissible (bind (eval_expr cx data) (read_result cx)) _ mid`]
     >- (qpat_assum `gas_admissible tail_source _ mid` mp_tac >>
         pure_rewrite_tac[gasContextTheory.gas_admissible_def] >>
         disch_tac >> rpt gen_tac >> strip_tac >>
         Cases_on `res'` >- simp[expr_res_ok_def] >>
         first_x_assum (qspec_then `gs` mp_tac) >>
         simp[Abbr `tail_source`, bind_def] >> metis_tac[])
     >~ [`return_buf_frame d cenv sm t`]
     >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
         qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
         fs[ci_mono_def, loweringPostsTheory.wb_frame_def])
     >~ [`stmt_state_rel H ctx func cenv cx mid t`]
     >- (rpt strip_tac >>
         qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
           (qspec_then `H` mp_tac) >> simp[] >> metis_tac[])
     >~ [`LENGTH vs < dimword (:256)`]
     >- (simp[wordsTheory.dimword_def] >> decide_tac)
     >~ [`post_value_type cenv data = _`]
     >- simp[loweringPostsTheory.post_value_type_word, compileEnvTheory.is_word_type_def])) >>
  simp[Abbr `tail_source`] >> disch_tac >>
  irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
  simp[] >> suspend "fixed_post"
QED

Resume raw_log_expr_sim_full[dynamic_data]:
  `env.type_defs = get_tenv cx /\
   (!id et. FLOOKUP env.var_types id = SOME et ==>
       well_formed_type env.type_defs et)` by
    (qpat_assum `expr_body_pre cenv cx env data mid` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rewrite_tac[expr_body_pre_def, expr_sim_inv_def] >> strip_tac >>
     qpat_x_assum `env_consistent _ _ _` mp_tac >>
     rewrite_tac[env_consistent_def, env_context_consistent_def,
       env_scopes_consistent_def] >> strip_tac >>
     simp[well_formed_type_def] >> metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  `well_formed_type (get_tenv cx) (expr_type data)` by
    metis_tac[exprSafeOperandTheory.well_typed_expr_type_well_formed] >>
  `evaluate_type (get_tenv cx) (expr_type data) =
     SOME (BaseTV (BytesT (Dynamic m)))` by
    (gvs[well_formed_type_def, evaluate_type_def] >> metis_tac[]) >>
  simp[Abbr `tail_source`] >>
  irule gas_outcome_full_post_source >>
  qabbrev_tac `rawlog = Call NoneT RawLog
    [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
      (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics; data] NONE` >>
  qexistsl_tac [
    `\H res ee G tn u. ?v. res = INL v /\
      expr_post H ctx func cenv cx rawlog mid sm sb t ee v (Lit 0w) u /\
      expr_store_bound cx (expr_type rawlog) v (Lit 0w) u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn u /\
      ptr_val_ok cx (post_value_type cenv rawlog) v (Lit 0w) G tn u /\
      (~is_word_type (post_value_type cenv rawlog) ==>
       ptr_buf_ok cenv rawlog (Lit 0w) G u) /\
      ghost_kept_at lo cenv mid sm G1 tn1 t G tn`,
    `\H res ee gt r. expr_exit res r`] >>
  simp[Abbr `rawlog`] >> conj_tac >- suspend "dynamic_post" >>
  simp[expr_type_def] >>
  qpat_assum `LENGTH vs <= (4:num)` (fn bnd =>
    irule (SRULE [bnd, expr_type_def, loweringPostsTheory.post_value_type_def]
      (Q.INST [`vals` |-> `vs`, `ann` |-> `NoneT`, `dflt` |-> `NONE`,
        `data_op` |-> `value`, `len_op` |-> `len`, `ops` |-> `ops`,
        `ptr_op` |-> `ptr'`, `s1` |-> `s1`, `s2` |-> `s2`,
        `shadow_func` |-> `shadow_func`, `shadow_sa` |-> `shadow_sm`,
        `shadow_sm` |-> `shadow_sn`, `sm` |-> `sn`,
        `es_call` |-> `[Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
          (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics; data]`]
        raw_log_dynamic_data_full))) >>
  simp[loweringPostsTheory.post_value_type_bytestring,
    compileEnvTheory.is_bytestring_type_def] >> rpt conj_tac
  >~ [`!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x`]
  >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> fs[ci_mono_def])
  >~ [`!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x`]
  >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> fs[ci_mono_def])
  >~ [`!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t`]
  >- (rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `H` mp_tac) >> simp[] >> metis_tac[])
  >~ [`local_ptrs_reserved cenv sm`]
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def])
  >~ [`gas_admissible (bind (eval_expr cx data) (read_result cx)) _ mid`]
  >- (qpat_assum `gas_admissible (bind (bind _ _) _) _ mid` mp_tac >>
      pure_rewrite_tac[gasContextTheory.gas_admissible_def] >>
      disch_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `res'` >- simp[expr_res_ok_def] >>
      first_x_assum (qspec_then `gs` mp_tac) >> simp[bind_def] >> metis_tac[])
  >~ [`gas_admissible (bind (bind (eval_expr cx data) (read_result cx)) _) _ mid`]
  >- (qpat_assum `LENGTH vs <= (4:num)` (fn bnd =>
      qpat_assum `gas_admissible (bind (bind _ _) _) _ mid`
        (ACCEPT_TAC o REWRITE_RULE [bnd])))
  >~ [`return_buf_frame d cenv sm t`]
  >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
      qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
      fs[ci_mono_def, loweringPostsTheory.wb_frame_def]) >>
  qpat_assum `expr_type data = BaseT (BytesT (Dynamic m))`
    (fn eq => RULE_ASSUM_TAC (REWRITE_RULE [eq])) >>
  qexistsl_tac [`ops`,`shadow_func`,`shadow_sm`,`shadow_sn`] >>
  simp[] >> conj_tac
  >- (simp[] >> qpat_assum `LIST_REL _ ops vs` mp_tac >>
      qid_spec_tac `vs` >> qid_spec_tac `ops` >>
      Induct >> simp[venomStateTheory.eval_operands_def] >>
      rpt strip_tac >> gvs[] >> first_x_assum drule >>
      disch_then (qspec_then `H` mp_tac) >> simp[]) >>
  simp[wordsTheory.dimword_def] >> decide_tac
QED

Resume raw_log_expr_sim_full[fixed_post]:
  qx_genl_tac [`H`,`out_res`,`end_es`,`endG`,`endtn`,`endst`] >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     qpat_assum `LENGTH vs <= 4`
       (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
     drule valid_horizon_frame >>
     disch_then drule >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  gvs[] >> simp[Abbr `Q`] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!tail. eval_exprs cx topics _ = _`
       (qspec_then `[]` assume_tac) >>
     `storage_trace_frame (eval_exprs cx topics)` by
       simp[evaluate_storage_trace_frame] >>
     drule valid_horizon_frame >> disch_then drule >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  fs[ci_mono_def, expr_type_def, loweringPostsTheory.post_value_type_def] >>
  drule_all (SRULE [expr_type_def, loweringPostsTheory.post_value_type_def,
    loweringPostsTheory.expr_has_effect_thm] raw_log_topics_continuation_post) >>
  simp[]
QED

Resume raw_log_expr_sim_full[dynamic_post]:
  qx_genl_tac [`H`,`out_res`,`end_es`,`endG`,`endtn`,`endst`] >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     qpat_assum `LENGTH vs <= 4`
       (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
     drule valid_horizon_frame >>
     disch_then drule >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  gvs[] >> simp[Abbr `Q`] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!tail. eval_exprs cx topics _ = _`
       (qspec_then `[]` assume_tac) >>
     `storage_trace_frame (eval_exprs cx topics)` by
       simp[evaluate_storage_trace_frame] >>
     drule valid_horizon_frame >> disch_then drule >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  fs[ci_mono_def, expr_type_def, loweringPostsTheory.post_value_type_def] >>
  drule_all (SRULE [expr_type_def, loweringPostsTheory.post_value_type_def,
    loweringPostsTheory.expr_has_effect_thm] raw_log_topics_continuation_post) >>
  simp[]
QED

Finalise raw_log_expr_sim_full
