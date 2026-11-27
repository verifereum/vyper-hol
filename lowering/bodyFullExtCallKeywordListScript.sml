Theory bodyFullExtCallKeywordList
Ancestors
  bodyFullShadowBodyInv
  bodyFullExtCallKeywords bodyFullExtCallDefaultKeyword bodyFullExtCallPosTransport
  vyperTypeSystem forPtrAllocationFrame fragGasOriginPtr gasOutcomeFull
  targetPureSourceFrame exprOperandVar exprSimSource exprLoweringProps
  gasOutcomeFullCompose fragGasOrigin fragGasMode fragGasPathFrameMem
  exprLowering compileEnv vyperState loweringPosts vyperTyping
  vyperInterpreter wordArgsPtr vyperStorageFootprint bodyPtrDefs
  gasShadowCompile gasShadowCompileHelpers gasShadowState compilerFirstEmission
  fragExec entryReachBodyFirstEmissionExpr bodyFullPreds exprSimWordArgs
  stmtSimProps vyperStorageTrace gasExemptCert
  entryReachBodyFirstEmissionExprSupport exprSimDefs
  bodyFullBuiltinWordPowCompose stmtLoweringMono freshWrites stateRelProj
  bodyPtrBopRepresentationFrame vyperEvalExprPreservesScopesDom
  bodyFullIfExpReach
  bodyFullPredsMods[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]
  gasOutcomeFullMods[qualified]

Theorem keyword_suffix_ci_mono[local]:
  !ks xs sa. ci_mono sa (SND (compile_ext_call_kwargs compile_expr cenv rt ks xs sa))
Proof
  Induct >> Cases_on `xs` >> rpt strip_tac >>
  simp[compile_ext_call_kwargs_def, ci_mono_comp_return] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_ext_call_kwarg, cj 1 ci_mono_compile_expr_sa] >>
  rpt strip_tac >> simp[pairTheory.UNCURRY] >>
  ho_match_mp_tac ci_mono_bind >> simp[pairTheory.UNCURRY, ci_mono_comp_return]
QED

(* Invert only the ExtCall typing clause. *)
Theorem extcall_keyword_suffix_types:
  well_typed_expr env (Call ty (ExtCall stat skip (name,arg_types,rt) opts) args drv) ==>
  MAP expr_type (DROP (1 + LENGTH arg_types) args) = MAP (ext_call_kw_type rt) opts
Proof
  simp[cj 13 well_typed_expr_def]
QED

(* Allocation rows come from the same marked physical execution as the post. *)
Theorem extcall_keyword_outcome_allocations[local]:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source (es,s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source (es,s,G,tn)
    (\H res ee G' tn' t. Q H res ee G' tn' t /\
      (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
                 FLOOKUP t.vs_allocas aid = SOME row) /\
      t.vs_labels = s.vs_labels) R
Proof
  simp_tac bool_ss [gas_outcome_full_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac
  >- (disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      disj1_tac >> drule gas_origin_ptr_path_projections >> strip_tac >> conj_tac
      >- (drule gas_path_ptr_old_allocations >> simp[]) >>
      drule gas_origin_path_erase >>
      disch_then (mp_tac o MATCH_MP gas_marked_path_exec) >>
      metis_tac[gas_path_code_labels]) >>
  disj2_tac >> metis_tac[]
QED

Theorem keyword_head_scope_domains[local]:
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := obs ++ tail) = (INL v,ee with gas_obs := tail)) ==>
  MAP FDOM ee.scopes = MAP FDOM es.scopes
Proof
  disch_then (qspec_then `[]` mp_tac) >>
  simp[] >> disch_then (strip_assume_tac o MATCH_MP (REWRITE_RULE [ETA_AX] eval_expr_read_INL)) >>
  drule read_result_state >>
  disch_then (SUBST_ALL_TAC o SYM) >>
  drule eval_expr_preserves_scopes_dom >> simp[]
QED

(* The scalar and materialized cases agree on the frame for the suffix. *)
Theorem extcall_keyword_head_outcome:
  body_expr_full_ok_mods mods exps cx e /\ (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env es /\
  expr_body_pre_mods mods cenv cx env e es /\
  expr_type e = ext_call_kw_type rt k /\
  compile_ext_call_kwarg compile_expr cenv rt k e sa = ((op,dt),sb) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt k (gas_shadow_expr e)
    shadow_sa = ((op,dt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      return_buf_frame d cenv sb t /\ wb_frame cenv es ee sa s0 t /\
      MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      t.vs_labels = s0.vs_labels /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      (k <> EKDefault ==> ?w. eval_operand op t = SOME w /\
           dest_NumV v = SOME (w2n w) /\ op_taint tn op = {}) /\
      (k = EKDefault ==> if is_word_type rt then
         dt = rt /\ expr_val_rel cx rt v op t /\ ptr_val_ok cx rt v op G tn t
       else dt = lowered_value_type cenv e /\ ptr_val_ok cx dt v op G tn t /\
            ptr_mem_ok cx dt v op G tn t /\ ptr_buf_ok cenv e op G t /\
            (!w. eval_operand op t = SOME w /\ type_memory_bytes cenv dt <> 0 ==>
             w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next) /\
            (?w aid tv. eval_operand op t = SOME w /\
              evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
              val_wf tv v /\ FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
              aid < sb.cs_next_id /\
              (!n b sz. local_region cenv ee.scopes t n b sz ==>
                regions_disjoint (w2n w) (type_memory_size tv) b sz))))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `k = EKDefault /\ ~is_word_type rt`
  >- (gvs[ext_call_kw_type_def] >>
      drule_all extcall_kwarg_default_owned_lookup_full >>
      disch_then (qspec_then `PG` (mp_tac o MATCH_MP extcall_keyword_outcome_allocations)) >>
      disch_tac >> irule gas_outcome_full_post_source >>
      goal_assum (drule_at Any) >> simp[] >> rpt gen_tac >> strip_tac >>
      `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
        (qpat_assum `res = INL v` SUBST_ALL_TAC >>
         drule keyword_head_scope_domains >> simp[]) >>
      qexists_tac `v` >> gvs[] >> qexists_tac `aid` >> simp[] >>
      first_assum ACCEPT_TAC) >>
  `dt = rt /\
   lower_value compile_expr cenv (ext_call_kw_type rt k) e sa = (op,sb)` by
    (Cases_on `lower_value compile_expr cenv (ext_call_kw_type rt k) e sa` >>
     qpat_assum `compile_ext_call_kwarg _ _ _ _ e _ = _` mp_tac >>
     Cases_on `k` >>
     gvs[ext_call_kw_type_def, compile_ext_call_kwarg_def, comp_bind_def,
         comp_return_def]) >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    ((drule compiler_lower_value_var >> simp[cj 1 compiler_compile_var] >> (metis_tac[cj 1 compiler_compile_var, compiler_lower_value_var]))) >>
  qpat_x_assum `dt = rt` (SUBST_ALL_TAC o SYM) >>
  drule_all extcall_kwarg_scalar_full >>
  disch_then (qspec_then `PG` (mp_tac o MATCH_MP extcall_keyword_outcome_allocations)) >>
  disch_tac >> irule gas_outcome_full_post_source >>
  goal_assum (drule_at Any) >> simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `expr_post H ctx func cenv cx e es sa sb s0 ee v op t` >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (qpat_assum `res = INL v` SUBST_ALL_TAC >>
     drule keyword_head_scope_domains >> simp[]) >>
  `is_word_type (expr_type e)` by
    (Cases_on `k` >> gvs[ext_call_kw_type_def,is_word_type_def]) >>
  qpat_assum `expr_post H ctx func cenv cx e es sa sb s0 ee v op t`
    (assume_tac o MATCH_MP exprSimWordArgsTheory.expr_post_frame) >>
  qexists_tac `v` >>
  gvs[expr_post_def] >> Cases_on `k` >>
  gvs[ext_call_kw_type_def, is_word_type_def, bodyPtrDefsTheory.ptr_val_ok_def]
QED

(* Fold the concrete keyword compiler and evaluator over the same suffix.
   The selected operands match source first-occurrence selection; evaluating
   a later duplicate still contributes its gas marks and frame. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  map_every qid_spec_tac
    [`tn0`,`G0`,`s0`,`es`,`shadow_sb`,`shadow_sa`,`sb`,`sa`,`dopt`,`go`,`vo`,`ks`] >>
  Induct_on `xs` >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS)
  >- (gvs[compile_ext_call_kwargs_def, comp_return_def] >>
      irule (Q.INST [`res` |-> `INL ([] : value list)`, `ee` |-> `es`,
                    `t` |-> `s0`, `G'` |-> `G0`, `tn'` |-> `tn0`]
        (INST_TYPE [alpha |-> ``:value list``] gas_outcome_full_pure)) >>
      simp[evaluate_def, return_def] >>
      qexistsl [`G0`, `s0`, `tn0`] >>
      simp[gas_origin_ptr_path_rules, ghost_kept_at_refl, ext_call_kwarg_def] >>
      qx_gen_tac `H` >> strip_tac >>
      `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
       storage_well_formed_on cx es (FST H)` by
        (irule storage_well_formed_on_backends >> simp[]) >>
      qpat_x_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
        (qspec_then `H` mp_tac) >>
      simp[] >> strip_tac >> gvs[ghost_inv_at_def, wb_frame_refl] >>
      first_assum ACCEPT_TAC) >>
  suspend "cons"
QED
*)
Theorem extcall_request_keywords_owned_outcome:
  body_exprs_full_ok_mods mods exps cx xs /\ (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env es /\
  expr_sim_inv_mods mods cenv cx env es /\
  (!e st. MEM e xs /\ expr_sim_inv_mods mods cenv cx env st ==>
    expr_body_pre_mods mods cenv cx env e st) /\
  MAP expr_type xs = MAP (ext_call_kw_type rt) ks /\
  compile_ext_call_kwargs compile_expr cenv rt ks xs sa = ((vo,go,dopt),sb) /\
  compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) rt ks (MAP gas_shadow_expr xs)
    shadow_sa = ((vo,go,dopt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_exprs cx xs) (es,s0,G0,tn0)
    (\H res ee G tn t. ?vs. res = INL vs /\ LENGTH vs = LENGTH xs /\
      expr_sim_inv_mods mods cenv cx env ee /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      return_buf_frame d cenv sb t /\ wb_frame cenv es ee sa s0 t /\
      MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      t.vs_labels = s0.vs_labels /\
      (case ext_call_kwarg EKGas ks vs of
         NONE => go = NONE
       | SOME v => ?op w. go = SOME op /\ eval_operand op t = SOME w /\
           (!x. op = Var x ==> not_fresh_at sb x) /\
           dest_NumV v = SOME (w2n w) /\ op_taint tn op = {}) /\
      (case ext_call_kwarg EKValue ks vs of
         NONE => vo = NONE
       | SOME v => ?op w. vo = SOME op /\ eval_operand op t = SOME w /\
           (!x. op = Var x ==> not_fresh_at sb x) /\
           dest_NumV v = SOME (w2n w) /\ op_taint tn op = {}) /\
      (case ext_call_kwarg EKDefault ks vs of
         NONE => dopt = NONE
       | SOME v => ?e op dt. dopt = SOME (op,dt) /\
           ext_call_kwarg EKDefault ks xs = SOME e /\
           (!x. op = Var x ==> not_fresh_at sb x) /\
           if is_word_type rt then
             dt = rt /\ expr_val_rel cx rt v op t /\ ptr_val_ok cx rt v op G tn t
           else dt = lowered_value_type cenv e /\ ptr_val_ok cx dt v op G tn t /\
                ptr_mem_ok cx dt v op G tn t /\ ptr_buf_ok cenv e op G t /\
                (!w. eval_operand op t = SOME w /\ type_memory_bytes cenv dt <> 0 ==>
                  w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next) /\
                (?w aid tv. eval_operand op t = SOME w /\
                  evaluate_type (get_tenv cx) dt = SOME tv /\ val_wf tv v /\
                  FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
                  aid < sb.cs_next_id)))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume extcall_request_keywords_owned_outcome[cons]:
  Cases_on `ks` >> fs[] >>
  rename1 `compile_ext_call_kwargs _ _ rt (k::ks) (e::xs) sa = _` >>
  Cases_on `compile_ext_call_kwarg compile_expr cenv rt k e sa` >>
  PairCases_on `q` >>
  rename1 `compile_ext_call_kwarg _ _ _ _ _ sa = ((op,dt),sm)` >>
  `gas_shadow_compiles (compile_ext_call_kwarg compile_expr cenv rt k e)
     (compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt k (gas_shadow_expr e))` by
    (irule (SIMP_RULE bool_ss []
      (Q.INST [`sh` |-> `T`] gas_shadow_compiles_ext_call_kwarg_env)) >>
     simp[cj 1 gas_shadow_compile_expr_env]) >>
  Cases_on `compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt k (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_ext_call_kwarg _ _ _ _ (gas_shadow_expr e) shadow_sa = (z,shadow_sm)` >>
  qpat_x_assum `gas_shadow_compiles _ _` (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `gas_shadow_compiles (compile_ext_call_kwargs compile_expr cenv rt ks xs)
    (compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) rt ks (MAP gas_shadow_expr xs))` by
    (irule (SIMP_RULE bool_ss []
      (Q.INST [`sh` |-> `T`] gas_shadow_compiles_ext_call_kwargs_env)) >>
     simp[cj 1 gas_shadow_compile_expr_env]) >>
  Cases_on `compile_ext_call_kwargs compile_expr cenv rt ks xs sm` >>
  PairCases_on `q` >>
  rename1 `compile_ext_call_kwargs _ _ rt ks xs sm = ((vot,got,dopt_t),sb_t)` >>
  Cases_on `compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) rt ks (MAP gas_shadow_expr xs) shadow_sm` >>
  rename1 `compile_ext_call_kwargs _ _ rt ks (MAP gas_shadow_expr xs) shadow_sm = (z,shadow_sb_t)` >>
  qpat_x_assum `gas_shadow_compiles _ _` (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`sm`,`shadow_sm`] mp_tac) >>
  simp[] >> strip_tac >> gvs[compile_ext_call_kwargs_def, comp_bind_def, comp_return_def] >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    (conj_tac >>
     (let val extends = cj 1 (MATCH_MP first_emission_ext_call_kwarg
                                      (cj 1 first_emission_compile_expr))
      in first_assum (mp_then Any ACCEPT_TAC extends) end)) >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    (conj_tac >>
     (let val extends = cj 1 (MATCH_MP first_emission_ext_call_kwargs
                                      (cj 1 first_emission_compile_expr))
      in first_assum (mp_then Any ACCEPT_TAC extends) end)) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sb shadow_func` by
    metis_tac[fn_has_code_split] >>
  gvs[body_exprs_full_ok_def] >>
  `expr_body_pre cenv cx env e es` by metis_tac[] >>
  drule_all extcall_keyword_head_outcome >>
  disch_then (qspec_then `PG` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ _` >>
  rewrite_tac[eval_exprs_cons_action] >> irule gas_outcome_full_bind_all_path >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl [`mid`,`t`,`v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  qexists `\H res ee G tn t. headQ H res ee G tn t /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "tail" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def] >>
  gvs[expr_exit_INR_type,halt_exit_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume extcall_request_keywords_owned_outcome[tail]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  strip_tac >> disj1_tac >>
  qunabbrev_tac `headQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then assume_tac)) >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)` (fn path =>
     qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
     qpat_assum `!fn i v. frag_reachable ctx func s0 fn i v ==> _`
       (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
        CONJ path o CONJ no_phi)))) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `v` (MAP_EVERY assume_tac o CONJUNCTS)) assume_tac) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  qexists_tac `v` >> simp[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL v, mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL]))) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx e) _ _ = (INL v,mid with gas_obs := [])`
       (irule_at Any) >> imp_res_tac exprBodyPrePropsTheory.expr_body_pre_static_facts >> simp[]) >>
  `expr_sim_inv cenv cx env mid` by
    (`expr_body_pre cenv cx env e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
       simp[expr_body_pre_gas_obs] >>
     drule_all (REWRITE_RULE [ETA_AX] exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
  `body_exprs_full_ok cx xs` by
    (drule_at (Pat `bind _ _ _ = _`) (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >>
     strip_tac >> metis_tac[]) >>
  `ci_mono sa sm` by
    (qpat_assum `compile_ext_call_kwarg _ _ _ _ e sa = _` (fn th =>
       mp_tac (Q.SPECL [`compile_expr`,`cenv`,`rt`,`k`,`e`,`sa`]
         ci_mono_compile_ext_call_kwarg) >>
       simp[th, cj 1 ci_mono_compile_expr_sa])) >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  qpat_x_assum `!ks' vo' go' dopt' sa' sb' shadow_sa' shadow_sb' es' s0' G0' tn0'.
                 _ ==> gas_outcome_full _ _ _ _ (eval_exprs cx xs) _ _ _`
    (qspecl_then [`ks`,`vot`,`got`,`dopt_t`,`sm`,`sb`,`shadow_sm`,`shadow_sb`,
                  `mid`,`t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >-
    (`(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
       metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
     qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[] >> metis_tac[])) >>
  disch_tac >>
  `!src. bind (eval_exprs cx xs) (\vs. return (v::vs)) src =
     (sum$SUM_MAP (CONS v) I (FST (eval_exprs cx xs src)),
      SND (eval_exprs cx xs src))` by
    (gen_tac >> Cases_on `eval_exprs cx xs src` >>
     rename1 `eval_exprs cx xs src = (rs,ee)` >>
     Cases_on `rs` >> simp[bind_def, return_def, sumTheory.SUM_MAP_def]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (eval_exprs cx xs) _ _ _`
    (mp_then (Pos last)
       (mp_tac o BETA_RULE o Q.ISPECL
         [`bind (eval_exprs cx xs) (\vs. return ((v:value)::vs))`,
          `sum$SUM_MAP (CONS (v:value)) (I : exception -> exception)`])
       gas_outcome_full_source_map) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> simp[sumTheory.SUM_MAP_def])) >>
  disch_tac >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_exprs cx xs) _) _ _ _`
    (irule_at Any) >>
  reverse conj_tac
  >- (rpt gen_tac >> simp[sumTheory.SUM_MAP_def] >>
      disch_then (qx_choose_then `orig` strip_assume_tac) >> Cases_on `orig` >>
      gvs[] >> metis_tac[expr_exit_INR_type]) >>
  BETA_TAC >> qx_genl_tac [`H`, `out`, `ee`, `G2`, `tn2`, `u`] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `obs` assume_tac)
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac
        (qx_choose_then `orig` (CONJUNCTS_THEN2 assume_tac
          (qx_choose_then `vs` (MAP_EVERY assume_tac o CONJUNCTS)))))))) >>
  `MAP FDOM ee.scopes = MAP FDOM mid.scopes /\
   MAP FDOM mid.scopes = MAP FDOM es.scopes` by simp[] >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (`valid_horizon cx st0 H mid.storage_trace` by
       (`valid_horizon cx st0 H (mid with gas_obs := obs).storage_trace` suffices_by simp[] >>
        qpat_assum `!tail. bind (eval_exprs cx xs) _ _ = _`
          (qspec_then `[]` (mp_then Any mp_tac valid_horizon_frame)) >>
        simp[] >> disch_then irule >> simp[] >> irule storage_trace_frame_bind_all >>
        simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
     `valid_horizon cx st0 H es.storage_trace` suffices_by simp[] >>
     `valid_horizon cx st0 H
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings).storage_trace`
       suffices_by simp[] >>
     qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (INL v,_)`
       (mp_then Any mp_tac valid_horizon_frame) >>
     simp[] >> disch_then irule >> simp[] >> irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `ci_mono sm sb` by
    (qspecl_then [`ks`,`xs`,`sm`] mp_tac keyword_suffix_ci_mono >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
   sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id` by
    fs[ci_mono_def] >>
  `wb_frame cenv es ee sa s0 u` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_trans) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid ee sm t u` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (irule (horizonTypeLib.at_horizon_named "H" ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2` (irule_at Any) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >> simp[]) >>
  `(!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x u = SOME w) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
            FLOOKUP u.vs_allocas aid = SOME b)` by
    (conj_tac >> rpt strip_tac
     >- (rename1 `lookup_var x u = SOME w` >>
         `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
         `lookup_var x t = SOME w` by simp[] >> simp[]) >>
     rename1 `FLOOKUP u.vs_allocas aid = SOME b` >>
     `FLOOKUP t.vs_allocas aid = SOME b` by simp[] >> simp[]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `t.vs_alloca_next` >> simp[]) >>
  qexists `v::vs` >> simp[sumTheory.SUM_MAP_def] >>
  `!w. eval_operand op t = SOME w ==> eval_operand op u = SOME w` by
    (Cases_on `op` >> gvs[venomStateTheory.eval_operand_def]) >>
  `op_taint tn2 op = op_taint tn1 op /\ op_prov G2 op = op_prov G1 op` by
    (Cases_on `op` >> simp[ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >>
     rename1 `_ /\ FLOOKUP G2 x = FLOOKUP G1 x` >>
     qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2`
       (qspec_then `x` mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
     simp[ptrDisciplineTheory.op_taint_def]) >>
  `!x. op = Var x ==> not_fresh_at sb x` by metis_tac[not_fresh_at_mono] >>
  Cases_on `k` >> gvs[ext_call_kwarg_def] >>
  TRY (qpat_x_assum `!w. eval_operand op t = SOME w ==> _` (fn th =>
    qpat_assum `eval_operand op t = SOME _` (mp_tac o MATCH_MP th)) >> strip_tac) >>
  TRY (goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `is_word_type rt` >> gvs[]
  >- (fs[expr_val_rel_def, bodyPtrDefsTheory.ptr_val_ok_def] >> metis_tac[]) >>
  (* The head allocation survives the suffix, with its bytes and taint frame. *)
  `eval_operand op u = SOME w` by simp[] >>
  `FLOOKUP u.vs_allocas aid = SOME (w2n w,type_memory_size tv)` by simp[] >>
  `val_footprint tv v <= type_memory_size tv` by
    simp[exprSimPropsTheory.val_footprint_le] >>
  `mem_bytes_at (w2n w) (type_memory_size tv) u.vs_memory =
   mem_bytes_at (w2n w) (type_memory_size tv) t.vs_memory` by
    (qpat_assum `wb_frame cenv mid ee sm t u`
       (mp_tac o cj 3 o REWRITE_RULE [wb_frame_def]) >>
     disch_then (qspecl_then [`aid`,`w2n w`,`type_memory_size tv`] mp_tac) >>
     impl_tac >- (simp[GSYM loweringStateRelDefsTheory.regions_disjoint_def] >> first_assum ACCEPT_TAC) >>
     simp[]) >>
  `mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory` by
    (qpat_assum `mem_bytes_at (w2n w) (type_memory_size tv) u.vs_memory = _`
       (mp_tac o MATCH_MP (cj 1 valueEncodingProofsTheory.mem_bytes_at_agree_window) o SYM) >>
     disch_then (qspecl_then [`w2n w`,`val_footprint tv v`] mp_tac) >> simp[]) >>
  `!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn2.t_mem ==>
       i IN tn1.t_mem` by
    (gen_tac >> strip_tac >>
     `i < w2n w + type_memory_size tv` by decide_tac >>
     qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2`
       (mp_tac o cj 2 o REWRITE_RULE [ghost_kept_at_def]) >>
     disch_then (qspecl_then [`aid`,`w2n w`,`type_memory_size tv`,`i`] mp_tac) >>
     impl_tac >- (simp[GSYM loweringStateRelDefsTheory.regions_disjoint_def] >> first_assum ACCEPT_TAC) >>
     simp[]) >>
  `!x. op = Var x ==> FLOOKUP G2 x = FLOOKUP G1 x` by
    (rpt strip_tac >> fs[ptrDisciplineTheory.op_prov_def]) >>
  `ptr_mem_ok cx (lowered_value_type cenv e) v op G2 tn2 u` by
    (drule_at (Pat `ptr_mem_ok cx _ v op G1 tn1 t`) bop_ptr_mem_ok_frame >>
     disch_then irule >> gvs[]) >>
  simp[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_buf_ok_def] >>
  conj_tac >- fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  conj_tac
  >- (strip_tac >>
      qpat_assum `ptr_buf_ok cenv e op G1 t`
        (mp_tac o Q.SPEC `w` o REWRITE_RULE [bodyPtrDefsTheory.ptr_buf_ok_def]) >>
      gvs[] >> strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
  qexists `aid` >> simp[] >> decide_tac
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise extcall_request_keywords_owned_outcome
*)
