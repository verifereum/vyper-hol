(* Linked sequential simulation for the ExtCall keyword suffix. *)
Theory bodyExtKeywordListFoldMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyExtKeywordHeadRunMods bodyFullShadowBodyInv
  exprLowering compileEnv fragGasOriginPtr wordArgsPtr
  bodyBranchCellFrameMods vyperStorageFootprint exprSimWordArgs
  gasOutcomeFullMods gasOutcomeFullPostMods gasOutcomeFullBindMods
  gasExemptCertMods gasShadow gasContext gasStorage gasOutcome
  exprSimHypsDefs exprSimSource exprLoweringProps bodyInvSplit exprSimDefs
  vyperInterpreter vyperState vyperTypeSystem vyperAST vyperContext
  vyperStorageTrace venomState loweringPosts loweringStateRelDefs bodyPtrDefs
  bodyCallSupport list pair option finite_map arithmetic
  gasShadowCompile gasShadowCompileHelpers gasShadowState
  entryReachBodyFirstEmissionExpr entryReachBodyFirstEmissionExprSupport fragExec
  freshWrites bodyPtrBopRepresentationFrame logValueFramePtr exprSimProps
  valueEncodingProofs ptrDiscipline
Libs horizonTypeLib

val head_outcome = snd (dest_imp (concl extcall_keyword_head_outcome_mods));

val head_rule = ``!e k sa sb shadow_sa shadow_sb op dt es s0 G0 tn0.
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env e es /\
  expr_type e = ext_call_kw_type rt k /\
  compile_ext_call_kwarg compile_expr cenv rt k e sa = ((op,dt),sb) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt k
    (gas_shadow_expr e) shadow_sa = ((op,dt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==> ^head_outcome``;

Theorem ext_kw_inv_gas_obs[local]:
  expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs) <=>
  expr_sim_inv_mods mods cenv cx env es
Proof
  simp[expr_sim_inv_mods_def]
QED

Theorem ext_kw_frame_obs[local]:
  (immutable_frame_mods func cenv cx (es with gas_obs := gs) s <=>
   immutable_frame_mods func cenv cx es s) /\
  (ghost_inv_at_mods D lo d cenv cx (es with gas_obs := gs) G tn s <=>
   ghost_inv_at_mods D lo d cenv cx es G tn s) /\
  (storage_well_formed_on cx (es with gas_obs := gs) A <=>
   storage_well_formed_on cx es A)
Proof
  rpt conj_tac
  >- simp[immutable_frame_mods_def, immutables_rel_mods_def,
          immutables_rel_def, immutable_alloca_sep_mods_def,
          immutable_alloca_sep_def]
  >- simp[ghost_inv_at_mods_def]
  >> irule storage_well_formed_on_backends >> simp[]
QED

Theorem keyword_cons_erased[local]:
  ignore_bind (bind source (\vs. return (v::vs))) (return ()) =
  ignore_bind source (return ())
Proof
  simp[ignore_bind_def, bind_assoc, FUN_EQ_THM, bind_def, return_def] >>
  gen_tac >> Cases_on `source x` >> Cases_on `q` >> simp[]
QED

Theorem keyword_cons_source[local]:
  source s = (res,ee) ==>
  bind source (\vs. return (v::vs)) s = (SUM_MAP (CONS v) I res,ee)
Proof
  Cases_on `res` >> simp[bind_def, return_def, sumTheory.SUM_MAP_def]
QED

Theorem keyword_cons_outcome[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind source (\vs. return (v::vs))) (es,s,G,tn)
    (\H raw ee G tn t. ?res. raw = SUM_MAP (CONS v) I res /\ Q H res ee G tn t)
    (\H raw ee gt r. ?res. raw = SUM_MAP (CONS v) I res /\ R H res ee gt r)
Proof
  `!x. SND (bind source (\vs. return (v::vs)) x) = SND (source x)` by
    (gen_tac >> Cases_on `source x` >> Cases_on `q` >>
     simp[bind_def, return_def]) >>
  disch_then (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  asm_rewrite_tac[gas_outcome_full_mods_def, keyword_cons_erased] >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_bad_storage_at_def] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`SUM_MAP (CONS v) I res`, `ee`, `r`, `G'`, `tn'`] >>
      simp[] >> conj_tac >- (rpt strip_tac >> irule keyword_cons_source >> simp[]) >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem keyword_fold_suffix_mono[local]:
  !ks xs sa. ci_mono sa (SND (compile_ext_call_kwargs compile_expr cenv rt ks xs sa))
Proof
  Induct >> Cases_on `xs` >> rpt strip_tac >>
  simp[compile_ext_call_kwargs_def, ci_mono_comp_return] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_ext_call_kwarg, cj 1 compile_expr_ci_mono] >>
  rpt strip_tac >> simp[UNCURRY] >>
  ho_match_mp_tac ci_mono_bind >> simp[UNCURRY, ci_mono_comp_return]
QED

Theorem ext_kw_list_run_with_head_mods:
  ^head_rule ==>
  body_exprs_full_ok_mods mods exps cx xs /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_sim_inv_mods mods cenv cx env es /\
  (!e st. MEM e xs /\
    expr_sim_inv_mods mods cenv cx env st ==>
      expr_body_pre_mods mods cenv cx env e st) /\
  MAP expr_type xs = MAP (ext_call_kw_type rt) ks /\
  compile_ext_call_kwargs compile_expr cenv rt ks xs sa = ((vo,go,dopt),sb) /\
  compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) rt ks
    (MAP gas_shadow_expr xs) shadow_sa = ((vo,go,dopt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==>
    dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    mods cx st0 (eval_exprs cx xs) (es,s0,G0,tn0)
    (\H res ee G tn t. ?vs. res = INL vs /\ LENGTH vs = LENGTH xs /\
      expr_sim_inv_mods mods cenv cx env ee /\
      body_const_cells_agree_mods mods cx env ee /\
      stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ~t.vs_halted /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      return_buf_frame d cenv sb t /\
      wb_frame cenv es ee sa s0 t /\
      MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
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
           else dt = lowered_value_type cenv e /\
             ptr_val_ok cx dt v op G tn t /\
             ptr_mem_ok cx dt v op G tn t /\
             ptr_buf_ok cenv e op G t /\
             (!w. eval_operand op t = SOME w /\
               type_memory_bytes cenv dt <> 0 ==>
               w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next) /\
             (?w aid tv. eval_operand op t = SOME w /\
               evaluate_type (get_tenv cx) dt = SOME tv /\ val_wf tv v /\
               FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
               aid < sb.cs_next_id)))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (mk_asm "head") >>
  map_every qid_spec_tac
    [`tn0`,`G0`,`s0`,`es`,`shadow_sb`,`shadow_sa`,`sb`,`sa`,`dopt`,`go`,`vo`,`ks`] >>
  Induct_on `xs` >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS)
  >- (gvs[compile_ext_call_kwargs_def, comp_return_def] >>
      irule (Q.INST [`res` |-> `INL ([] : value list)`, `ee` |-> `es`,
                    `t` |-> `s0`, `G'` |-> `G0`, `tn'` |-> `tn0`]
        (INST_TYPE [alpha |-> ``:value list``] gas_outcome_full_mods_pure)) >>
      simp[evaluate_def, return_def] >>
      qexistsl [`G0`, `s0`, `tn0`] >>
      simp[gas_origin_ptr_path_rules, ghost_kept_at_refl,
           ext_call_kwarg_def, immutable_frame_mods_def,
           body_exprs_full_ok_mods_def] >>
      qx_gen_tac `H` >> strip_tac >>
      qpat_x_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
        (qspec_then `H` mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      `expr_sim_inv_mods mods cenv cx env (es with gas_obs := [])` by
        simp[ext_kw_inv_gas_obs] >>
      `immutable_frame_mods func cenv cx (es with gas_obs := []) s0` by
        simp[ext_kw_frame_obs] >>
      `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
        simp[ext_kw_frame_obs] >>
      `ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G0 tn0 s0` by
        simp[ext_kw_frame_obs] >>
      `wb_frame cenv es (es with gas_obs := []) sa s0 s0` by
        (irule wb_frame_refl >> simp[]) >>
      qpat_assum `immutable_frame_mods _ _ _ (es with gas_obs := []) _`
        (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def]) >>
      simp[] >> metis_tac[])
  >- suspend "cons"
QED

Resume ext_kw_list_run_with_head_mods[cons]:
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
  Cases_on `compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt k
    (gas_shadow_expr e) shadow_sa` >>
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
  Cases_on `compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) rt ks
    (MAP gas_shadow_expr xs) shadow_sm` >>
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
  qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fn_has_code_split >>
  simp[] >> strip_tac >>
  qspecl_then [`shadow_sa`,`shadow_sm`,`shadow_sb`,`shadow_func`] mp_tac fn_has_code_split >>
  simp[] >> strip_tac >>
  gvs[body_exprs_full_ok_mods_def] >>
  `expr_body_pre_mods mods cenv cx env e es` by simp[] >>
  asm_x "head" (qspecl_then [`e`,`k`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
                            `op`,`dt`,`es`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (assume_tac o BETA_RULE) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _
      (bind (eval_expr cx e) (read_result cx)) _ headQ _` >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >>
  rpt conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return])
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> fs[keyword_cons_erased])
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qexists_tac `headQ` >> conj_tac
  >- suspend "tail"
  >- fs[halt_exit_def, INST_TYPE [alpha |-> ``:value list``, beta |-> ``:value``]
                       stmtSimPropsTheory.expr_exit_INR_type]
QED

Resume ext_kw_list_run_with_head_mods[tail]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  disj1_tac >> qunabbrev_tac `headQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `v` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  qexists_tac `v` >> simp[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _`
      (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))) >>
  `body_exprs_full_ok_mods mods exps cx xs` by
    (drule_then strip_assume_tac (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >>
     qpat_x_assum `(?s tv t s1 v t1. _ /\ _) ==> body_exprs_full_ok_mods _ _ _ xs`
       irule >> goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `ci_mono sa sm` by
    (qspecl_then [`compile_expr`,`cenv`,`rt`,`k`,`e`,`sa`] mp_tac
      ci_mono_compile_ext_call_kwarg >> simp[cj 1 compile_expr_ci_mono]) >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `!ks' vo' go' dopt' sa' sb' shadow_sa' shadow_sb' es' s0' G0' tn0'.
      _ ==> gas_outcome_full_mods _ _ _ _ (eval_exprs cx xs) _ _ _`
    (qspecl_then [`ks`,`vot`,`got`,`dopt_t`,`sm`,`sb`,`shadow_sm`,`shadow_sb`,
                  `mid`,`t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >-
    (`(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
       metis_tac[not_fresh_at_mono] >>
     simp[] >> conj_tac
     >- (rpt strip_tac >> qpat_assum `!fn inst u. frag_reachable ctx func t fn inst u ==> _`
           (drule_then ACCEPT_TAC)) >>
     qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[])) >>
  disch_then (assume_tac o MATCH_MP keyword_cons_outcome) >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_exprs cx xs) _) _ _ _`
    (irule_at Any) >> BETA_TAC >>
  reverse conj_tac
  >- (rpt gen_tac >> disch_then (qx_choose_then `orig` strip_assume_tac) >>
      Cases_on `orig` >> gvs[sumTheory.SUM_MAP_def,expr_exit_def,halt_exit_def]) >>
  suspend "transport"
QED

Resume ext_kw_list_run_with_head_mods[transport]:
  qx_genl_tac [`H`,`out`,`ee`,`G2`,`tn2`,`u`] >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss []) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (`valid_horizon cx st0 H (mid with gas_obs := xs').storage_trace` suffices_by simp[] >>
     qpat_assum `!tail. bind (eval_exprs cx xs) _ _ = _`
       (qspec_then `[]` (mp_then Any mp_tac valid_horizon_frame)) >>
     simp[] >> disch_then irule >>
     simp[] >> irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`valid_horizon cx st0 H
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings).storage_trace` suffices_by simp[] >>
     qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (INL v,_)`
       (mp_then Any mp_tac valid_horizon_frame) >>
     simp[] >> disch_then irule >>
     simp[] >> irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `ci_mono sm sb` by
    (qspecl_then [`ks`,`xs`,`sm`] mp_tac keyword_fold_suffix_mono >> simp[]) >>
  `sa.cs_next_id <= sm.cs_next_id /\
   sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id` by fs[ci_mono_def] >>
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
  qpat_assum `wb_frame cenv es ee sa s0 u`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (irule LESS_EQ_TRANS >> qexists_tac `t.vs_alloca_next` >> simp[]) >>
  qexists_tac `v::vs` >> simp[sumTheory.SUM_MAP_def] >>
  suspend "selected"
QED

Resume ext_kw_list_run_with_head_mods[selected]:
  `!w. eval_operand op t = SOME w ==> eval_operand op u = SOME w` by
    (Cases_on `op` >> simp[venomStateTheory.eval_operand_def] >>
     rpt strip_tac >>
     qpat_assum `!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==> _` irule >>
     simp[]) >>
  `op_taint tn2 op = op_taint tn1 op /\ op_prov G2 op = op_prov G1 op` by
    (Cases_on `op` >> simp[ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >>
     rename1 `_ /\ FLOOKUP G2 x = FLOOKUP G1 x` >>
     qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2`
       (qspec_then `x` mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
     simp[ptrDisciplineTheory.op_taint_def]) >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  reverse (Cases_on `k = EKDefault`)
  >- (Cases_on `k` >> gvs[ext_call_kwarg_def] >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[ext_call_kwarg_def] >>
  Cases_on `is_word_type rt` >> gvs[]
  >- (fs[expr_val_rel_def, bodyPtrDefsTheory.ptr_val_ok_def] >> metis_tac[]) >>
  suspend "owned"
QED

Resume ext_kw_list_run_with_head_mods[owned]:
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

Finalise ext_kw_list_run_with_head_mods
