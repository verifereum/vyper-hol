(* The selected omitted defaults reach a replayable grouped initializer endpoint. *)
Theory linkedGroupedRejectSeed
Ancestors linkedGroupedKeywordInitialize linkedGroupedDefaultOutcome
  linkedDefaultSourceFrame groupedDefaultCode groupedDefaultEvaluation
  bodyFullPreds bodyFullPredsMods bodyFullShadowBodyInv bodyInvSplit
  exprSimProps exprBodyPreProps exprSimHypsDefs gasShadowCompileBase
  gasShadowState gasShadow gasOutcomeFullMods fragGasOriginPtr fragExec
  vyperInterpreter vyperState vyperStorageFootprint vyperStorageTrace
  vyperTypeContract ptrDiscipline compileEnv exprLoweringProps compileVyper
  gasSummary loweringStateRelDefs bodyPtrDefs venomState list pair finite_map words
  rich_list exprBodyPreCallSafetyProps fragFuel
Libs groupedRejectSlotsLib

val _ = Parse.hide "tops";

Theorem row22_omitted_seed_path_mods:
    compile_init_kwargs ce vars off 0 hi sa = ((),sb) /\
    compile_init_kwargs (gas_shadow_env T ce)
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars)
      off 0 hi sha = ((),shb) /\
    fn_has_code sa sb fn /\ fn_has_code sha shb shfn /\ gas_shadow_state sa sha /\
    LIST_REL (\(n,dst,ty,e) (aid,p,base,tv).
      dst = Var p /\ runtime_constant_expr mods e /\ expr_type e = ty /\
      (!es'. expr_sim_inv_mods mods (ce with ce_vars := FEMPTY) cx env es' ==>
        expr_body_pre_mods mods (ce with ce_vars := FEMPTY) cx env e es') /\
      lower_value compile_expr (ce with ce_vars := FEMPTY) ty e =
        lower_value compile_expr ce ty e /\
      lower_value compile_expr (gas_shadow_env T (ce with ce_vars := FEMPTY))
        ty (gas_shadow_expr e) =
        lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      type_memory_bytes ce ty = type_memory_size tv /\
      type_memory_size tv + 64 < dimword (:256)) vars slots /\
    EVERY (^row22_kw_alloc sa s G tn) slots /\
    EVERY (^row22_kw_initialized sa s G tn) kept /\
    ALL_DISTINCT (MAP FST slots ++ MAP FST kept) /\
    contract_inv mods exps ctx (ce with ce_vars := FEMPTY) cx /\
    module_body_inv mods src tops (ce with ce_vars := FEMPTY) cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    EVERY (body_expr_full_ok_mods mods exps cx) (MAP (\(_,_,_,e). e) vars) /\
    body_const_cells_agree mods cx env es /\
    env.type_defs = get_tenv cx /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
    ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function fn shfn /\ MEM fn ctx.ctx_functions /\ MEM shfn shadow_ctx.ctx_functions /\
    fn_inst_ids_distinct fn /\
    (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    (!H. dead_lo_ok H (DF H) 0 (ce with ce_vars := FEMPTY) cx) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx es s /\
      immutable_frame_mods fn (ce with ce_vars := FEMPTY) cx es s /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx es G tn s) /\
    expr_sim_inv_mods mods (ce with ce_vars := FEMPTY) cx env es /\
    alloca_history fn s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!f inst u. frag_reachable ctx fn s f inst u ==> dalloca_fmp_headroom inst u) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  no_sha256_exprs (MAP (\(_,_,_,e). e) vars) /\
  storage_trace_domain cx st0 es.storage_trace ==>
  ?D explicit marks r J tz.
    gas_origin_ptr_path (D,0,explicit,ctx,fn,[]) (s,G,tn) marks (r,J,tz) /\
    (!w. r = OK w ==> at_point sb w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  qabbrev_tac `ds = MAP (\(_,_,_,e). e) vars` >>
  `EVERY (runtime_constant_expr mods) ds` by
    (simp[Abbr `ds`, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
     simp[FORALL_PROD] >> rpt strip_tac >>
     drule_all LIST_REL_MEM_IMP >>
     disch_then (qx_choose_then `slot` strip_assume_tac) >>
     PairCases_on `slot` >> fs[]) >>
  `no_sha256_exprs ds` by simp[Abbr `ds`] >>
  `!gs. (SND (eval_exprs cx ds (es with gas_obs := gs))).storage_trace =
       es.storage_trace` by
    (gen_tac >> Cases_on `eval_exprs cx ds (es with gas_obs := gs)` >>
     drule_all grouped_checked_default_source_frame_mods >>
     simp[evaluation_state_component_equality]) >>
  mp_tac (Q.SPECL [`vars`,`slots`,`kept`,`sa`,`sha`,`es`,`s`,`G`,`tn`]
    (Q.INST [`PG` |-> `[]`] grouped_omitted_initializers_mods)) >>
  impl_tac >-
    (simp[Abbr `ds`] >> conj_tac
     >- (qpat_assum `EVERY _ kept` mp_tac >>
         simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD]) >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
           (drule_then (ACCEPT_TAC o cj 2))) >>
     rpt strip_tac >>
     qpat_assum `frag_reachable ctx fn s f inst u` (fn reach =>
       qpat_assum `!f inst u. frag_reachable ctx fn s f inst u ==> _`
         (ACCEPT_TAC o C MATCH_MP reach))) >>
  qpat_assum `Abbrev (ds = _)`
    (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  strip_tac >> drule_all grouped_default_initializer_outcome_mods >>
  disch_then (qx_choosel_then [`marks`,`res`,`ee`]
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac
        (qx_choosel_then [`r`,`J`,`tz`] assume_tac)))) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- FIRST_ASSUM ACCEPT_TAC >>
  strip_tac >>
  qexistsl_tac [`DF (storage_trace_horizon ee.storage_trace)`,
    `gas_explicit_sites ctx shadow_ctx`, `marks`, `r`, `J`, `tz`] >>
  rpt strip_tac >> gvs[at_point_def, exit_result_def, pairTheory.UNCURRY] >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
  impl_tac >- FIRST_ASSUM ACCEPT_TAC >>
  rpt strip_tac >> FIRST_ASSUM ACCEPT_TAC
QED
