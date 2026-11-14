(* Mixed tuple assignment preserves the ordinary snapshot alternatives. *)
Theory tupleAssignImmutableDeploy
Ancestors
  tupleAssignImmutableDeployImmutableHead tupleAssignImmutableDeploySupportedTarget
  tupleAssignImmutableDeploySourceSuffix
  tuplePlaceFlagPrefix tuplePlaceRootReady tuplePlaceOpen tuplePlaceHead
  tuplePlaceCodeParts tuplePlaceSource tuplePlaceHeadGas tuplePlaceSuffixCode
  stmtSimAssignTuple stmtSimAssignTuplePlaces stmtSimDeclCompose stmtReasonVvMemory
  stmtSimDefs stmtSimForced stmtSimProps stmtSimForRounds bodySim
  exprSimHypsDefs exprSimDefs exprSimHyps loweringPosts exprLoweringProps
  supportedTargets vyperTypeSystem vyperTypeDefaults vyperTypeArgFits
  vyperInterpreter vyperState compileEnv stmtLowering stmtLoweringMono
  gasOutcome gasSummary gasSummaryCompose fragGasMode fragGasPath
  freshWrites list rich_list finite_map

Theorem tuple_immutable_unpack_outcome_open:
  body_inv tops ctx cenv cx /\ cx.in_deploy /\
  expr_type e = TupleT tys /\ lowered_value_type cenv e = TupleT ltys /\ gs <> [] /\
  value_has_type (TupleTV ltvs) (ArrayV (TupleV vs)) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) ltys ltvs /\
  expr_post ctx func cenv cx e es sa su s0 ee (ArrayV (TupleV vs)) op sv /\
  (!x. op = Var x ==> not_fresh_at su x) /\ sa.cs_next_id <= su.cs_next_id /\
  (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
  compile_tuple_unpack cenv (TupleT ltys) flag gs op su = ((),sf) /\
  fn_has_code su sf func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv su /\
  ~sv.vs_halted /\ sv.vs_current_bb = su.cs_current_bb /\
  sv.vs_inst_idx = LENGTH su.cs_current_insts /\
  expr_sim_inv cenv cx env ee /\
  body_tuple_target_ok cx (TupleTarget gs) (ArrayV (TupleV vs)) /\
  LIST_REL (\g t. well_typed_atarget env g t) gs tys /\
  EVERY (\g. ?bt. g = BaseTarget bt /\ supported_target tops bindings bt /\
    target_indices_pre cenv cx env bt /\
    call_evaluation_safe cx (int_calls_target bt) /\
    (body_base_target_ok cx bt ==> target_case F ctx func cenv cx bt) /\
    (immutable_root cx bt ==> ?nsid. bt = TopLevelNameTarget nsid /\
      IS_SOME (supported_immutable_type tops nsid))) gs /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs)+64 < dimword (:256) /\
    type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
  type_alloc_ok cenv (TupleT tys) /\ acyclic_struct_metadata cenv.ce_struct_fields ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs))) (ee,sv)
    (\res ff t. res = INL () /\ expr_sim_inv cenv cx env ff /\ ~block_is_terminated sf /\
      stmt_state_rel ctx func cenv cx ff t /\ ~t.vs_halted /\
      t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x v. not_fresh_at su x /\ lookup_var x sv = SOME v ==> lookup_var x t = SOME v) /\
      (!aid entry. FLOOKUP sv.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      alloca_frame cenv ee su sv cenv ff t)
    (\res ff r. expr_exit res r)
Proof
  strip_tac >>
  drule_all tuple_place_compiler_flag_prefix_head >> strip_tac >>
  `ltys <> []` by
    (imp_res_tac arg_types_fit_LENGTH >>
     fs[LIST_REL_EL_EQN] >> Cases_on `ltys` >> fs[]) >>
  `~block_is_terminated ss` by
    (irule tuple_place_load_open_probe >> goal_assum (drule_at Any) >> simp[]) >>
  `su.cs_next_var <= sl.cs_next_var` by
    (irule (cj 2 stmtSimAssignTupleTheory.tuple_stage_grows) >>
     qexistsl [`flag /\ EXISTS (\t. ~is_word_type t) ltys /\
        0 < type_memory_size_list ltvs`, `op`, `staged`,
       `type_memory_bytes cenv (TupleT ltys)`] >>
     qpat_x_assum `(if _ then _ else _) su = (staged,sl)` mp_tac >>
     Cases_on `flag /\ EXISTS (\t. ~is_word_type t) ltys /\
       0 < type_memory_size_list ltvs` >>
     simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >> pairarg_tac >>
     simp[comp_bind_def, comp_return_def]) >>
  `sl.cs_next_var <= ss.cs_next_var` by
    metis_tac[stmtSimReturnTheory.compile_tuple_load_all_grows] >>
  `LENGTH ltys = LENGTH tys` by metis_tac[arg_types_fit_LENGTH] >>
  `EVERY (\g. ?bt. g = BaseTarget bt) gs` by
    (qpat_x_assum `EVERY (\g. ?bt. g = BaseTarget bt /\ _) gs` mp_tac >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  `body_tuple_targets_ok cx gs vs` by fs[body_tuple_target_ok_def] >>
  `gas_outcome F (cx_tops cx) (ctx,func)
     (assign_tuple_target_list cx gs vs) (ee,t)
     (\res ff q. res = INL () /\ expr_sim_inv cenv cx env ff /\ ~block_is_terminated sf /\
       tuple_place_head ctx func cenv cx ff sa.cs_next_id sf
         tys ltys ltvs vs elems w (LENGTH tys) q /\
       body_tuple_targets_ok cx (DROP (LENGTH tys) gs) (DROP (LENGTH tys) vs) /\
       (!x v. not_fresh_at ss x /\ lookup_var x t = SOME v ==> lookup_var x q = SOME v) /\
       (!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==>
         FLOOKUP q.vs_allocas aid = SOME entry) /\
       alloca_frame cenv ee ss t cenv ff q)
     (\res ff r. expr_exit res r)` by
    (irule (SRULE [] (DISCH_ALL (Q.SPEC `0`
       (UNDISCH (SPEC_ALL tuple_mixed_suffix_from_steps))))) >>
     simp[] >>
     map_every qx_gen_tac [`i`,`es'`,`sp`,`sx`,`sy`,`s'`,`bt`,`r`] >> strip_tac >>
     `i < LENGTH gs` by metis_tac[LIST_REL_LENGTH] >>
     `supported_target tops bindings bt /\ target_indices_pre cenv cx env bt /\
      call_evaluation_safe cx (int_calls_target bt) /\
      (body_base_target_ok cx bt ==> target_case F ctx func cenv cx bt) /\
      (immutable_root cx bt ==> ?nsid. bt = TopLevelNameTarget nsid /\
        IS_SOME (supported_immutable_type tops nsid))` by
       (qpat_x_assum `EVERY (\g. ?bt. g = BaseTarget bt /\ _) gs`
          (qspec_then `i` mp_tac o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
     `well_typed_target env bt (EL i tys)` by
       (fs[LIST_REL_EL_EQN] >>
        qpat_x_assum `!n. n < LENGTH gs ==> well_typed_atarget _ _ _`
          (qspec_then `i` mp_tac) >>
        simp[well_typed_atarget_def]) >>
     `local_ptrs_reserved cenv sx` by
       (irule local_ptrs_reserved_next_var >> qexists `sp` >>
        fs[tuple_place_head_def]) >>
     Cases_on `immutable_root cx bt`
     >- (gvs[optionTheory.IS_SOME_EXISTS] >>
         rename1 `supported_immutable_type tops nsid = SOME ity` >>
         PairCases_on `nsid` >>
         mp_tac (Q.INST [`es` |-> `es'`, `s0` |-> `s'`,
           `lo` |-> `sa.cs_next_id`, `sa` |-> `sx`, `sb` |-> `sy`,
           `src` |-> `nsid0`, `id` |-> `nsid1`] tuple_immutable_head_outcome) >>
         impl_tac >- simp[] >> simp[]) >>
     `target_pre cenv cx env bt es' /\ target_sim ctx func cenv cx env bt es'` by
       (fs[body_tuple_target_ok_def, targetPlaceSimTheory.target_pre_def,
           targetPlaceSimTheory.target_case_def] >> metis_tac[]) >>
     mp_tac (Q.INST [`es` |-> `es'`, `s0` |-> `s'`,
       `lo` |-> `sa.cs_next_id`, `sa` |-> `sx`, `sb` |-> `sy`]
       tuple_immutable_mutable_head_outcome) >>
     impl_tac >- simp[] >> simp[]) >>
  simp[Once evaluate_def] >>
  irule gas_outcome_zero_prefix >> goal_assum (drule_at Any) >>
  irule exprSimMemDefsTheory.gas_outcome_post_mono >> goal_assum (drule_at Any) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `sl.cs_next_id <= ss.cs_next_id` by
    (mp_tac (cj 4 ci_mono_list_helpers) >>
     disch_then (qspecl_then [`cenv`, `staged`, `ltys`, `0`, `sl`] mp_tac) >>
     simp[ci_mono_def]) >>
  `su.cs_next_id <= sl.cs_next_id` by
    (qpat_x_assum `(if _ then _ else _) su = (staged,sl)` mp_tac >>
     IF_CASES_TAC >> simp[comp_return_def] >>
     simp[comp_bind_def, comp_ignore_bind_def] >>
     pairarg_tac >> simp[comp_return_def] >>
     pairarg_tac >> simp[comp_return_def] >> strip_tac >>
     imp_res_tac pairTheory.SND >>
     metis_tac[ci_mono_compile_alloc_buffer, ci_mono_emit_void, ci_mono_def,
       pairTheory.SND, arithmeticTheory.LESS_EQ_TRANS]) >>
  fs[tuple_place_head_def] >>
  reverse conj_tac
  >- (irule alloca_frame_trans >> qexistsl [`cenv`,`ee`,`t`,`ss`] >>
      simp[] >> decide_tac) >>
  rpt strip_tac >>
  `not_fresh_at ss x` by
    metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  metis_tac[]
QED

Theorem compile_assign_tuple_mixed_stmt_frag:
  !ctx func cx lctx RetQ cenv ty env tops bindings gs e es tys tvs ltys ltvs.
    (!s tv t s1 v t1.
       eval_expr cx e s = (INL tv,t) /\ read_result cx tv s1 = (INL v,t1) ==>
       body_tuple_target_ok cx (TupleTarget gs) v) /\
    body_inv tops ctx cenv cx /\ cx.in_deploy /\
    expr_type e = TupleT tys /\ gs <> [] /\
    LIST_REL (\g t. well_typed_atarget env g t) gs tys /\
    assignable_type (get_tenv cx) (TupleT tys) /\
    lowered_value_type cenv e = TupleT ltys /\ arg_types_fit ltys tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
    (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
      type_memory_size (EL i tvs) + 64 < dimword (:256) /\
      type_memory_size (EL i ltvs) + 64 < dimword (:256)) /\
    EVERY (\g. ?bt. g = BaseTarget bt /\ supported_target tops bindings bt /\
      target_indices_pre cenv cx env bt /\
      call_evaluation_safe cx (int_calls_target bt) /\
      (body_base_target_ok cx bt ==> target_case F ctx func cenv cx bt) /\
      (immutable_root cx bt ==> ?nsid. bt = TopLevelNameTarget nsid /\
        IS_SOME (supported_immutable_type tops nsid))) gs /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    expr_sim_inv cenv cx env es /\ expr_body_pre cenv cx env e es /\
    expr_sim ctx func cenv cx (TupleT tys) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def, stmt_env_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[declare_stmt_local_def, comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >>
  drule_all tuple_place_compile_parts_frames >> strip_tac >>
  `fn_has_code sa su func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[forced_then_admissible, eval_assign_tuple_action] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `su`, `op`, `s0`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  rewrite_tac[eval_assign_tuple_action] >>
  irule gas_outcome_bind_value >> goal_assum (drule_at Any) >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `res` >> fs[expr_exit_def] >>
      simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    fs[expr_body_pre_def] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `body_tuple_target_ok cx (TupleTarget gs) v` by
    (qpat_x_assum `bind (eval_expr _ _) _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := []) /\
   ?vs. v = ArrayV (TupleV vs) /\
     value_has_type (TupleTV ltvs) (ArrayV (TupleV vs))` by
    (mp_tac (Q.INST
      [`es` |-> `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `ee` |-> `mid with gas_obs := []`] tuple_place_root_rhs_ready) >>
     simp[] >> metis_tac[]) >> gvs[] >>
  `type_alloc_ok cenv (TupleT tys)` by
    (fs[expr_body_pre_def] >> drule exprSimHypsTheory.alloc_limits_expr_type_alloc_ok >> simp[]) >>
  drule_all tuple_place_root_layout_ready >> strip_tac >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by simp[] >>
  drule_all (Q.INST [`ee` |-> `mid with gas_obs := []`]
    tuple_immutable_unpack_outcome_open) >> strip_tac >>
  irule exprSimSubscriptMapTheory.gas_outcome_conseq >> goal_assum (drule_at Any) >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >> Cases_on `res` >> fs[expr_exit_def] >>
      simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >> fs[expr_post_def] >>
  reverse conj_tac
  >- (`MAP FDOM mid.scopes = MAP FDOM es.scopes` by
        (drule eval_read_preserves_scopes_dom >> simp[]) >>
      irule alloca_frame_expr_prefix >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (qexistsl [`ctx`, `cx`, `func`] >> simp[]) >>
      qexistsl [`mid`, `su`, `t`] >> gvs[] >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `not_fresh_at su x` by metis_tac[not_fresh_at_mono] >> metis_tac[]
QED
