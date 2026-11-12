Theory bodyImmutableAugAssignFacts
Ancestors
  bodySim bodyStorageMetadata exprSimHypsDefs stmtSimAugAssignPlace supportedDecls
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperInterpreter
  vyperState exprOpenMain exprSimSource exprSimTopLevelImmutable
  finite_map list compileEnv loweringStateRelDefs exprSimUnwrap loweringPosts exprLoweringProps

Theorem immutable_augassign_metadata:
  !tops ctx cenv cx env es src id ity ret_ty ty bop e env'.
    body_inv tops ctx cenv cx /\ cx.in_deploy /\
    expr_sim_inv cenv cx env es /\
    supported_immutable_type tops (src,id) = SOME ity /\
    type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e) =
      SOME env' ==>
    src = NONE /\ cenv.ce_is_ctor /\ ty = ity /\ is_word_type ty /\
    FLOOKUP env.bare_globals (src,id) = SOME ty /\
    ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
          src = cenv.ce_module /\
          cenv.ce_module_var_type (src,id) = SOME ty /\
          (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
                off + type_memory_size tv < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >>
  drule aug_place_typing >> strip_tac >>
  qpat_x_assum `supported_immutable_type _ _ = _` mp_tac >>
  simp[supported_immutable_type_def] >>
  Cases_on `supported_variable_decl tops (src,id)` >> simp[] >>
  rename1 `_ = SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >>
  simp[] >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac supported_variable_decl_mem >> gvs[] >>
  rename1 `supported_value_type tops ity` >>
  `get_module_code cx NONE = SOME tops /\
   bare_globals_complete env.bare_globals cx /\
   bare_global_assignable_complete env.bare_global_assignable cx` by
    fs[body_inv_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `FLOOKUP env.bare_globals (NONE,id) = SOME ity /\
   FLOOKUP env.bare_global_assignable (NONE,id) = SOME ity` by
    metis_tac[bare_globals_complete_def, bare_global_assignable_complete_def] >>
  gvs[type_place_target_TopLevelNameTarget] >>
  fs[expr_sim_inv_def, bare_globals_layout_def, body_inv_def] >>
  metis_tac[exprSimSourceTheory.word_value_type_word]
QED

Theorem immutable_augassign_source_prefix:
  !cx src id es ts imms tv v.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = NONE /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) ==>
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (ImmutablePlace src id []),es) /\
    read_place cx (ImmutablePlace src id []) es = (INL v,es) /\
    place_type_value cx (ImmutablePlace src id []) es = (INL tv,es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def,
       get_immutables_def, get_address_immutables_def, get_place_def,
       read_place_def, place_type_value_def, bind_def, return_def,
       lift_option_type_def, lift_sum_def, evaluate_subscripts_def,
       subscripts_type_def]
QED

Theorem immutable_augassign_entry:
  !cenv cx env es src id ty.
    expr_sim_inv cenv cx env es /\
    FLOOKUP env.bare_globals (src,id) = SOME ty ==>
    ?ts imms tv v.
      get_module_code cx src = SOME ts /\
      find_var_decl_by_name id ts = NONE /\
      ALOOKUP es.immutables cx.txn.target = SOME imms /\
      FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) /\
      evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v
Proof
  rpt strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  drule_all env_consistent_bare_global_ready_src >> strip_tac >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  gvs[get_source_immutables_def] >>
  `find_var_decl_by_name id ts = NONE` by
    (fs[env_consistent_def, env_context_consistent_def] >>
     qpat_x_assum `!src id ty. FLOOKUP env.bare_globals _ = _ ==> ?ts. _`
       (drule_then strip_assume_tac) >> gvs[]) >>
  Cases_on `FLOOKUP (get_source_immutables src x) id` >>
  gvs[get_source_immutables_def] >>
  rename1 `_ = SOME pair` >> PairCases_on `pair` >>
  qexistsl_tac [`pair0`, `pair1`] >> simp[] >>
  conj_tac
  >- (fs[env_consistent_def, env_immutables_consistent_def,
         get_source_immutables_def] >> metis_tac[]) >>
  `state_well_typed es` by fs[expr_sim_inv_def] >>
  drule_all state_well_typed_immutables_ALOOKUP >>
  strip_tac >> drule imms_well_typed_get_source_immutables >>
  simp[get_source_immutables_def] >> metis_tac[]
QED

Theorem immutable_augassign_load:
  stmt_state_rel ctx func cenv cx es ss /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (tv,v) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\
  value_has_type tv v /\ off + type_memory_size tv < dimword (:256) ==>
  mload off ss = typed_val_to_w256 tv v
Proof
  strip_tac >>
  `val_in_memory tv v off ss.vs_memory` by
    (fs[stmt_state_rel_def, state_rel_def, immutables_rel_def] >> metis_tac[]) >>
  `immutable_holds cenv cx ty (Value v) (n2w off) es ss` by
    (simp[immutable_holds_def, read_result_def, return_def] >>
     qexistsl_tac [`id`, `off`, `tv`, `v`, `0`] >> simp[] >>
     `off < dimword (:256)` by decide_tac >> simp[]) >>
  drule_all immutable_holds_iload >> strip_tac >> gvs[] >>
  `off < dimword (:256)` by decide_tac >>
  gvs[wordsTheory.w2n_n2w]
QED
