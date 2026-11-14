(* Boundary facts for deploy-time assignment to a bare immutable. *)
Theory bodyImmutableAssignFacts
Ancestors
  bodyAssignPlace exprOpenMain exprLoweringProps bodySim exprSimHypsDefs
  supportedDecls bodyStorageMetadata vyperTypeInvariants vyperTypeSystem
  exprLowering compileEnv loweringStateRelDefs finite_map

Theorem immutable_assignment_shape:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
  immutable_root cx t ==>
  ?nsid ity. t = TopLevelNameTarget nsid /\
    supported_immutable_type tops nsid = SOME ity /\
    type_place_target env t = SOME (Type ity) /\
    cx.in_deploy /\ well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) ity /\
    assignable_type env.type_defs (expr_type e)
Proof
  strip_tac >>
  drule_all body_assign_immutable_target >> strip_tac >>
  drule assign_place_typing >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  drule_all body_immutable_target_type >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem immutable_assignment_globals:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_immutable_type tops (src,id) = SOME ity ==>
  FLOOKUP env.bare_globals (src,id) = SOME ity
Proof
  strip_tac >>
  qpat_x_assum `supported_immutable_type _ _ = _` mp_tac >>
  simp[supported_immutable_type_def] >>
  Cases_on `supported_variable_decl tops (src,id)` >> simp[] >>
  rename1 `_ = SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >>
  simp[] >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac supported_variable_decl_mem >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\
   bare_globals_complete env.bare_globals cx` by
    fs[body_inv_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  metis_tac[bare_globals_complete_def]
QED

Theorem immutable_assignment_layout:
  expr_sim_inv cenv cx env es /\
  FLOOKUP env.bare_globals (src,id) = SOME ity /\
  type_place_target env (TopLevelNameTarget (src,id)) = SOME (Type ity) /\
  cx.in_deploy ==>
  src = cenv.ce_module /\ cenv.ce_is_ctor /\
  cenv.ce_module_var_type (src,id) = SOME ity /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    (!tv. evaluate_type (get_tenv cx) ity = SOME tv ==>
          off + type_memory_size tv < dimword (:256))
Proof
  strip_tac >>
  `FLOOKUP env.bare_global_assignable (src,id) = SOME ity` by
    (fs[Once well_typed_expr_def] >>
     Cases_on `FLOOKUP env.bare_global_assignable (src,id)` >> gvs[]) >>
  fs[expr_sim_inv_def, bare_globals_layout_def] >> metis_tac[]
QED

Theorem immutable_assignment_destination:
  stmt_state_rel ctx func cenv cx es s /\ alloca_room ctx func s /\
  cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME tv ==>
  off + type_memory_size tv <= s.vs_alloca_next /\
  off + type_memory_size tv < dimword (:256) /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint off (type_memory_size tv) b sz) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint off (type_memory_size tv) b sz)
Proof
  strip_tac >>
  `immutable_decl_sep cenv cx es.scopes s.vs_vars s.vs_allocas
     s.vs_alloca_next` by
    fs[stmt_state_rel_def, immutable_alloca_sep_def] >>
  qpat_x_assum `immutable_decl_sep _ _ _ _ _ _` mp_tac >>
  rewrite_tac[immutable_decl_sep_alt] >>
  disch_then drule_all >> strip_tac >>
  drule alloca_room_next_lt >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem immutable_assignment_target_lowering:
  FLOOKUP cenv.ce_module_vars nsid = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type nsid = SOME ity ==>
  compile_get_target_ptr cfn cenv (TopLevelNameTarget nsid) st =
    ((Lit (n2w off), SOME LocCode, SOME (ValPT ity)),st)
Proof
  simp[compile_get_target_ptr_def, comp_return_def]
QED
