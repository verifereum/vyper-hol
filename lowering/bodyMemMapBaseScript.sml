(* The memory-counted mapping judgment of a subscript's base: a top-level
   mapping name emits no code, a subscript has body_expr_mem_ok's mapping
   clause, and nothing else names a mapping. *)
Theory bodyMemMapBase
Ancestors
  bodyMemoryPreds bodySim exprSimMapMemDefs exprSimSubscriptMap exprSimMapDefs
  fragGasMode fragGasPathMem gasSummary gasOutcome exprSimHypsDefs
  exprLoweringProps loweringStateRelDefs loweringPosts exprLowering context
  vyperTypeEnv vyperStoragePlaceProvenance vyperTypeSystem vyperInterpreter
  vyperState venomState

Theorem toplevel_mapping_marked_exec_mem[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (HashMapVarDecl tr kt vt,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\ ~s0.vs_halted ==>
  gas_marked_exec T (ctx,func) (eval_expr cx (TopLevelName ann (src,id)))
    (es,s0) [] (INL (HashMapRef tr (n2w slot) kt vt)) es (OK s0)
Proof
  strip_tac >>
  simp[gas_marked_exec_def, gas_marked_path_def, cj 1 gas_path_mem_rules,
       Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, LET_THM]
QED

(* exprSimSubscriptMap's compile_toplevel_map_sim, counted: the name
   compiles to a pointer literal and runs no instruction. *)
Theorem compile_toplevel_map_sim_mem:
  expr_map_pre cenv cx env (TopLevelName ann (src,id)) es ==>
  expr_map_sim_mem ctx func cenv cx ty (TopLevelName ann (src,id)) es
Proof
  strip_tac >>
  `env_consistent env cx es /\
   ?kt vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt)` by
    gvs[expr_map_pre_def, expr_sim_inv_def, well_typed_expr_def,
        AllCaseEqs()] >>
  drule_all env_consistent_toplevel_hashmap_static >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `lookup_var_slot_from_layout cx tr src id_str = SOME slot` >>
  drule_all lookup_global_mapping >> strip_tac >>
  `storage_mapping_region cx tr (n2w slot) (HashMapT kt vt)` by
    (irule lookup_global_mapping_region >> qexistsl [`src`, `es`, `es`, `id`] >>
     simp[]) >>
  rw[expr_map_sim_mem_def] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  fs[] >>
  drule_at (Pat `find_var_decl_by_name _ _ = _`) toplevel_storage_ce_vars_decl >>
  simp[var_decl_transient_def] >> disch_then drule_all >> strip_tac >>
  `compile_expr cenv ty (TopLevelName ann (src,id)) sa =
     (LocatedValue ann (mk_ptr (Lit (n2w slot))
        (if tr then LocTransient else LocStorage)),sa)` by
    (Cases_on `tr` >> gvs[compile_expr_def, vyperASTTheory.expr_type_def]) >>
  gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl [`INL (HashMapRef tr (n2w slot) kt vt)`, `es`, `OK s0`] >>
  conj_tac >- (irule toplevel_mapping_marked_exec_mem >> simp[]) >>
  disj1_tac >> simp_tac std_ss [] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp_tac std_ss (#rewrs (TypeBase.simpls_of ``:venom_state``))) >>
  qexists `s0` >> simp_tac std_ss [] >>
  qexistsl [`tr`, `n2w slot`, `kt`, `vt`] >>
  simp[slot_loc_def, mk_ptr_def, eval_operand_def, locals_kept_def]
QED

(* The base of a mapping subscript is memory-safe as a mapping: the
   counted twin of expr_map_case for every expression body_expr_mem_ok
   holds of. *)
Theorem body_expr_mem_ok_map:
  !cx e tops ctx func cenv env ty es.
    body_expr_mem_ok cx e /\ body_inv tops ctx cenv cx /\
    expr_map_pre cenv cx env e es ==>
    expr_map_sim_mem ctx func cenv cx ty e es
Proof
  rpt strip_tac >> drule expr_map_pre_shape >> strip_tac >> gvs[]
  >- (PairCases_on `id` >> metis_tac[compile_toplevel_map_sim_mem]) >>
  qpat_x_assum `body_expr_mem_ok _ _`
    (mp_tac o CONJUNCT2 o CONJUNCT2 o ONCE_REWRITE_RULE [body_expr_mem_ok_def]) >>
  disch_then irule >> simp[] >> metis_tac[]
QED
