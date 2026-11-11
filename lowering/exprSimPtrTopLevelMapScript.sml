(*
 * The pointer twin of S1's compile_toplevel_map_case (exprSimSubscriptMap):
 * a top-level mapping variable lowers to a pointer literal holding the
 * mapping's declared slot, with no code, so the state, the ghost and the
 * taint are those it started with, and a literal operand is untainted.
 *
 * TOP-LEVEL:
 *   compile_toplevel_map_sim_ptr
 *)
Theory exprSimPtrTopLevelMap
Ancestors
  bodyPtrSubscriptMapDefs exprSimSubscriptMap exprSimPtrTopLevelViews
  exprSimMapDefs exprSimHypsDefs bodyPtrDefs fragGasPathPtr gasSummary
  exprLoweringProps loweringStateRelDefs vyperStoragePlaceProvenance
  vyperTypeEnv vyperTypeSystem context exprLowering vyperInterpreter
  vyperState vyperAST loweringPosts venomState

Theorem compile_toplevel_map_sim_ptr:
  !d PG ctx func cenv cx env ty ann nsid es.
    expr_map_pre cenv cx env (TopLevelName ann nsid) es ==>
    expr_map_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann nsid) es
Proof
  rpt gen_tac >> PairCases_on `nsid` >> rename1 `TopLevelName ann (src,id)` >>
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
  rw[expr_map_sim_ptr_def] >>
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
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp_tac std_ss (#rewrs (TypeBase.simpls_of ``:venom_state``))) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (HashMapRef tr (n2w slot) kt vt)`,
                `es`, `G0`, `tn0`, `OK s0`] >>
  simp[gas_explicit_def, gas_path_ptr_rules] >> conj_tac
  >- simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
          return_def, raise_def, LET_THM] >>
  Cases_on `tr` >>
  gvs[slot_loc_def, mk_ptr_def, eval_operand_def, ptrDisciplineTheory.op_taint_def,
      ghost_inv_def, ghost_kept_def] >>
  metis_tac[]
QED
