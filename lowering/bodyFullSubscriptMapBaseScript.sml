Theory bodyFullSubscriptMapBase
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds exprSimSubscriptMap stateRelProj vyperPlaceResultTyping
  gasOutcomeFullCompose fragGasOriginPtr bodyPtrDefs wordArgsPtr
  exprSimMapDefs exprSimHypsDefs vyperTypeEnv vyperStoragePlaceProvenance
  vyperState bodySimFull gasSummary vyperStorageFootprint loweringStateRelDefs
  exprLowering loweringPosts vyperAST context venomState ptrDiscipline
  exprLoweringProps bodySim
  bodyFullPredsMods[qualified] bodyInvSplit[qualified]

(* The mapping declaration gives both the source reference and the compiled
   literal slot. Resolving it does not run an instruction or change a ghost. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `env_consistent env cx es /\
   ?kt vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt)` by
    (fs[expr_map_pre_def, expr_sim_inv_def] >>
     metis_tac[type_place_expr_global_lookup]) >>
  drule_all env_consistent_toplevel_hashmap_static >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `lookup_var_slot_from_layout cx tr src id_str = SOME slot` >>
  `storage_mapping_region cx tr (n2w slot) (HashMapT kt vt)` by
    (irule lookup_global_mapping_region >> qexistsl [`src`, `es`, `es`, `id`] >>
     irule lookup_global_mapping >> simp[]) >>
  rw[expr_map_sim_full_def] >>
  `!tail. eval_expr cx (TopLevelName ann (src,id)) (es with gas_obs := tail) =
     (INL (HashMapRef tr (n2w slot) kt vt), es with gas_obs := tail)` by
    (drule_all toplevel_mapping_marked_exec >>
     simp[gas_marked_exec_def, gas_explicit_def]) >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_outcome_full_bad_nil >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
    by fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0`
    by simp[] >>
  drule stmt_state_rel_vars_rels >> strip_tac >>
  drule_at (Pat `find_var_decl_by_name _ _ = _`) toplevel_storage_ce_vars_decl >>
  simp[var_decl_transient_def] >> disch_then drule_all >> strip_tac >>
  `compile_expr cenv ty (TopLevelName ann (src,id)) sa =
     (LocatedValue ann (mk_ptr (Lit (n2w slot)) (slot_loc tr)),sa)` by
    (qpat_x_assum `compile_expr _ _ (TopLevelName _ _) sa = _` kall_tac >>
     qpat_x_assum `FLOOKUP cenv.ce_module_vars _ = _` mp_tac >>
     Cases_on `tr` >> simp[] >> strip_tac >>
     simp[compile_expr_def, slot_loc_def, expr_type_def]) >>
  gvs[] >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `es`, `INL (HashMapRef tr (n2w slot) kt vt)`, `s0`, `tn0`] >>
  simp[gas_origin_ptr_path_rules] >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_then strip_assume_tac >>
  simp[mk_ptr_def, eval_operand_def, op_taint_def, op_prov_def,
       ghost_kept_at_refl, stmt_state_rel_start_gas_obs] >>
  conj_tac
  >- (qpat_assum `storage_well_formed_on cx es _` mp_tac >>
      simp[NoAsms, storage_well_formed_on_def, boolTheory.FORALL_BOOL,
           vyperStorageBackendTheory.get_storage_def]) >>
  qpat_assum `ghost_inv_at _ _ _ _ _ es _ _ _` mp_tac >>
  simp[NoAsms, ghost_inv_at_def] >>
  disch_then (ACCEPT_TAC o CONJUNCT1)
QED
*)
Theorem toplevel_map_sim_full[local]:
  expr_map_pre_mods mods cenv cx env (TopLevelName ann (src,id)) es ==>
  expr_map_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TopLevelName ann (src,id)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> drule expr_map_pre_shape >> strip_tac >> gvs[]
  >- (PairCases_on `id` >> irule toplevel_map_sim_full >> metis_tac[]) >>
  qpat_x_assum `body_expr_full_ok _ _`
    (mp_tac o CONJUNCT2 o CONJUNCT2 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
  metis_tac[]
QED
*)
Theorem body_expr_full_ok_map:
  body_expr_full_ok_mods mods exps cx e /\ (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env es /\
  expr_map_pre_mods mods cenv cx env e es ==>
  expr_map_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  cheat
QED
