(* A constructor immutable root resolves at the qualified key with no code. *)
Theory bodyWriteImmutableRootMods
Ancestors
  bodyWriteTargetStageMods gasOutcomeFullPostMods exprBodyPreProps
  exprSimHypsDefs exprSimWordArgs wordArgsPtr exprLoweringProps
  vyperTypeEnv vyperTypeInvariants vyperInterpreter vyperState
  vyperStorageFootprint vyperFixedShapePath finite_map alist
  bodyFullPostsMods bodyInvSplit loweringStateRelDefs bodyFullShadowBodyInv
  exprLowering compileEnv fragGasOriginPtr bodyFullTargetDefs ptrDiscipline
  targetPlaceSim loweringPosts venomState

Theorem immutable_root_typed_metadata[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  type_place_target env (TopLevelNameTarget (owner,id)) = SOME vt ==>
  ?ty. vt = Type ty /\ FLOOKUP env.bare_globals (owner,id) = SOME ty /\
       cenv.ce_module_var_type (owner,id) = SOME ty
Proof
  strip_tac >> drule_then assume_tac expr_sim_inv_mods_env >>
  `bare_globals_layout cenv.ce_is_ctor cenv.ce_module_var_type
     cenv.ce_module_vars cenv.ce_modules cx env.bare_globals
     env.bare_global_assignable` by fs[expr_sim_inv_mods_def] >>
  `?ity. FLOOKUP env.bare_globals (owner,id) = SOME ity` by
    fs[bare_globals_layout_def] >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[type_place_target_TopLevelNameTarget] >> strip_tac >> gvs[] >>
  qpat_x_assum `env_consistent _ _ _`
    (strip_assume_tac o REWRITE_RULE [env_consistent_def, env_context_consistent_def]) >>
  qpat_assum `!src id ty. FLOOKUP env.bare_global_assignable (src,id) = SOME ty ==> _`
    (drule_then strip_assume_tac) >> gvs[bare_globals_layout_def]
QED

Theorem immutable_root_source_lookup[local]:
  env_consistent env cx es /\ FLOOKUP env.bare_globals (owner,id) = SOME ty ==>
  ?tops imms rt v.
    get_module_code cx owner = SOME tops /\ find_var_decl_by_name id tops = NONE /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables owner imms) id = SOME (rt,v) /\
    evaluate_type (get_tenv cx) ty = SOME rt
Proof
  strip_tac >> drule_all_then strip_assume_tac env_consistent_bare_global_find_NONE >>
  drule_all_then strip_assume_tac env_consistent_bare_global_ready_src >>
  Cases_on `ALOOKUP es.immutables cx.txn.target`
  >- gvs[get_source_immutables_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables owner imms) id` >> gvs[] >>
  rename1 `FLOOKUP (get_source_immutables owner imms) id = SOME entry` >>
  PairCases_on `entry` >>
  qpat_x_assum `env_consistent _ _ _`
    (strip_assume_tac o REWRITE_RULE [env_consistent_def, env_immutables_consistent_def]) >>
  gvs[] >>
  qpat_assum `!src id ty tv v. _ ==> evaluate_type _ ty = SOME tv`
    (drule_all_then assume_tac) >> simp[]
QED

Theorem immutable_root_gas_obs[local]:
  (immutable_frame_mods func cenv cx (es with gas_obs := gs) s <=>
   immutable_frame_mods func cenv cx es s) /\
  (ghost_inv_at_mods D lo d cenv cx (es with gas_obs := gs) G tn s <=>
   ghost_inv_at_mods D lo d cenv cx es G tn s) /\
  (storage_well_formed_on cx (es with gas_obs := gs) A <=>
   storage_well_formed_on cx es A)
Proof
  rpt conj_tac
  >- simp[immutable_frame_mods_def, immutables_rel_mods_def, immutables_rel_def,
          immutable_alloca_sep_mods_def, immutable_alloca_sep_def]
  >- simp[ghost_inv_at_mods_def]
  >> irule storage_well_formed_on_backends >> simp[]
QED

Theorem write_immutable_root_stage_mods:
  expr_sim_inv_mods mods cenv cx env es /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) ==>
  write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env (TopLevelNameTarget (owner,id)) es
Proof
  strip_tac >> rw[write_base_sim_mods_def] >>
  drule_all_then strip_assume_tac immutable_root_typed_metadata >> gvs[] >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_all_then strip_assume_tac immutable_root_source_lookup >>
  qhdtm_x_assum `write_target_entry_mods`
    (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  qpat_x_assum `compile_get_target_ptr _ _ _ sa = _` mp_tac >>
  simp[compile_get_target_ptr_def, comp_return_def] >> strip_tac >> gvs[] >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `es`, `INL (PlaceR (ImmutablePlace owner id []))`,
                `s0`, `tn0`] >>
  conj_tac
  >- simp[Once evaluate_def, lookup_global_def, bind_def, get_immutables_def,
          get_address_immutables_def, lift_option_type_def, return_def] >>
  rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` drule >> strip_tac >>
  simp[gas_origin_ptr_path_rules, write_target_post_mods_def,
       stmt_state_rel_start_gas_obs, immutable_root_gas_obs, wb_frame_refl,
       ghost_kept_at_refl, value_type_place_def, target_ptr_ok_def,
       op_prov_def, op_taint_def, write_target_location_mods_def, target_root_def,
       mem_path_offset_def, evaluate_subscripts_def, eval_operand_def,
       fixed_shape_path_def] >>
  qexistsl_tac [`imms`, `rt`, `v`] >> simp[]
QED
