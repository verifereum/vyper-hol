(* Linked raw name lookups, at the caller's code cursor. *)
Theory bodyNameLookupPathsMods
Ancestors
  bodyFullPredsMods exprBodyPreProps bodyNameMemoryFacts stateRelProj
  exprSimTopLevelStorage exprSimTopLevelImmutable bodyFullZeroCasesMods
  gasOutcomeFullMods gasOutcomeFull gasStorage gasSummary gasShadowCompile
  vyperStorageFootprint bodyInvSplit loweringSlice loweringStateRelDefs
  bodyFullPostsMods bodyFullShadowBodyInv exprSimHypsDefs vyperTypeEnv
  vyperTypeInvariants vyperTypeSystem exprLoweringProps exprSimHyps
  exprSimNameValue exprSimNameWord ptrDiscipline bodyPtrDefs fragGasOriginPtr
  compileEnv exprLowering context vyperInterpreter vyperState vyperAST
  loweringPosts venomState valueEncodingProofs exprSimMemDefs typedMemoryCopy exprSimProps

Theorem lookup_pure_outcome_mods[local]:
  ~s.vs_halted /\
  (!tail. source (es with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,G',tn') /\ Q H res (ee with gas_obs := []) G' tn' t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `[]` >>
  Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`OK t`,`G'`,`tn'`] >>
      simp[gas_explicit_def] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  disj1_tac >> conj_tac >- simp[gas_bad_storage_at_def, gas_explicit_def] >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`,`func`,`PG`,`G`,`tn`,`s`] >>
  simp[gas_origin_ptr_focus_nil, storage_trace_domain_def]
QED

Theorem lookup_immutable_frame_mods[local]:
  es'.immutables = es.immutables /\ es'.scopes = es.scopes /\
  immutable_frame_mods func cenv cx es s ==>
  immutable_frame_mods func cenv cx es' s
Proof
  strip_tac >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def,
     immutable_alloca_sep_mods_def, immutable_alloca_sep_def, immutables_rel_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >>
  disch_then strip_assume_tac >> first_assum ACCEPT_TAC
QED

Theorem lookup_ghost_frame_mods[local]:
  es'.scopes = es.scopes /\ ghost_inv_at_mods D lo d cenv cx es G tn s ==>
  ghost_inv_at_mods D lo d cenv cx es' G tn s
Proof
  strip_tac >> qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ es _ _ _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[ghost_inv_at_mods_def] >> simp[] >>
  disch_then strip_assume_tac >> first_assum ACCEPT_TAC
QED

Theorem local_name_lookup_mods[local]:
  expr_body_pre_mods mods cenv cx env (Name ann id) es ==>
  ?entry p sz. lookup_scopes id es.scopes = SOME entry /\
               evaluate_type (get_tenv cx) ann = SOME entry.type /\
               value_has_type entry.type entry.value /\
               FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
               cenv.ce_var_type id = SOME ann
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `env_consistent env cx es /\ state_well_typed es` by fs[expr_sim_inv_mods_def] >>
  drule_all_then strip_assume_tac well_typed_Name_lookup >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    fs[expr_sim_inv_mods_def, well_typed_expr_def] >>
  `cenv.ce_var_type id = SOME ann` by fs[expr_sim_inv_mods_def, well_typed_expr_def] >>
  qexistsl_tac [`entry`,`p`,`sz`] >> gvs[]
QED

Theorem name_lookup_type_memory[local]:
  expr_sim_inv_mods mods cenv cx env es /\ evaluate_type (get_tenv cx) ann = SOME tv ==>
  type_memory_bytes cenv ann = type_memory_size tv
Proof
  strip_tac >> irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
  fs[expr_sim_inv_mods_def] >> metis_tac[]
QED

Theorem name_lookup_vv_post_mods[local]:
  immutable_frame_mods func cenv cx ee s /\
  vv_post H ctx func cenv cx e es sa sb s0 ee (PlaceR (MemoryPlace id path))
    (LocatedValue ann (mk_ptr op LocMemory)) s ==>
  vv_post_mods H ctx func cenv cx e es sa sb s0 ee (PlaceR (MemoryPlace id path))
    (LocatedValue ann (mk_ptr op LocMemory)) s
Proof
  simp[vv_post_def, vv_post_mods_def, vv_holds_mods_def,
       vv_place_ptr_mods_def, mk_ptr_def] >> metis_tac[]
QED

Theorem local_lookup_ghost_pointer[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME w ==>
  ptr_covers G tn p s sz /\
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem
Proof
  rewrite_tac[ghost_inv_at_mods_def] >> strip_tac >>
  qpat_assum `!nm e q len. lookup_scopes _ _ = _ /\ _ ==> _`
    (drule_all_then strip_assume_tac) >> simp[]
QED

Theorem name_lookup_vv_full_mods:
  expr_body_pre_mods mods cenv cx env (Name ann id) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Name ann id) es
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then strip_assume_tac local_name_lookup_mods >>
  drule_all_then assume_tac name_lookup_type_memory >>
  rw[expr_vv_sim_full_mods_def] >>
  drule compile_name_value_ptr >>
  disch_then (qspecl_then [`ty`,`sa`,`ann`] assume_tac) >> gvs[] >>
  irule lookup_pure_outcome_mods >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G0`,`es`,`INL (PlaceR (MemoryPlace id []))`,`s0`,`tn0`] >>
  conj_tac
  >- simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
          type_check_def, assert_def, check_def, ignore_bind_def] >>
  simp[] >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  simp[gas_origin_ptr_path_rules, ghost_kept_at_def] >>
  `immutable_frame_mods func cenv cx (es with gas_obs := []) s0` by
    (irule lookup_immutable_frame_mods >> qexists_tac `es` >> simp[]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G0 tn0 s0` by
    (irule lookup_ghost_frame_mods >> qexists_tac `es` >> simp[]) >>
  conj_tac >- (irule name_lookup_vv_post_mods >> simp[] >>
               irule name_value_post >> goal_assum (drule_at Any) >> simp[]) >>
  `?w. lookup_var p s0 = SOME w /\ w2n w + sz <= s0.vs_alloca_next /\
       type_memory_size entry.type <= sz /\ val_wf entry.type entry.value` by
    (drule stmt_state_rel_local_ptrs_alloca >> simp[local_ptrs_rel_def] >>
     strip_tac >> first_x_assum (drule_all_then strip_assume_tac) >>
     goal_assum drule >> simp[]) >>
  simp[expr_type_def, lowered_value_type_def, mk_ptr_def, vv_location_def] >>
  conj_tac
  >- (simp[GSYM mk_ptr_def] >> irule name_vv_store_bound >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all_then strip_assume_tac local_lookup_ghost_pointer >>
  `read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
    (INL entry.value, es with gas_obs := [])` by
    (qspecl_then [`cx`,`ann`,`id`,`es with gas_obs := []`,`entry`] mp_tac
       eval_name_word >> simp[Once evaluate_def, bind_def, get_scopes_def,
         return_def, type_check_def, assert_def, check_def, ignore_bind_def]) >>
  gvs[ptr_vv_ok_def, ptr_mem_ok_def, eval_operand_def, ptr_covers_def, ptr_buf_ok_def,
      lowered_value_type_def, expr_type_def] >>
  drule_then assume_tac val_store_size_le >> decide_tac
QED
