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
  bodyLocalNameWordReadMods bodyLocalNameAliasMods
  bodyQualifiedSlotRawMods bodyQualifiedImmutableRawMods immutableRegionFrameProps
  exprSimTopLevelProps exprBodyPreTypingProps vyperTypeGlobalLookupSoundness
  gasShadowCompileStmtHelpers exprSimMemorySource bodyQualifiedSlotWordMods
  bodyQualifiedSlotCopyMods bodyQualifiedCodeWordMods bodyQualifiedCtorCodeCopyMods
  bodyQualifiedRuntimeCodeCopyMods valueEncodingTyping immutableCopyExecution

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

(* Construct the fixed landing only when the source trace has a horizon. *)
Theorem lookup_pure_outcome_on_domain[local]:
  ~s.vs_halted /\
  (!tail. source (es with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
  (storage_trace_domain cx st0 ee.storage_trace ==>
    ?t G' tn'. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,G',tn') /\ Q H res (ee with gas_obs := []) G' tn' t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R
Proof
  strip_tac >> Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >- (first_x_assum drule >> strip_tac >> irule lookup_pure_outcome_mods >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `[]` >> disj1_tac >>
  conj_tac >- simp[gas_bad_storage_at_def, gas_explicit_def] >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`,`func`,`PG`,`G`,`tn`,`s`] >>
  simp[gas_origin_ptr_focus_nil, storage_trace_domain_def]
QED

Theorem name_lookup_value_full_mods[local]:
  expr_body_pre_mods mods cenv cx env (Name ann id) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Name ann id) es
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then strip_assume_tac local_name_lookup_mods >>
  drule_all_then assume_tac name_lookup_type_memory >>
  rw[expr_sim_full_mods_def] >> irule lookup_pure_outcome_on_domain >>
  simp[] >> qexistsl_tac [`es`,`INL entry.value`] >>
  conj_tac >- (gen_tac >>
    qspecl_then [`cx`,`ann`,`id`,`es with gas_obs := tail`,`entry`] mp_tac
      (CONV_RULE (DEPTH_CONV ETA_CONV) eval_name_word) >> simp[]) >>
  strip_tac >> simp[] >> Cases_on `is_word_type ann`
  >- (
    `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
      fs[storage_trace_domain_def] >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
    `?w. lookup_var p s0 = SOME w` by
      (drule stmt_state_rel_local_ptrs_alloca >> simp[local_ptrs_rel_def] >>
       strip_tac >> first_x_assum (drule_all_then strip_assume_tac) >>
       goal_assum drule >> simp[]) >>
    drule_all_then strip_assume_tac local_lookup_ghost_pointer >>
    simp[expr_type_def] >> irule (SIMP_RULE (srw_ss()) [expr_type_def] local_name_word_read_mods) >>
    simp[] >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
      (INL entry.value, es with gas_obs := [])` by
    (qspecl_then [`cx`,`ann`,`id`,`es with gas_obs := []`,`entry`] mp_tac
       eval_name_word >> simp[Once evaluate_def, bind_def, get_scopes_def,
         return_def, type_check_def, assert_def, check_def, ignore_bind_def]) >>
  simp[expr_type_def] >> irule (SIMP_RULE (srw_ss()) [expr_type_def] local_name_alias_read_mods) >> simp[] >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  reverse conj_tac >- (qexists_tac `ty` >> simp[]) >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac >- (irule lookup_immutable_frame_mods >> qexists_tac `es` >> simp[]) >>
  irule lookup_ghost_frame_mods >> qexists_tac `es` >> simp[]
QED

Theorem name_lookup_full_ok_mods:
  !mods exps cx ann id. body_expr_full_ok_mods mods exps cx (Name ann id)
Proof
  rw[body_expr_full_ok_mods_def]
  >- (irule name_lookup_value_full_mods >> goal_assum (drule_at Any) >> simp[]) >>
  irule name_lookup_vv_full_mods >> goal_assum (drule_at Any) >> simp[]
QED

(* The qualified place intro is passed in, so the consumer does not depend on
   the placement of its implementation. *)
val qualified_place =
  ``!mods exps ctx cenv cx env es src id tops func s off rt v ann.
    contract_inv mods exps ctx cenv cx /\
    expr_sim_inv_mods mods cenv cx env es /\
    get_module_code cx src = SOME tops /\
    immutable_frame_mods func cenv cx es s /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    lookup_immutable cx es src id = SOME (rt,v) /\
    evaluate_type (get_tenv cx) ann = SOME rt ==>
    ALOOKUP cenv.ce_modules src = SOME tops /\
    off + type_memory_size rt < dimword (:256) /\
    read_result cx (PlaceR (ImmutablePlace src id [])) es = (INL v,es) /\
    vv_holds_mods cenv cx ann (PlaceR (ImmutablePlace src id []))
      (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) es s /\
    vv_place_ptr_mods cenv cx es s (PlaceR (ImmutablePlace src id []))
      (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) /\
    immutable_value_admissible rt v /\
    (~cenv.ce_is_ctor ==> off + type_memory_size rt <= LENGTH s.vs_data_section) /\
    val_in_memory rt v off (if cenv.ce_is_ctor then s.vs_memory else s.vs_data_section)``;

Theorem qualified_lookup_dispatch[local]:
  expr_body_pre_mods mods cenv cx env (TopLevelName ann (src,id)) es /\
  gas_admissible (eval_expr cx (TopLevelName ann (src,id))) expr_vv_res_ok es ==>
  ?tops. get_module_code cx src = SOME tops /\
    (find_var_decl_by_name id tops = NONE \/
     ?tr typ id_str. find_var_decl_by_name id tops = SOME (StorageVarDecl tr typ,id_str))
Proof
  strip_tac >> Cases_on `get_module_code cx src`
  >- metis_tac[missing_module_not_gas_admissible] >> simp[] >>
  rename1 `get_module_code cx src = SOME tops` >>
  Cases_on `find_var_decl_by_name id tops` >> simp[] >>
  PairCases_on `x` >> Cases_on `x0` >> simp[] >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
  drule_all TopLevelName_Type_HashMapVarDecl_impossible >> simp[]
QED

(* Match the prefix certificates to the actual caller indices explicitly only
   where the indices are absent from the source hypotheses. *)
val slot_prefix_tac =
  drule_all_then strip_assume_tac
    (SIMP_RULE (srw_ss()) [LET_THM]
      (Q.INST [`sa` |-> `sa`, `ty` |-> `ty`] qualified_slot_raw_mods));

val immutable_prefix =
  REWRITE_RULE [Q.GENL [`mods`,`exps`,`ctx`,`cenv`,`cx`,`env`,`entry`,`H`,`D`,`lo`,
    `es`,`src`,`tops`,`s`,`d`,`G`,`tn`,`id`,`off`,`imms`,`rt`,`v`]
    qualified_immutable_ctor_frame_mods] qualified_immutable_raw_mods;

val immutable_prefix_tac =
  drule_all_then (qspec_then `ty` (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM]))
    immutable_prefix;

Theorem qualified_name_vv_full_mods[local]:
  ^qualified_place /\ contract_inv mods exps ctx cenv cx /\
  expr_body_pre_mods mods cenv cx env (TopLevelName ann (src,id)) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TopLevelName ann (src,id)) es
Proof
  strip_tac >> rw[expr_vv_sim_full_mods_def] >>
  drule_all_then strip_assume_tac qualified_lookup_dispatch
  >- (immutable_prefix_tac >> gvs[] >>
      irule lookup_pure_outcome_on_domain >> simp[] >>
      qexistsl_tac [`es`,`INL (PlaceR (ImmutablePlace src id []))`] >>
      simp[] >> strip_tac >> qexistsl_tac [`s0`,`G0`,`tn0`] >>
      gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> ALOOKUP _ _ = _ /\ _`
        (drule_then strip_assume_tac) >>
      fs[gas_origin_ptr_path_rules, vv_location_def, mk_ptr_def, arithmeticTheory.ADD_COMM] >>
      strip_tac >> gvs[]) >>
  slot_prefix_tac >>
  qpat_x_assum `!ty sa. ?slot rt. _` (qspecl_then [`ty`,`sa`] strip_assume_tac) >>
  irule lookup_pure_outcome_on_domain >> simp[] >>
  qexistsl_tac [`es with storage_trace := es.storage_trace ++ [StorageRoot tr slot rt]`,
                `INL (PlaceR (StoragePlace tr (n2w slot) rt))`] >>
  simp[] >> strip_tac >>
  qpat_assum `storage_trace_domain _ _ _ ==> _` (drule_then strip_assume_tac) >> gvs[] >>
  qexistsl_tac [`s0`,`G0`,`tn0`] >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> MEM _ _ /\ _`
    (drule_then strip_assume_tac) >>
  Cases_on `tr` >> simp[gas_origin_ptr_path_rules, ghost_kept_at_def, vv_location_def, mk_ptr_def, slot_loc_def]
QED

Theorem lookup_bad_trace_mods[local]:
  ~s.vs_halted /\
  (!tail. (SND (source (es with gas_obs := tail))).storage_trace = obs) /\
  ~storage_trace_domain cx st0 obs ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `[]` >>
  disj1_tac >> conj_tac >- simp[gas_bad_storage_at_def, gas_explicit_def] >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`,`func`,`PG`,`G`,`tn`,`s`] >>
  simp[gas_origin_ptr_focus_nil, storage_trace_domain_def]
QED

Theorem forced_lookup_trace[local]:
  (!tail. source (es with gas_obs := tail) = (INL tv,ee with gas_obs := tail)) ==>
  !tail. (SND (bind source (read_result cx) (es with gas_obs := tail))).storage_trace =
         ee.storage_trace
Proof
  strip_tac >> gen_tac >> simp[bind_def] >>
  Cases_on `read_result cx tv (ee with gas_obs := tail)` >>
  drule_then SUBST_ALL_TAC read_result_state >> simp[]
QED

Theorem qualified_lookup_type_memory[local]:
  expr_body_pre_mods mods cenv cx env (TopLevelName ann key) es /\
  evaluate_type (get_tenv cx) ann = SOME rt ==>
  type_memory_bytes cenv ann = type_memory_size rt /\ type_memory_size rt < 2 ** 64
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_inv >>
  drule_all_then assume_tac name_lookup_type_memory >> simp[] >>
  `alloc_limits_expr cenv (TopLevelName ann key)` by fs[expr_body_pre_mods_def] >>
  Cases_on `is_word_type ann`
  >- (drule_all word_tv_memory_size >> simp[]) >>
  drule alloc_limits_expr_type_alloc_ok >> simp[expr_type_def,allocLimitsTheory.type_alloc_ok_def]
QED

Theorem qualified_name_value_full_mods[local]:
  ^qualified_place /\ contract_inv mods exps ctx cenv cx /\
  expr_body_pre_mods mods cenv cx env (TopLevelName ann (src,id)) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TopLevelName ann (src,id)) es
Proof
  strip_tac >> rw[expr_sim_full_mods_def] >>
  drule_then assume_tac forced_expr_admissible_raw >>
  drule_all_then strip_assume_tac qualified_lookup_dispatch
  >- suspend "immutable" >> suspend "slot"
QED

Resume qualified_name_value_full_mods[immutable]:
  immutable_prefix_tac >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- suspend "immutable_good" >>
  irule lookup_bad_trace_mods >> simp[] >> qexists_tac `es.storage_trace` >> simp[] >>
  irule forced_lookup_trace >> simp[]
QED

Resume qualified_name_value_full_mods[immutable_good]:
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ALOOKUP _ _ = _ /\ _`
    (drule_then strip_assume_tac) >>
  `value_has_type rt v` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE (srw_ss())
        [vv_post_mods_def, vv_holds_mods_def, immutable_holds_mods_def, immutable_holds_def,
         expr_type_def, mk_ptr_def, eval_operand_def]) >> gvs[]) >>
  drule_all_then strip_assume_tac qualified_lookup_type_memory >>
  irule lookup_pure_outcome_on_domain >> simp[] >> qexistsl [`es`,`INL v`] >>
  conj_tac >- (drule read_result_gas_obs >> simp[bind_def]) >> strip_tac >>
  `unwrap_value cenv (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) sa = (op,sb)` by
    fs[lower_value_def,comp_bind_def] >>
  `off < dimword (:256)` by decide_tac >>
  `w2n (n2w off : bytes32) = off` by simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s0 /\
    immutable_frame_mods func cenv cx (es with gas_obs := []) s0 /\
    storage_well_formed_on cx (es with gas_obs := []) (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G0 tn0 s0` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ALOOKUP _ _ = _ /\ _`
       (drule_then strip_assume_tac) >> gvs[vv_post_mods_def]) >>
  Cases_on `is_word_type ann` >- suspend "immutable_word" >>
  Cases_on `cenv.ce_is_ctor` >- suspend "immutable_ctor" >> suspend "immutable_runtime"
QED

Resume qualified_name_value_full_mods[immutable_word]:
  drule_all_then assume_tac word_tv_memory_size >>
  `~cenv.ce_is_ctor ==> immutable_copy_read F (n2w off) s0 = typed_val_to_w256 rt v` by
    (strip_tac >> simp[immutable_copy_read_def, GSYM valueEncodingDefsTheory.mem_word_at_def] >>
     irule exprSimPropsTheory.val_in_memory_word_type >> fs[] >>
     qexistsl [`ann`,`get_tenv cx`] >> simp[]) >>
  simp[expr_type_def] >>
  irule (SIMP_RULE (srw_ss()) [expr_type_def]
    (Q.INST [`e` |-> `TopLevelName ann (src,id)`, `ee` |-> `es with gas_obs := []`]
      qualified_code_word_read_mods)) >> simp[] >>
  conj_tac >- (gen_tac >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
      (drule_then strip_assume_tac) >> simp[]) >>
  qexists_tac `n2w off` >> fs[]
QED

Resume qualified_name_value_full_mods[immutable_ctor]:
  simp[expr_type_def] >>
  irule (SIMP_RULE (srw_ss()) [expr_type_def]
    (Q.INST [`ee` |-> `es with gas_obs := []`] qualified_ctor_code_copy_read_mods)) >>
  simp[] >> conj_tac >- (gen_tac >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
      (drule_then strip_assume_tac) >> simp[]) >>
  qexistsl [`off`,`ty`] >> fs[arithmeticTheory.LESS_MOD,arithmeticTheory.ADD_COMM]
QED

Resume qualified_name_value_full_mods[immutable_runtime]:
  `lo = 0` by fs[dead_lo_ok_mods_def] >> gvs[] >>
  simp[expr_type_def] >>
  irule (SIMP_RULE (srw_ss()) [expr_type_def,lowered_value_type_def]
    (Q.INST [`e` |-> `TopLevelName ann (mid,id)`, `ee` |-> `es with gas_obs := []`]
      qualified_runtime_code_copy_read_mods)) >> simp[] >>
  conj_tac >- (gen_tac >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> immutable_frame_mods _ _ _ _ _ /\ _`
      (drule_then strip_assume_tac) >> simp[]) >>
  qexists_tac `n2w off` >>
  fs[value_has_type_val_wf,arithmeticTheory.ADD_COMM,arithmeticTheory.LESS_MOD]
QED

Resume qualified_name_value_full_mods[slot]:
  slot_prefix_tac >>
  qpat_x_assum `!ty sa. ?slot rt. _` (qspecl_then [`ty`,`sa`] strip_assume_tac) >>
  qabbrev_tac `ee = es with storage_trace := es.storage_trace ++ [StorageRoot tr slot rt]` >>
  Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >- suspend "slot_good" >>
  irule lookup_bad_trace_mods >> simp[] >> qexists_tac `ee.storage_trace` >> simp[] >>
  irule forced_lookup_trace >> simp[Abbr `ee`]
QED

Resume qualified_name_value_full_mods[slot_good]:
  `storage_trace_domain cx st0 (es.storage_trace ++ [StorageRoot tr slot rt])` by
    fs[Abbr `ee`] >>
  qpat_x_assum `storage_trace_domain _ _ (_ ++ _) ==> _` (drule_then strip_assume_tac) >>
  irule lookup_pure_outcome_on_domain >> simp[] >> qexistsl [`ee`,`INL v`] >>
  conj_tac >- simp[bind_def,Abbr `ee`] >> strip_tac >>
  `unwrap_value cenv (LocatedValue ann (mk_ptr (Lit (n2w slot)) (slot_loc tr))) sa = (op,sb)` by
    fs[lower_value_def,comp_bind_def] >>
  Cases_on `is_word_type ann` >- suspend "slot_word" >> suspend "slot_copy"
QED

Resume qualified_name_value_full_mods[slot_word]:
  simp[expr_type_def] >>
  qpat_assum `is_word_type ann` (fn th =>
    irule (SIMP_RULE (srw_ss()) [expr_type_def,th]
      (Q.INST [`e` |-> `TopLevelName ann (src,id)`,
               `ee` |-> `ee with gas_obs := []`] qualified_slot_word_read_mods))) >>
  simp[] >> qexistsl [`n2w slot`,`ann`,`tr`,`PlaceR (StoragePlace tr (n2w slot) rt)`] >>
  fs[Abbr `ee`,expr_type_def] >>
  fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> MEM _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Resume qualified_name_value_full_mods[slot_copy]:
  simp[expr_type_def] >>
  drule_all_then strip_assume_tac qualified_lookup_type_memory >>
  fs[Abbr `ee`,expr_type_def] >>
  `valid_horizon cx st0 (storage_trace_horizon (es.storage_trace ++ [StorageRoot tr slot rt]))
      (es.storage_trace ++ [StorageRoot tr slot rt])` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> MEM _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qabbrev_tac `ee = es with <|gas_obs := []; storage_trace := es.storage_trace ++ [StorageRoot tr slot rt]|>` >>
  `storage_holds cx tr ann (PlaceR (StoragePlace tr (n2w slot) rt)) (n2w slot) ee s0` by
    (Cases_on `tr` >> qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE (srw_ss())
        [vv_post_mods_def, vv_holds_mods_def, vv_holds_def,
         expr_type_def, mk_ptr_def, slot_loc_def, eval_operand_def]) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes /\ storage_trace_domain cx st0 ee.storage_trace` by
    simp[Abbr `ee`] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func cenv cx (TopLevelName ann (src,id)) es sa sa s0 ee
      (PlaceR (StoragePlace tr (n2w slot) rt))
      (LocatedValue ann (mk_ptr (Lit (n2w slot)) (slot_loc tr))) s0 /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G0 tn0 s0` by
    (simp[Abbr `ee`] >> gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> MEM _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `read_result cx (PlaceR (StoragePlace tr (n2w slot) rt)) ee = (INL v,ee)` by
    simp[Abbr `ee`] >>
  drule_all_then strip_assume_tac
    (SIMP_RULE (srw_ss()) []
      (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`]
        qualified_slot_copy_read_mods)) >> gvs[Abbr `ee`] >>
  goal_assum (drule_at Any)
QED

Finalise qualified_name_value_full_mods

Theorem qualified_name_lookup_full_ok_mods:
  ^qualified_place ==>
  !mods exps cx ann nsid. body_expr_full_ok_mods mods exps cx (TopLevelName ann nsid)
Proof
  strip_tac >> rpt gen_tac >> PairCases_on `nsid` >>
  rw[body_expr_full_ok_mods_def]
  >- (irule qualified_name_value_full_mods >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`env`,`exps`,`mods`] >> simp[]) >>
  irule qualified_name_vv_full_mods >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`env`,`exps`,`mods`] >> simp[]
QED
