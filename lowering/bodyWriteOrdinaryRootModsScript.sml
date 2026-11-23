(* Ordinary write roots resolve to their address without emitting code. *)
Theory bodyWriteOrdinaryRootMods
Ancestors
  bodyWriteTargetStageMods gasOutcomeFullPostMods fragGasOriginPtr
  bodyFullPostsMods bodyFullTargetDefs loweringPosts compileEnv
  venomState ptrDiscipline
  exprBodyPreProps exprSimHypsDefs exprSimProps exprLoweringProps exprLowering
  bodyInvSplit bodyFullShadowBodyInv bodyPtrDefs loweringStateRelDefs
  nameLoweringProps stateRelProj placeTypingProps wordArgsPtr
  targetPlaceSim vyperTypeEnv vyperTypeSystem vyperTypeInvariants
  vyperPlaceResultTyping gasOutcomeFull
  vyperStorageFootprint vyperState vyperInterpreter finite_map words

Theorem ordinary_root_frames[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  immutable_frame_mods func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at_mods D lo d cenv cx es G tn s ==>
  let ee = es with <|storage_trace := trace; gas_obs := []|> in
    stmt_state_rel H ctx func cenv cx ee s /\
    immutable_frame_mods func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods D lo d cenv cx ee G tn s /\
    wb_frame cenv es ee sa s s
Proof
  strip_tac >> simp[LET_THM, stmt_state_rel_start_gas_obs, wb_frame_def] >>
  rpt conj_tac
  >- (let val defs = [immutable_frame_mods_def, immutables_rel_mods_def,
                      immutables_rel_def, immutable_alloca_sep_mods_def,
                      immutable_alloca_sep_def]
      in SIMP_TAC (srw_ss()) defs >>
         qpat_assum `immutable_frame_mods _ _ _ _ _`
           (ACCEPT_TAC o SIMP_RULE (srw_ss()) defs)
      end)
  >- (qmatch_goalsub_abbrev_tac `storage_well_formed_on cx ee _` >>
      `ee.accounts = es.accounts /\ ee.tStorage = es.tStorage` by simp[Abbr `ee`] >>
      drule_then (fn th => simp[th]) storage_well_formed_on_backends)
  >> SIMP_TAC (srw_ss()) [ghost_inv_at_mods_def] >>
     qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [ghost_inv_at_mods_def])
QED

Theorem ordinary_local_entry[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  type_place_target env (NameTarget id) = SOME vt ==>
  ?ty p sz entry. vt = Type ty /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME ty /\
    lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
    evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  simp[type_place_target_NameTarget] >> strip_tac >> gvs[] >>
  drule expr_sim_inv_mods_env >>
  simp[env_consistent_def, env_scopes_consistent_def] >> strip_tac >>
  qpat_assum `!id. FLOOKUP _ id = SOME T ==> ?entry. _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  qpat_assum `!id ty. _ ==> ?p sz. FLOOKUP _ id = SOME _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!id ty. _ ==> cenv.ce_var_type id = SOME ty`
    (drule_then assume_tac) >>
  qpat_assum `!id ty entry. _ ==> evaluate_type _ ty = SOME entry.type`
    (drule_all_then assume_tac) >>
  qexistsl_tac [`p`, `sz`, `entry`] >> simp[]
QED

Theorem ordinary_root_pointer_local[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
  target_ptr_ok cenv (PlaceR (MemoryPlace id []))
    (Var p,SOME LocMemory,SOME (ValPT ty)) G tn s
Proof
  strip_tac >> simp[target_ptr_ok_def] >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_inv_at_mods_def] >> strip_tac >>
  qpat_assum `!name entry p sz. _ ==> ptr_covers _ _ _ _ _ /\ _`
      (drule_all_then strip_assume_tac) >> fs[ptr_covers_def, op_prov_def]
QED

Theorem write_local_root_stage_mods:
  expr_sim_inv_mods mods cenv cx env es ==>
  write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env (NameTarget id) es
Proof
  strip_tac >> rw[write_base_sim_mods_def] >>
  drule_all ordinary_local_entry >> strip_tac >> gvs[] >>
  gvs[write_target_entry_mods_def, compile_get_target_ptr_def, comp_return_def] >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G0`, `es`, `INL (PlaceR (MemoryPlace id []))`, `s0`, `tn0`] >>
  conj_tac
  >- simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def] >>
  simp[gas_origin_ptr_path_rules] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_all_then (qspec_then `sa` (strip_assume_tac o REWRITE_RULE [LET_THM]))
    (SIMP_RULE (srw_ss()) [LET_THM] (Q.INST [`trace` |-> `es.storage_trace`]
      ordinary_root_frames)) >>
  simp[write_target_post_mods_def, ghost_kept_at_refl, value_type_place_def] >>
  conj_tac
  >- metis_tac[local_ptrs_reserved_def] >>
  conj_tac
  >- (irule ordinary_root_pointer_local >> conj_tac >- (qexists_tac `sz` >> simp[]) >>
      qexistsl_tac [`DF H`, `cx`, `d`, `entry`, `es`, `lo`] >> simp[]) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule_all local_ptrs_rel_value >> strip_tac >>
  simp[write_target_location_mods_def, place_readable_def, place_ptr_rel_def,
       read_place_def, get_scopes_def, bind_def, lift_option_type_def,
       lift_sum_def, return_def, read_memory_path_def, evaluate_subscripts_def,
       mem_path_offset_def, eval_operand_def, WORD_ADD_0] >>
  fs[eval_operand_def]
QED

Theorem ordinary_root_slot[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (decl,key) /\
  var_decl_transient decl = tr /\
  lookup_var_slot_from_layout cx tr src key = SOME slot ==>
  FLOOKUP cenv.ce_module_vars (src,id) =
    SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))
Proof
  strip_tac >> drule_then assume_tac stmt_state_rel_state_rel >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by fs[state_rel_def] >>
  drule_all toplevel_decl_ce_vars >> simp[]
QED

Theorem ordinary_root_map_table[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  type_place_target env (TopLevelNameTarget (src,id)) = SOME (HashMapT kt vt) ==>
  ?tr. cenv.ce_hashmap_info (src,id) = SOME (tr,kt,vt)
Proof
  strip_tac >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_all_then assume_tac type_place_target_global_lookup >>
  `place_map_tables_agree_on_defined cenv env` by fs[expr_sim_inv_mods_def] >>
  qpat_x_assum `place_map_tables_agree_on_defined _ _`
    (mp_tac o REWRITE_RULE [place_map_tables_agree_on_defined_def]) >>
  disch_then drule >> Cases_on `cenv.ce_hashmap_info (src,id)` >> simp[] >>
  PairCases_on `x` >> simp[]
QED

(* Resolve the slot only under a valid horizon. When it is invalid the
   same source equation supplies the empty-prefix bad-storage alternative. *)
Theorem ordinary_global_root_run[local]:
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (TopLevelNameTarget (src,id)) es st0 sa sb shadow_sa shadow_sb r s0 G0 tn0 /\
  (!tail. eval_base_place cx (TopLevelNameTarget (src,id)) (es with gas_obs := tail) =
    (INL pv, es with <|storage_trace := es.storage_trace ++ events; gas_obs := tail|>)) /\
  (!H. valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx es s0 ==>
    sb = sa /\ r = (Lit w,SOME loc,SOME (value_type_place vt))) /\
  target_ptr_ok cenv pv (Lit w,SOME loc,SOME (value_type_place vt)) G0 tn0 s0 /\
  write_target_location_mods cenv cx (TopLevelNameTarget (src,id))
    (es with <|storage_trace := es.storage_trace ++ events; gas_obs := []|>)
    pv vt (Lit w,SOME loc,SOME (value_type_place vt)) G0 s0 ==>
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_base_place cx (TopLevelNameTarget (src,id)))
    (es,s0,G0,tn0)
    (\H res ee G tn t. ?pv. res = INL pv /\
      write_target_post_mods H (DF H) lo d ctx func cenv cx
        (TopLevelNameTarget (src,id)) es sa sb s0 ee pv vt r G0 tn0 G tn t) R
Proof
  strip_tac >> gvs[write_target_entry_mods_def] >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G0`, `es with storage_trace := es.storage_trace ++ events`,
                `INL pv`, `s0`, `tn0`] >>
  simp[gas_origin_ptr_path_rules] >> rpt strip_tac >>
  drule_then assume_tac gasOutcomeFullTheory.valid_horizon_append >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!H. _ /\ stmt_state_rel _ _ _ _ _ _ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  drule_all_then (qspecl_then [`es.storage_trace ++ events`, `sa`]
    (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM])) ordinary_root_frames >>
  simp[write_target_post_mods_def, ghost_kept_at_refl]
QED

Theorem write_toplevel_ordinary_root_stage_mods:
  expr_sim_inv_mods mods cenv cx env es /\
  ~immutable_root cx (TopLevelNameTarget (src,id)) ==>
  write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env (TopLevelNameTarget (src,id)) es
Proof
  strip_tac >> rw[write_base_sim_mods_def] >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `!ts. get_module_code cx src = SOME ts ==> find_var_decl_by_name id ts <> NONE` by
    (qpat_x_assum `~immutable_root _ _` mp_tac >>
     simp[immutable_root_def, target_root_def]) >>
  drule_all toplevel_target_decl >> strip_tac >> gvs[]
  >- suspend "storage" >> suspend "mapping"
QED

Resume write_toplevel_ordinary_root_stage_mods[storage]:
  `cenv.ce_hashmap_info (src,id) = NONE /\ cenv.ce_module_var_type (src,id) = SOME ty` by
    (qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
     qpat_assum `!src id ts tr typ id_str. _ ==> cenv.ce_hashmap_info _ = NONE /\ _`
       (drule_all_then strip_assume_tac) >> simp[]) >>
  irule ordinary_global_root_run >>
  (reverse conj_tac >- (qexistsl_tac [`shadow_func`, `shadow_sa`, `shadow_sb`] >> simp[])) >>
  qexistsl_tac [`[StorageRoot tr slot tv]`, `slot_loc tr`,
                `PlaceR (StoragePlace tr (n2w slot) tv)`, `n2w slot`] >>
  simp[target_ptr_ok_def, op_taint_def, op_prov_def, write_target_location_mods_def,
       place_ptr_rel_def, place_readable_def, eval_operand_def] >>
  conj_tac
  >- simp[Once evaluate_def, lookup_global_def, bind_def, ignore_bind_def,
          record_storage_event_def, lift_option_type_def, return_def, LET_THM] >>
  rpt strip_tac >> drule_all_then assume_tac
    (SIMP_RULE (srw_ss()) [var_decl_transient_def] (Q.INST
      [`decl` |-> `StorageVarDecl tr ty`] ordinary_root_slot)) >>
  qhdtm_x_assum `write_target_entry_mods`
    (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  qpat_x_assum `compile_get_target_ptr _ cenv _ sa = _` mp_tac >>
  Cases_on `tr` >> simp[compile_get_target_ptr_def, comp_return_def, LET_THM,
                        value_type_place_def, slot_loc_def]
QED

Resume write_toplevel_ordinary_root_stage_mods[mapping]:
  drule_all_then strip_assume_tac ordinary_root_map_table >>
  irule ordinary_global_root_run >>
  (reverse conj_tac >- (qexistsl_tac [`shadow_func`, `shadow_sa`, `shadow_sb`] >> simp[])) >>
  qexistsl_tac [`[]`, `slot_loc tr`, `HashMapRef tr (n2w slot) kt vt'`, `n2w slot`] >>
  simp[target_ptr_ok_def, op_taint_def, op_prov_def, write_target_location_mods_def,
       place_ptr_rel_def, place_readable_def, eval_operand_def] >>
  conj_tac
  >- simp[Once evaluate_def, lookup_global_def, bind_def,
          lift_option_type_def, return_def, LET_THM] >>
  rpt strip_tac >> drule_all_then assume_tac
    (SIMP_RULE (srw_ss()) [var_decl_transient_def] (Q.INST
      [`decl` |-> `HashMapVarDecl tr kt vt'`] ordinary_root_slot)) >>
  qhdtm_x_assum `write_target_entry_mods`
    (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  qpat_x_assum `compile_get_target_ptr _ cenv _ sa = _` mp_tac >>
  Cases_on `tr` >> simp[compile_get_target_ptr_def, comp_return_def, LET_THM,
                        value_type_place_def, slot_loc_def]
QED

Finalise write_toplevel_ordinary_root_stage_mods

Theorem write_ordinary_root_stage_mods:
  (expr_sim_inv_mods mods cenv cx env es ==>
    write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx env (NameTarget id) es) /\
  (expr_sim_inv_mods mods cenv cx env es /\
   ~immutable_root cx (TopLevelNameTarget (src,id)) ==>
    write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx env (TopLevelNameTarget (src,id)) es)
Proof
  conj_tac >- ACCEPT_TAC write_local_root_stage_mods >>
  ACCEPT_TAC write_toplevel_ordinary_root_stage_mods
QED
