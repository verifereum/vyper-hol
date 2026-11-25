(* Assemble the reached word slot on its actual empty-mark suffix. *)
Theory bodyMakeSlotWordMods
Ancestors
  bodyMakeSlotWordSuffixMods bodyMakeSlotAnchorWriteMods bodyMakeSlotRangeFramesMods
  bodyMakeSlotRegisteredImmMods bodyMakeSlotRegisteredStateMods
  bodyStructFieldsSourceMods gasOutcomeFullPostMods bodyFullIfExpReach
  wordArgsPtr exprSimWordArgs exprSimCopy bodyMemoryDefs exprSimFullBundleProps
  bodyInvCodeProps stateRelProj bodyFullPostsMods assignTuplePtrCopyLen
  bodyMakeElementsContractMods vyperStorageTrace vyperStorageFootprint
  exprSimMemorySource loweringPosts loweringStateRelDefs exprSimUnwrap
  gasOutcomeFull freshWrites list arithmetic finite_map bodyStructFieldCutsMods
  typedMemoryCopy venomState exprBodyPreProps bodyInvSplit bodyPtrDefs fragGasOriginPtr

val _ = Parse.hide "base";

Theorem make_slot_word_landing_mods:
  make_slot_landing_mods is_word_type
Proof
  rewrite_tac[make_slot_landing_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac make_slot_word_suffix_mods >>
  qhdtm_x_assum `make_slot_entry_mods`
    (strip_assume_tac o REWRITE_RULE[make_slot_entry_mods_def,make_elements_entry_mods_def]) >>
  qhdtm_x_assum `make_elements_static_mods`
    (strip_assume_tac o REWRITE_RULE[make_elements_static_mods_def]) >>
  qhdtm_x_assum `make_elements_cut_mods`
    (strip_assume_tac o REWRITE_RULE[make_elements_cut_mods_def]) >>
  `expr_body_pre_mods mods cenv cx env h es` by simp[] >>
  qhdtm_x_assum `make_elements_admissible_mods`
    (assume_tac o REWRITE_RULE[make_elements_admissible_mods_def]) >>
  drule_all_then strip_assume_tac struct_fields_source_cuts_mods >>
  `?events. mid.storage_trace = es.storage_trace ++ events` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     `storage_trace_frame (eval_expr cx h)` by simp[cj 5 evaluate_storage_trace_frame] >>
     drule_all storage_trace_frame_prefix >> simp[]) >>
  `?evs. mid.storage_trace = ebase.storage_trace ++ evs` by
    (qpat_assum `mid.storage_trace = es.storage_trace ++ _` mp_tac >>
     qpat_assum `es.storage_trace = ebase.storage_trace ++ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[APPEND_ASSOC]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s /\
   stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx ebase sbase` by
    suspend "entry_horizons" >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ make_slot_child_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE[make_slot_child_post_mods_def,sumTheory.INL_11])) >>
  `wb_frame cenv es mid sa s u /\ (~expr_has_effect h ==> pure_frame cenv func es sa s u)` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ u`
       (strip_assume_tac o REWRITE_RULE[vv_post_mods_def]) >>
     rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `compile_expr cenv (expr_type h) h sa = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  `local_ptrs_reserved cenv sm` by suspend "reserved" >>
  `(!name b n. local_region cenv mid.scopes u name b n ==>
     loweringStateRelDefs$regions_disjoint base cap b n) /\
   wb_frame cenv ebase mid csbase sbase t /\
   ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase gf tf` by suspend "anchor" >>
  drule_all_then strip_assume_tac make_slot_range_frames_mods >>
  `make_elements_cut_mods DF lo d ctx func cenv cx st0
    (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) sb mid t gf tf /\
   make_elements_save_mods s t` by suspend "endpoint" >>
  suspend "finish"
QED

Resume make_slot_word_landing_mods[entry_horizons]:
  conj_tac
  >- (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by
        (irule valid_horizon_append >> qexists_tac `events'` >>
         qpat_assum `mid.storage_trace = es.storage_trace ++ events'`
           (fn th => pure_once_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
      qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H ebase.storage_trace ==> _` irule >>
  irule valid_horizon_append >> qexists_tac `evs` >>
  qpat_assum `mid.storage_trace = ebase.storage_trace ++ evs`
    (fn th => pure_once_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC
QED

Resume make_slot_word_landing_mods[reserved]:
  irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]
QED

Resume make_slot_word_landing_mods[anchor]:
  `MAP FDOM ebase.scopes = MAP FDOM mid.scopes` by metis_tac[] >>
  `wb_frame cenv ebase mid csbase sbase u` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ebase sbase`
       (mp_then Any irule wb_frame_trans) >>
     simp[] >> qexistsl_tac [`es`,`sa`,`s`] >> simp[]) >>
  `ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase g1 tt1` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ebase sbase`
       (mp_then Any irule ghost_kept_at_wb_trans) >>
     simp[] >> qexistsl_tac [`G`,`es`,`es`,`s`,`sa`,`tn`] >> simp[]) >>
  `!name b n. local_region cenv es.scopes s name b n <=>
               local_region cenv mid.scopes u name b n` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx es s`
       (mp_then Any mp_tac wb_frame_local_regions) >>
     disch_then (qspecl_then [`sa`,`u`,`mid`,`mid`] mp_tac) >> simp[]) >>
  `!name b n. local_region cenv ebase.scopes sbase name b n <=>
               local_region cenv es.scopes s name b n` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ebase sbase`
       (mp_then Any mp_tac wb_frame_local_regions) >>
     disch_then (qspecl_then [`csbase`,`s`,`es`,`es`] mp_tac) >> simp[]) >>
  `!name b n. local_region cenv mid.scopes u name b n ==>
     loweringStateRelDefs$regions_disjoint base cap b n` by metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `FLOOKUP u.vs_allocas aid = SOME (base,cap)` by
    (qpat_assum `wb_frame cenv es mid sa s u`
       (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >> simp[]) >>
  `alloca_inv u` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ u`
       (strip_assume_tac o REWRITE_RULE[vv_post_mods_def]) >>
     qpat_assum `stmt_state_rel _ _ _ _ _ mid u`
       (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >> first_assum ACCEPT_TAC) >>
  `csbase.cs_next_var <= sm.cs_next_var` by decide_tac >>
  `!name b n. local_region cenv ebase.scopes sbase name b n ==> b+n <= base \/ base+cap <= b` by
    (rpt strip_tac >>
     `local_region cenv es.scopes s name b n` by
       (qpat_assum `!name b n. local_region cenv ebase.scopes sbase name b n <=> _`
          (fn th => pure_once_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!name b n. local_region cenv es.scopes s name b n ==> _` (drule_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  irule make_slot_anchor_write_mods >>
  qpat_assum `struct_store_effects _ _ _ _` (irule_at Any) >>
  qpat_assum `FLOOKUP u.vs_allocas aid = SOME (base,cap)` (irule_at Any) >>
  asm_simp_tac bool_ss [] >>
  rpt strip_tac >>
  qpat_assum `!name b n. local_region cenv mid.scopes u name b n ==> _`
    (drule_then mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Resume make_slot_word_landing_mods[endpoint]:
  qpat_assum `struct_store_effects _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[struct_store_effects_def,expr_sim_full_endpoint_def]) >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (strip_assume_tac o SRULE[typed_copy_state_frame_def,venom_state_component_equality]) >>
     simp[EQ_SYM_EQ]) >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[typed_copy_state_frame_def]) >> first_assum ACCEPT_TAC) >>
  `not_fresh_at sm q /\ not_fresh_at sb q` by metis_tac[not_fresh_at_mono] >>
  `lookup_var q u = SOME (n2w base)` by
    (irule wb_frame_vars >>
     qpat_assum `wb_frame cenv es mid sa s u` (irule_at Any) >> simp[]) >>
  `ptr_covers g1 tt1 q u cap` by
    (qpat_assum `ghost_kept_at lo cenv es sa G tn s g1 tt1`
       (strip_assume_tac o REWRITE_RULE[ghost_kept_at_def]) >>
     irule ptr_covers_lookup_frame >> qpat_assum `ptr_covers G tn q s cap` (irule_at Any) >> simp[]) >>
  `lookup_var q t = SOME (n2w base) /\ ptr_covers gf tf q t cap` by
    (simp[] >> irule ptr_covers_lookup_frame >> qpat_assum `ptr_covers g1 tt1 q u cap` (irule_at Any) >> simp[]) >>
  `return_buf_frame d cenv sm u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >> simp[] >>
     metis_tac[wb_frame_vars]) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`u`,`sm`] >> simp[]) >>
  `(!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z) /\
   (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z)` by
    suspend "headroom" >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\ immutable_frame_mods func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx mid gf tf t`
    by suspend "state" >>
  suspend "close_cut"
QED

Resume make_slot_word_landing_mods[headroom]:
  conj_asm1_tac
  >- (qx_genl_tac [`f`,`i`,`z`] >> disch_tac >> irule gas_origin_ptr_path_dalloca_fmp_headroom >>
      qpat_assum `gas_origin_ptr_path _ (s,G,tn) marks (OK u,g1,tt1)` (irule_at Any) >>
      qexists_tac `f` >> asm_rewrite_tac[]) >>
  qx_genl_tac [`f`,`i`,`z`] >> disch_tac >> irule gas_origin_ptr_path_dalloca_fmp_headroom >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ (u,g1,tt1) _ _`
    (drule_then (irule_at Any)) >> qexists_tac `f` >> asm_rewrite_tac[]
QED

Resume make_slot_word_landing_mods[state]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ make_slot_child_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE[make_slot_child_post_mods_def,sumTheory.INL_11])) >>
  qpat_assum `vv_post_mods H ctx func cenv cx h es sa sm s mid _ vv u`
    (strip_assume_tac o REWRITE_RULE[vv_post_mods_def]) >>
  `FLOOKUP u.vs_allocas aid = SOME (base,cap)` by simp[] >>
  `env_consistent env cx mid` by (drule expr_sim_inv_mods_env >> simp[]) >>
  `immutable_frame_mods func cenv cx mid t` by
    (irule make_slot_registered_immutable_frame_mods >>
     qpat_assum `typed_copy_state_frame sm (base+off) _ u t` (irule_at Any) >>
     qpat_assum `contract_inv mods exps ctx cenv cx` (irule_at Any) >>
     qpat_assum `expr_sim_inv_mods mods cenv cx env ebase` (irule_at Any) >>
     qpat_assum `FLOOKUP u.vs_allocas aid = SOME (base,cap)` (irule_at Any) >> simp[]) >>
  `ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops` by
    (drule_then SUBST1_TAC contract_inv_cenv_modules >> fs[module_body_inv_def]) >>
  `stmt_state_rel H ctx func cenv cx mid t /\ ghost_inv_at_mods (DF H) lo d cenv cx mid gf tf t` by
    (irule make_slot_registered_state_ghost_mods >>
     qpat_assum `struct_store_effects func _ _ _` (irule_at Any) >>
     qpat_assum `FLOOKUP u.vs_allocas aid = SOME (base,cap)` (irule_at Any) >>
     qpat_assum `ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops` (irule_at Any) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx mid u` (irule_at Any) >>
     qpat_assum `ghost_inv_at_mods (DF H) lo d cenv cx mid g1 tt1 u` (irule_at Any) >>
     asm_simp_tac bool_ss [] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `csbase` >>
         simp[] >> decide_tac) >>
     rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `csbase` >>
     simp[] >> decide_tac) >>
  asm_rewrite_tac[]
QED

Resume make_slot_word_landing_mods[close_cut]:
  `make_elements_save_mods s t` by
    (rewrite_tac[make_elements_save_mods_def] >>
     qpat_assum `wb_frame cenv es mid sa s u`
       (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >> simp[]) >>
  `make_elements_save_mods sbase t` by
    (fs[make_elements_save_mods_def] >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas aid = SOME (base,cap)` by fs[make_elements_save_mods_def] >>
  `MAP FDOM ebase.scopes = MAP FDOM mid.scopes` by metis_tac[] >>
  `aid < sb.cs_next_id /\ base+cap <= t.vs_alloca_next /\ sbase.vs_alloca_next <= t.vs_alloca_next`
    by decide_tac >>
  `!name b n. local_region cenv mid.scopes t name b n ==>
     loweringStateRelDefs$regions_disjoint base cap b n` by
    (rpt strip_tac >>
     `local_region cenv mid.scopes t name b n <=> local_region cenv mid.scopes u name b n` by
       (irule copy_buffer_local_region_frame >> qexists_tac `sm` >> simp[]) >>
     `local_region cenv mid.scopes u name b n` by
       (qpat_assum `local_region cenv mid.scopes t name b n <=> _`
          (fn th => pure_once_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!name b n. local_region cenv mid.scopes u name b n ==> _`
       (qspecl_then [`name`,`b`,`n`] (drule_then ACCEPT_TAC))) >>
  rewrite_tac[make_elements_cut_mods_def] >> conj_tac
  >- (conj_tac >- (qexists_tac `evs` >> first_assum ACCEPT_TAC) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Resume make_slot_word_landing_mods[finish]:
  `~u.vs_halted` by
    (drule_then strip_assume_tac gas_origin_ptr_path_projections >>
     drule fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted >> simp[]) >>
  rewrite_tac[make_elements_run_mods_def] >> irule gas_outcome_full_mods_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`gf`,`mid`,`INL v`,`t`,`tf`] >> conj_tac
  >- (drule read_result_gas_obs >> simp[]) >>
  `mid with gas_obs := [] = mid` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  gen_tac >> disch_tac >> conj_tac
  >- (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ (u,g1,tt1) _ _`
        (drule_then ACCEPT_TAC)) >>
  qpat_assum `struct_store_effects _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[struct_store_effects_def]) >>
  asm_rewrite_tac[make_slot_post_mods_def,make_elements_admissible_mods_def] >>
  qexists_tac `v` >> asm_rewrite_tac[]
QED

Finalise make_slot_word_landing_mods
