Theory immutableRegionFrameProps
Ancestors
  bodyInvSplit bodyInvCodeProps bodyFullShadowBodyInv exprBodyPreProps
  immutableRegionTypingProps immutableRegionDeadProps ctorDeployDeadSectionRel abiCanonicalHeadSize
  valueEncodingProps valueEncodingProofs loweringSlice vyperTypeInvariants
  loweringStateRelDefs stateRelProj vyperContext bodyPtrDefs finite_map

Theorem immutable_region_value_layout_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  cenv.ce_is_ctor /\ dead_lo_ok_mods H D lo cenv cx /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (rt,v) ==>
  immutable_region_mods mods src id off (type_memory_size rt) /\
  well_formed_type_value rt /\ off + type_memory_size rt <= lo /\
  (?ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\
        evaluate_type (get_tenv cx) ty = SOME rt)
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  `?bytes. immutable_region_mods mods src id off bytes` by metis_tac[] >>
  drule_all_then strip_assume_tac immutable_region_mods_type >>
  `evaluate_type (get_tenv cx) ty = SOME rt` by
    (qpat_assum `env_consistent env cx es`
       (mp_tac o cj 3 o REWRITE_RULE [env_consistent_def]) >>
     simp[env_immutables_consistent_def] >>
     disch_then (mp_tac o Q.SPECL [`src`,`id`,`ty`,`rt`,`v`] o cj 2) >>
     simp[]) >>
  `lo = imm_len_mods mods` by fs[dead_lo_ok_mods_def] >>
  gvs[] >>
  metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]
QED

Theorem immutable_region_mem_frame_mods[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env entry /\
  immutable_region_mods mods src id off (type_memory_size rt) /\
  off + type_memory_size rt <= lo /\
  well_formed_type_value rt /\ immutable_value_admissible rt v /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME rt /\
  val_in_memory rt v off s.vs_memory /\
  ghost_inv_at_mods D lo d cenv cx es G tn s ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v off mem
Proof
  strip_tac >>
  `val_wf rt v` by metis_tac[immutable_admissible_val_wf] >>
  `!m. mem_bytes_at off (type_memory_size rt) (mem_bytes_at 0 lo m) =
       mem_bytes_at off (type_memory_size rt) m` by
    simp[valueEncodingDefsTheory.mem_bytes_at_bounded,
         abiCanonicalHeadSizeTheory.mem_bytes_at_window] >>
  `val_in_memory rt v off (mem_bytes_at 0 lo s.vs_memory)` by
    (irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
     qexistsl_tac [`type_memory_size rt`, `s.vs_memory`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `val_in_memory rt v off (mem_bytes_at 0 lo mem)` suffices_by
    (strip_tac >> irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
     qexistsl_tac [`type_memory_size rt`, `mem_bytes_at 0 lo mem`] >> simp[]) >>
  irule section_value_memory_frame >> simp[] >>
  qexists_tac `mem_bytes_at 0 lo s.vs_memory` >> simp[] >>
  rpt strip_tac >>
  `j < lo` by decide_tac >>
  Cases_on `j IN tn.t_mem`
  >- (CCONTR_TAC >>
      `imm_section_dead_mods cenv (mem_bytes_at 0 lo s.vs_memory) j` by
        fs[ghost_inv_at_mods_def] >>
      drule_all_then (fn th => fs[th]) imm_section_dead_mods_regions >>
      rename1 `immutable_region_mods mods src' name' off' (type_memory_size tv)` >>
      drule (cj 1 ctorDeployDeadSectionTheory.mem_dead_bytes_range) >> strip_tac >>
      drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
        contract_inv_immutable_section_layout >>
      Cases_on `(src',name') = (src,id)`
      >- (gvs[] >>
          `FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
           FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off')` by metis_tac[] >>
          `off' = off` by metis_tac[optionTheory.SOME_11, compileEnvTheory.var_location_11] >>
          gvs[]) >>
      `regions_disjoint off (type_memory_size rt) off' (type_memory_size tv)` by metis_tac[] >>
      fs[regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at j 1 s.vs_memory = mem_bytes_at j 1 mem` by fs[mem_agree_outside_def] >>
  pop_assum (mp_tac o Q.AP_TERM `EL 0`) >>
  simp[valueEncodingProofsTheory.EL_mem_bytes_at]
QED

Theorem immutable_ctor_frame_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env entry /\
  cenv.ce_is_ctor /\ dead_lo_ok_mods H D lo cenv cx /\
  es.immutables = entry.immutables /\ stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (rt,v) ==>
  off + type_memory_size rt <= lo /\
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v off mem
Proof
  strip_tac >>
  `ALOOKUP entry.immutables cx.txn.target = SOME imms` by metis_tac[] >>
  drule_all_then strip_assume_tac immutable_region_value_layout_mods >>
  drule_then (strip_assume_tac o MATCH_MP state_rel_immutables_rel)
    stmt_state_rel_state_rel >>
  `immutable_value_admissible rt v /\ val_in_memory rt v off s.vs_memory` by
    (qpat_assum `immutables_rel _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [immutables_rel_def, LET_THM]) >>
     CONV_TAC (LAND_CONV BETA_CONV) >>
     disch_then (mp_tac o Q.SPECL [`id`,`rt`,`v`,`off`]) >>
     simp[]) >>
  simp[] >>
  mp_tac (Q.INST [`src` |-> `cenv.ce_module`] immutable_region_mem_frame_mods) >>
  simp[]
QED

Theorem qualified_immutable_ctor_frame_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env entry /\
  cenv.ce_is_ctor /\ dead_lo_ok_mods H D lo cenv cx /\
  es.immutables = entry.immutables /\
  ALOOKUP cenv.ce_modules src = SOME tops /\
  immutables_rel_mods cenv cx.txn.target cenv.ce_is_ctor es s /\
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (rt,v) ==>
  off + type_memory_size rt <= lo /\
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v off mem
Proof
  strip_tac >>
  `ALOOKUP entry.immutables cx.txn.target = SOME imms` by metis_tac[] >>
  drule_all_then strip_assume_tac immutable_region_value_layout_mods >>
  qpat_x_assum `immutables_rel_mods _ _ _ _ _`
    (drule_then mp_tac o REWRITE_RULE [immutables_rel_mods_def]) >>
  simp[immutables_rel_def] >>
  disch_then (qspecl_then [`id`,`rt`,`v`,`off`] mp_tac) >>
  simp[] >> strip_tac >>
  mp_tac immutable_region_mem_frame_mods >> simp[]
QED
