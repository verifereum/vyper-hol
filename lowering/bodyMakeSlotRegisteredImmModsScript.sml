(* A store into a registered row leaves every linked owner's immutable bytes alone. *)
Theory bodyMakeSlotRegisteredImmMods
Ancestors
  bodyFullPostsMods bodyInvSplit bodyInvCodeProps immutableRegionTypingProps
  exprLoweringProps loweringSlice typedMemoryCopy loweringStateRelDefs
  venomState compileEnv vyperTypeInvariants

Theorem registered_immutable_region_disjoint[local]:
  contract_inv mods exps ctx ce cx /\ expr_sim_inv_mods mods ce cx env es /\
  env_consistent env cx mid /\ ce.ce_is_ctor /\
  immutable_alloca_sep func (ce with ce_module := owner) cx mid u /\
  FLOOKUP ce.ce_module_vars (owner,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables owner imms) name = SOME (tv,v) /\
  FLOOKUP u.vs_allocas aid = SOME (b0,cap) ==>
  regions_disjoint off (type_memory_size tv) b0 cap
Proof
  strip_tac >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  `?bytes. immutable_region_mods mods owner name off bytes` by
    metis_tac[] >>
  drule_all_then strip_assume_tac immutable_region_mods_type >>
  `evaluate_type (get_tenv cx) ty = SOME tv` by
    (qpat_assum `env_consistent env cx mid`
       (mp_tac o cj 3 o REWRITE_RULE [env_consistent_def]) >>
     simp[env_immutables_consistent_def] >>
     disch_then (qspecl_then [`owner`,`name`,`ty`,`tv`,`v`] mp_tac o cj 2) >>
     Cases_on `ALOOKUP mid.immutables cx.txn.target` >> gvs[]) >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
  simp[immutable_alloca_sep_def, immutable_decl_sep_def] >> strip_tac >>
  qpat_assum `!name ty tv off. _ ==> _` (qspecl_then [`name`,`ty`,`tv`,`off`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem make_slot_registered_immutable_frame_mods:
  contract_inv mods exps ctx ce cx /\ expr_sim_inv_mods mods ce cx env es /\
  env_consistent env cx mid /\ immutable_frame_mods func ce cx mid u /\
  local_ptrs_reserved ce sm /\ FLOOKUP u.vs_allocas aid = SOME (b0,cap) /\
  off+n <= cap /\ typed_copy_state_frame sm (b0+off) n u t ==>
  immutable_frame_mods func ce cx mid t
Proof
  strip_tac >>
  `typed_copy_state_frame sm b0 cap u t` by
    (irule typed_copy_state_frame_subinterval >> qexistsl_tac [`b0+off`,`n`] >>
     simp[] >> decide_tac) >>
  qpat_x_assum `typed_copy_state_frame sm (b0+off) n u t` kall_tac >>
  qpat_x_assum `typed_copy_state_frame sm b0 cap u t`
    (strip_assume_tac o SRULE [typed_copy_state_frame_def,venom_state_component_equality]) >>
  fs[immutable_frame_mods_def,immutables_rel_mods_def,immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (qx_genl_tac [`owner`,`tops`] >> disch_tac >>
      irule immutables_rel_mem_agree >> qexists_tac `u` >> simp[] >>
      fs[typed_copy_frame_def] >> rpt strip_tac >>
      first_x_assum irule >> simp[GSYM regions_disjoint_def] >>
      `immutable_alloca_sep func (ce with ce_module := owner) cx mid u` by
        (first_x_assum irule >> qexists_tac `tops` >> simp[]) >>
      drule_all_then ACCEPT_TAC registered_immutable_region_disjoint) >>
  qx_genl_tac [`owner`,`tops`] >> disch_tac >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`u`,`mid`] >> simp[] >>
  rpt strip_tac >> rename1 `local_region _ _ t name b len` >> qexists_tac `name` >>
  qpat_x_assum `local_region _ _ t _ _ _` mp_tac >> simp[local_region_def] >>
  rpt strip_tac >>
  `not_fresh_at sm p` by metis_tac[local_ptrs_reserved_def] >>
  metis_tac[]
QED
