(* A typed write to a nonlocal registered window preserves the state relation
   at the same horizon, and the ghost invariant at the same dead set. *)
Theory bodyMakeSlotRegisteredStateMods
Ancestors
  bodyStructFieldCutsMods bodyIfExpTypedGhostMods bodyFullPostsMods bodyInvSplit
  stateRelProj exprLoweringProps localPtrsProps loweringStateRelDefs
  typedMemoryCopy compileEnv venomState finite_map alist arithmetic

val _ = Parse.hide "base";

Theorem make_slot_registered_state_ghost_mods:
  stmt_state_rel H ctx func ce cx mid u /\
  ghost_inv_at_mods D lo d ce cx mid g1 tt1 u /\
  immutable_frame_mods func ce cx mid t /\
  ALOOKUP ce.ce_modules ce.ce_module = SOME tops /\
  local_ptrs_reserved ce sm /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  lo <= base /\ off + type_memory_size dtv <= cap /\
  FLOOKUP u.vs_allocas aid = SOME (base,cap) /\
  (!name b n. local_region ce mid.scopes u name b n ==>
     loweringStateRelDefs$regions_disjoint base cap b n) /\
  struct_store_effects func (sm,g1,tt1,u) (sb,gf,tf,t) (base+off,dtv,v) ==>
  stmt_state_rel H ctx func ce cx mid t /\ ghost_inv_at_mods D lo d ce cx mid gf tf t
Proof
  strip_tac >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor mid t /\
   immutable_alloca_sep func ce cx mid t` by
    (qpat_assum `immutable_frame_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE
          [immutable_frame_mods_def,immutables_rel_mods_def,immutable_alloca_sep_mods_def]) >>
     conj_tac
     >- (qpat_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ _` (drule_then ACCEPT_TAC)) >>
     `ce with ce_module := ce.ce_module = ce` by simp[compile_env_component_equality] >>
     qpat_assum `ce with ce_module := ce.ce_module = ce` (fn eq =>
       qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ _`
         (drule_then (ACCEPT_TAC o PURE_REWRITE_RULE [eq])))) >>
  fs[struct_store_effects_def] >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `!name b n. local_region ce mid.scopes u name b n ==>
     loweringStateRelDefs$regions_disjoint (base+off) (type_memory_size dtv) b n` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!name b n. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  reverse conj_tac
  >- (irule ifexp_typed_copy_ghost_mods >>
      qpat_assum `typed_copy_state_frame _ _ _ _ _` (irule_at Any) >>
      qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `local_ptrs_rel _ _ _ _` (irule_at Any) >>
      simp[] >> conj_tac >> first_assum ACCEPT_TAC) >>
  fs[typed_copy_state_frame_def, typed_copy_frame_def, venom_state_component_equality] >>
  `local_ptrs_rel func ce mid.scopes t` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `u` >> simp[] >>
     conj_tac
     >- (rpt strip_tac >> sym_tac >>
         qpat_assum `!a n. _ ==> mem_bytes_at a n _ = _` irule >>
         qpat_assum `!name b n. _ ==> loweringStateRelDefs$regions_disjoint (_ + _) _ _ _` drule >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at _ x ==> lookup_var x _ = _` irule >>
         fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     rpt strip_tac >> gvs[]) >>
  `state_rel H func ce cx mid t` by
    (irule state_rel_frame >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`mid`,`u`] >> simp[] >>
     drule_then ACCEPT_TAC stmt_state_rel_state_rel) >>
  `immutable_base_zero ce t` by
    (irule immutable_base_zero_frame >> qexists_tac `u` >>
     simp[] >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at _ x ==> lookup_var x _ = _` irule >>
         drule_all local_ptrs_reserved_imm_base >> simp[]) >>
     drule_then ACCEPT_TAC stmt_state_rel_immutable_base_zero) >>
  irule stmt_state_rel_allocas_frame >> simp[] >>
  qexistsl_tac [`mid`,`u`] >> simp[]
QED
