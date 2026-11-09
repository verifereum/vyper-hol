(* Memory and allocation frames for a constructor immutable write. *)
Theory immutableDeployAssignStateFrame
Ancestors
  immutableDeployAssignSourceFrame immutableDeployAssignFacts localPtrsProps
  valueEncodingProps exprLoweringProps compileEnv finite_map vyperPlaceFrames
  venomState

Theorem immutable_store_local_ptrs_frame:
  local_ptrs_rel func ce scopes s /\
  immutable_decl_sep ce cx scopes s.vs_vars s.vs_allocas s.vs_alloca_next /\
  ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
  q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
  (!a k. regions_disjoint a k off (type_memory_size tv) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  local_ptrs_rel func ce scopes q
Proof
  strip_tac >> irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
  rpt conj_tac
  >- (rpt strip_tac >> sym_tac >> first_x_assum irule >>
      fs[immutable_decl_sep_alt] >> metis_tac[regions_disjoint_def]) >>
  simp[] >> rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem immutable_store_alloca_sep_frame:
  immutable_alloca_sep func ce cx es s /\
  local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
  q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
  ALOOKUP es.immutables cx.txn.target = SOME mods /\
  FLOOKUP (get_source_immutables ce.ce_module mods) id = SOME (tv,old) /\
  write_place cx (ImmutablePlace ce.ce_module id []) v es = (INL (),es') ==>
  immutable_alloca_sep func ce cx es' q
Proof
  strip_tac >>
  `es'.scopes = es.scopes` by
    (drule write_immutable_place_frame >> strip_tac >> simp[]) >>
  `!name tv' v'.
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of
       NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
      name = SOME (tv',v') ==>
    ?v0. FLOOKUP (get_source_immutables ce.ce_module mods) name = SOME (tv',v0)` by
    (rpt strip_tac >>
     drule_all immutable_root_write_lookup >>
     disch_then (qspec_then `name` mp_tac) >>
     Cases_on `ALOOKUP es'.immutables cx.txn.target` >>
     gvs[] >> Cases_on `name = id` >> gvs[] >> metis_tac[]) >>
  fs[immutable_alloca_sep_def, immutable_decl_sep_def, local_region_def,
     lookup_var_def, local_ptrs_reserved_def] >>
  metis_tac[]
QED
