(* Restore the immutable memory relation after a root constructor write. *)
Theory immutableDeployAssignMemoryFrame
Ancestors
  immutableDeployAssignSourceFrame immutableDeployAssignFacts exprSimHypsDefs
  compileEnv loweringStateRelDefs valueEncodingProps valueTypingMemoryProps vyperTypeEnv
  vyperTypeInvariants vyperState finite_map

Theorem immutable_store_immutables_frame:
  immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es s /\
  expr_sim_inv ce cx env es /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  write_place cx (ImmutablePlace ce.ce_module id []) v es = (INL (),es') /\
  immutable_value_admissible tv v /\ val_in_memory tv v off q.vs_memory /\
  immutable_value_bytes_rel tv v
    (mem_bytes_at off (type_memory_size tv) q.vs_memory) /\
  (!a k. regions_disjoint a k off (type_memory_size tv) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es' q
Proof
  strip_tac >>
  `?mods old. ALOOKUP es.immutables cx.txn.target = SOME mods /\
    FLOOKUP (get_source_immutables ce.ce_module mods) id = SOME (tv,old)` by
    (drule_all immutable_assign_source_lookup >> simp[]) >>
  `bare_globals_layout ce.ce_is_ctor ce.ce_module_var_type ce.ce_module_vars
     cx env.bare_globals env.bare_global_assignable /\
   env_immutables_consistent env cx es /\ state_well_typed es` by
    fs[expr_sim_inv_def, env_consistent_def] >>
  qpat_x_assum `expr_sim_inv _ _ _ _` kall_tac >>
  `!name. FLOOKUP
    (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
     | SOME imms => get_source_immutables ce.ce_module imms) name =
    if name = id then SOME (tv,v)
    else FLOOKUP (get_source_immutables ce.ce_module mods) name` by
    (gen_tac >> drule_all immutable_root_write_lookup >>
     disch_then (qspec_then `name` mp_tac) >>
     Cases_on `ALOOKUP es'.immutables cx.txn.target` >>
     gvs[get_source_immutables_def]) >>
  fs[immutables_rel_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `name = id`
  >- (gvs[] >> metis_tac[]) >>
  gvs[] >>
  `?ty'. FLOOKUP env.bare_globals (ce.ce_module,name) = SOME ty'` by
    metis_tac[bare_globals_layout_def] >>
  `evaluate_type (get_tenv cx) ty' = SOME tv'` by
    (gvs[env_immutables_consistent_def] >>
     qpat_x_assum `!src id ty tv v. _ /\ _ ==> evaluate_type _ _ = _`
       (drule_all_then assume_tac) >> simp[]) >>
  `regions_disjoint byte_offset (type_memory_size tv') off
      (type_memory_size tv)` by
    (fs[bare_globals_layout_def] >>
     qpat_x_assum `!src id1 id2 ty1 ty2 off1 off2 tv1 tv2. _`
       (drule_all_then assume_tac) >> simp[]) >>
  `val_wf tv' v'` by
    (drule_all state_well_typed_immutables_ALOOKUP >> strip_tac >>
     drule_all imms_well_typed_get_source_immutables >>
     metis_tac[value_has_type_memory_wf]) >>
  `mem_bytes_at byte_offset (type_memory_size tv') q.vs_memory =
   mem_bytes_at byte_offset (type_memory_size tv') s.vs_memory` by metis_tac[] >>
  metis_tac[val_in_memory_mem_agree, arithmeticTheory.LESS_EQ_REFL]
QED
