(* Resource transport for supplied default-copy endpoints. *)
Theory extcallReturnDefaultMemoryFrame
Ancestors
  bodyFullUnwrapSlotPost extcallReturnDefaultWordJoint exprSimBufferStore
  ptrDiscipline bodyPtrDefs loweringPosts exprSimProps venomState finite_map list pred_set

Theorem return_default_memory_ghost_frame:
  ghost_inv_at D lo d cenv cx ee G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  local_ptrs_rel func cenv ee.scopes s /\ lo <= start /\
  (!name b sz. local_region cenv ee.scopes s name b sz ==>
    start+nb <= b \/ b+sz <= start) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!a k. a+k <= start \/ start+nb <= a ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!j. j < start \/ start+nb <= j ==> (j IN tm.t_mem <=> j IN tn.t_mem)) /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm ==>
  ghost_inv_at D lo d cenv cx ee G' tm u
Proof
  strip_tac >>
  `lo <= u.vs_alloca_next /\ allocas_from lo u /\ stor_taint_ok_at D tm u` by
    (gvs[ghost_inv_at_def, stor_taint_ok_at_def, allocas_from_def,
         venom_state_component_equality] >> gvs[]) >>
  irule unwrap_slot_copy_ghost_inv_at >> simp[] >>
  goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  qexistsl_tac [`nb`, `sa`, `start`] >> simp[] >>
  gvs[ghost_inv_at_def, stor_taint_ok_at_def, allocas_from_def,
      venom_state_component_equality] >> metis_tac[]
QED

Theorem return_default_memory_state_frame:
  stmt_state_rel H ctx func cenv cx ee s /\ local_ptrs_reserved cenv sa /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!a k. a+k <= start \/ start+nb <= a ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!name b sz. local_region cenv ee.scopes s name b sz ==>
    b+sz <= start \/ start+nb <= b) /\
  LENGTH s.vs_memory <= LENGTH u.vs_memory /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) start nb) ==>
  stmt_state_rel H ctx func cenv cx ee u
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee (u with vs_inst_idx := s.vs_inst_idx)` suffices_by
    simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
  irule buffer_store_state_frame >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`start`, `nb`, `sa`] >>
  gvs[lookup_var_def, venom_state_component_equality] >> metis_tac[]
QED

Theorem return_default_memory_wb_frame:
  wb_frame cenv es ee sa s0 s /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  u.vs_allocas = s.vs_allocas /\
  (!aid b sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    b+sz <= start \/ start+nb <= b) /\
  (!name b sz. local_region cenv es.scopes s0 name b sz ==>
    b+sz <= start \/ start+nb <= b) /\
  (!a k. a+k <= start \/ start+nb <= a ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  wb_frame cenv es ee sa s0 u
Proof
  strip_tac >>
  qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
  rewrite_tac[wb_frame_def] >> strip_tac >>
  simp[wb_frame_def] >>
  conj_tac >- metis_tac[] >>
  irule locals_kept_regions_tail >> qexists_tac `s` >> simp[] >>
  metis_tac[]
QED
