(* Remaining-location reads and frames at one counted endpoint. *)
Theory bodyIntCallHeldRemainingRead
Ancestors
  bodyIntCallHeldCopyValue bodyIntCallHeldStorageWord
  bodyIntCallHeldImmutableCopy bodyIntCallHeldImmutableWord
  bodyIntCallStorageTyped freshWrites gasSummary exprSimMemorySource
  loweringPosts venomState compileEnv exprLoweringProps

Theorem storage_unwrap_held_tail:
  unwrap_value ce (LocatedValue sty p) sa = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type sty /\ fn_has_code sa sb func /\
  type_memory_bytes ce sty < dimword(:256) /\
  sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  alloca_room ctx func s /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ expr_sim_inv ce cx env es /\
  vv_holds ce cx ty raw (LocatedValue sty p) es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  intcall_held_args ce cx start sa es s H ==>
  ?z v b. gas_marked_path F ctx func s 0 (OK z) /\
    read_result cx raw es = (INL v,es) /\ expr_val_rel cx ty v op z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    FLOOKUP z.vs_allocas sa.cs_next_id = SOME (b,type_memory_bytes ce sty) /\
    val_wf tv v /\ val_in_memory tv v b z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\ b = s.vs_alloca_next /\
    wb_frame ce es sa s z /\ intcall_held_args ce cx start sb es z H
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all storage_typed_unwrap_path >> strip_tac >>
  `ci_mono sa sm /\ ci_mono sa sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_unwrap_value, pairTheory.SND] >>
  `u.vs_memory = s.vs_memory` by
    (qpat_x_assum `u with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` (mp_tac o GSYM) >>
     simp[venom_state_component_equality]) >>
  `wb_frame ce es sa s z` by
    (irule fresh_allocation_copy_wb_frame >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`sa.cs_next_id`, `type_slot_size tv`, `p.ptr_location`,
       `type_slot_size tv`, `type_memory_bytes ce sty`, `sm`, `a`, `u`] >>
     gvs[ci_mono_def]) >>
  `intcall_held_args ce cx start sb es z H` by
    (irule intcall_held_allocation_copy_frame >>
     goal_assum (drule_at (Pat `intcall_held_args _ _ _ _ _ _ _`)) >>
     gvs[ci_mono_def] >> metis_tac[]) >>
  qexistsl_tac [`z`, `v`, `b`] >> simp[]
QED
