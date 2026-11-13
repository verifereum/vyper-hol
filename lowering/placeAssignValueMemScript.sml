(* Location dispatch for strict widened aggregate place assignment.
   The actual-caller storage bound is exported by placeAssignAllocationBounds:
   assign_relayout_compiled_destination_bound uses target_post at the compiled
   pointer result, not an equality between destination and expression types. *)
Theory placeAssignValueMem
Ancestors
  placeMemoryContinuationMem placeStorageContinuationMem placeAssignAllocationBounds

Theorem place_assign_value_mem:
  !ce dst loc src dty sty src_loc sa sb a func ctx cx ee s env v stv p w ff d.
  (compile_assign_value ce dst loc src (is_word_type dty) src_loc dty sty
     (case dty of ArrayT et (Dynamic _) =>
        SOME ((type_memory_bytes ce et + 31) DIV 32, type_memory_bytes ce et)
      | _ => NONE) (type_memory_bytes ce dty) sa = ((),sb) /\
   (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
   fn_has_code a sa func /\ fn_has_code sa sb func /\
   fn_inst_ids_distinct func /\ local_ptrs_reserved ce a /\
   local_ptrs_reserved ce sa /\ ce.ce_target CapMcopy /\
   acyclic_struct_metadata ce.ce_struct_fields /\
   stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
   alloca_history func s /\ return_buf_frame d ce sa s /\
   eval_operand dst s = SOME w /\
   place_ptr_rel ce cx s (PlaceR p) w (SOME loc) (Type dty) /\
   (!x. dst = Var x ==> not_fresh_at sa x) /\
   (!x. src = Var x ==> not_fresh_at sa x) /\
   expr_val_rel cx sty v src s /\ expr_val_at ce cx sty a sa ee v src s /\
   expr_val_own ce cx sty a sa ee v src s /\
   evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
   type_widens_to (get_tenv cx) sty dty /\
   ~is_word_type sty /\ ~is_word_type dty /\
   ~is_bytestring_type sty /\ ~is_bytestring_type dty /\ sty <> dty /\
   storage_place_region cx p /\
   (!id path entry t0. p = MemoryPlace id path /\
      lookup_scopes id ee.scopes = SOME entry /\ ce.ce_var_type id = SOME t0 ==>
      evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
   write_place cx p v ee = (INL (),ff) /\
   ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
   s.vs_inst_idx = LENGTH sa.cs_current_insts /\
   ((loc = LocStorage \/ loc = LocTransient) ==>
      type_memory_bytes ce dty < dimword (:256))) ==>
  ?dtv t. evaluate_type (get_tenv cx) dty = SOME dtv /\
   gas_path_mem ctx func s 0 (OK t) /\ stmt_state_rel ctx func ce cx ff t /\
   alloca_history func t /\ return_buf_frame d ce sb t /\
   s.vs_alloca_next <= t.vs_alloca_next /\
   ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\ t.vs_labels = s.vs_labels /\
   (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
   LENGTH s.vs_memory <= LENGTH t.vs_memory /\
   (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
      aid < sa.cs_next_id /\
      (!name b len. local_region ce ee.scopes s name b len ==>
         off+sz <= b \/ b+len <= off) ==>
      mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory) /\
   (loc = LocMemory ==> val_in_memory dtv v (w2n w) t.vs_memory) /\
   (!off n. t.vs_alloca_next <= off ==>
      mem_bytes_at off n t.vs_memory = mem_bytes_at off n s.vs_memory)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `loc = LocMemory`
  >- (drule_all place_memory_assign_value_mem >> simp[]) >>
  `type_memory_bytes ce dty < dimword (:256)` by metis_tac[] >>
  drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)
    place_storage_assign_value_mem >> simp[] >>
  disch_then irule >> metis_tac[]
QED
