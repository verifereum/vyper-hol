(* Logical local updates at counted-copy endpoints, independent of cursor. *)
Theory widenedLocalContinuationMem
Ancestors
  widenedLocalCopyPathMem bodyDeclMemoryCore bodyMemAssignLocalMem
  exprLoweringProps venomState venomMemDefs compileEnv context

Theorem stmt_state_rel_copy_cursor[local]:
  stmt_state_rel ctx fn ce cx es
    (t with <|vs_current_bb := bb; vs_inst_idx := idx; vs_prev_bb := prev|>) <=>
  stmt_state_rel ctx fn ce cx es t
Proof
  `fmp_room ctx fn
    (t with <|vs_current_bb := bb; vs_inst_idx := idx; vs_prev_bb := prev|>) <=>
   fmp_room ctx fn t` by (irule fmp_room_fields_cong >> simp[]) >>
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
    local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
    transient_rel_def, accounts_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
    contract_storage_def, contract_transient_def, alloca_inv_def,
    allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
    pending_alloca_size_def, immutable_alloca_sep_def, immutable_base_zero_alt]
QED

Theorem typed_copy_assign_state:
  stmt_state_rel ctx fn ce cx es u /\
  find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p u = SOME dw /\ local_ptrs_reserved ce sa /\
  (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
    vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
    vs_prev_bb := u.vs_prev_bb|>) = u /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u) /\
  (!b n. b+n <= w2n dw \/ w2n dw+type_memory_size entry.type <= b ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n u.vs_memory) /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  val_wf entry.type v /\ val_in_memory entry.type v (w2n dw) t.vs_memory ==>
  stmt_state_rel ctx fn ce cx
    (es with scopes := pre ++ (env |+ (id,entry with <|value := v; popped := []|>))::rest) t
Proof
  strip_tac >>
  qabbrev_tac `z = t with <|vs_current_bb := u.vs_current_bb;
    vs_inst_idx := u.vs_inst_idx; vs_prev_bb := u.vs_prev_bb|>` >>
  `stmt_state_rel ctx fn ce cx
    (es with scopes := pre ++ (env |+ (id,entry with <|value := v; popped := []|>))::rest) z`
    suffices_by simp[Abbr `z`, stmt_state_rel_copy_cursor] >>
  irule local_memory_write_frame >>
  first_assum (irule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `find_containing_scope _ _ = _`)) >>
  first_assum (irule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  first_assum (irule_at (Pat `lookup_var _ _ = SOME _`)) >>
  first_assum (irule_at (Pat `local_ptrs_reserved _ _`)) >>
  fs[Abbr `z`, lookup_var_def] >>
  gvs[venom_state_component_equality]
QED

Theorem typed_copy_declare_state:
  stmt_state_rel ctx fn ce cx es u /\ fn_inst_ids_distinct fn /\
  es.scopes = sc::rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce es.scopes p /\ lookup_var p u = SOME dw /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa p /\
  (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
    vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
    vs_prev_bb := u.vs_prev_bb|>) = u /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u) /\
  (!b n. b+n <= w2n dw \/ w2n dw+type_memory_size dtv <= b ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n u.vs_memory) /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\ type_memory_size dtv <= sz /\
  val_wf dtv v /\ val_in_memory dtv v (w2n dw) t.vs_memory ==>
  stmt_state_rel ctx fn ce cx
    (es with scopes := (sc |+ (id,<|assignable := a; type := dtv; value := v; popped := []|>))::rest) t
Proof
  strip_tac >>
  qabbrev_tac `z = t with <|vs_current_bb := u.vs_current_bb;
    vs_inst_idx := u.vs_inst_idx; vs_prev_bb := u.vs_prev_bb|>` >>
  `stmt_state_rel ctx fn ce cx
    (es with scopes := (sc |+ (id,<|assignable := a; type := dtv; value := v; popped := []|>))::rest) z`
    suffices_by simp[Abbr `z`, stmt_state_rel_copy_cursor] >>
  irule body_stmt_state_rel_declare_store_frame >>
  first_assum (irule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `es.scopes = _`)) >>
  first_assum (irule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  first_assum (irule_at (Pat `lookup_var _ _ = SOME _`)) >>
  first_assum (irule_at (Pat `MEM _ (fn_insts _)`)) >>
  first_assum (irule_at (Pat `local_ptrs_reserved _ _`)) >>
  fs[Abbr `z`, lookup_var_def] >> gvs[venom_state_component_equality]
QED
