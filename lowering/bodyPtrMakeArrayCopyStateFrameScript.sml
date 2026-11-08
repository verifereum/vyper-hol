Theory bodyPtrMakeArrayCopyStateFrame
Ancestors
  exprSimPtrLiteralBuffer exprSimStorageCopy exprLoweringProps compileEnv
  venomState venomExecSemantics venomMemDefs localPtrsProps loweringSlice

(* The cursor erased by copy_static is irrelevant to the source relation. *)
Theorem literal_stmt_state_rel_cursor:
  stmt_state_rel ctx func cenv cx es
    (s with <|vs_prev_bb := pb; vs_current_bb := bb; vs_inst_idx := idx|>) <=>
  stmt_state_rel ctx func cenv cx es s
Proof
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, immutable_alloca_sep_def,
       immutable_base_zero_alt, fmp_room_def, accounts_rel_def]
QED

Theorem literal_copy_window_stmt_state_rel:
  stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
  copy_static t = copy_static u /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  (!x. not_fresh_at sh x ==> lookup_var x t = lookup_var x u) /\
  (!name a len. local_region cenv es.scopes u name a len ==>
    regions_disjoint b n a len) /\
  (!a len. a+len <= b \/ b+n <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
  MEM (mk_inst aid ALLOCA [Lit (n2w n)] [p]) (fn_insts func) /\
  FLOOKUP u.vs_allocas aid = SOME (b,n) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  qabbrev_tac `z = t with <|vs_prev_bb := u.vs_prev_bb;
    vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx|>` >>
  `stmt_state_rel ctx func cenv cx es z` suffices_by
    simp[Abbr `z`, literal_stmt_state_rel_cursor] >>
  irule literal_ptr_state_memory_frame >>
  qexistsl_tac [`aid`, `b`, `n`, `p`, `sa`, `sh`, `u`] >>
  simp[Abbr `z`] >>
  qpat_x_assum `copy_static t = copy_static u` mp_tac >>
  simp[copy_static_def, venom_state_component_equality, lookup_var_def] >>
  metis_tac[lookup_var_def]
QED
