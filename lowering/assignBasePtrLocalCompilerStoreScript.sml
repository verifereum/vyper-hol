(* Compiler-facing local store. Runtime bytestring extents are recovered
   from robust representation; no header-cleanliness premise is needed. *)
Theory assignBasePtrLocalCompilerStore
Ancestors assignBasePtrLocalContinuation assignTuplePtrLocalCompat
  tupleLocalStoreRun bodyPtrDefs context compileEnv loweringStateRelDefs localPtrsProps
  vyperLookup valueEncoding valueEncodingProps valueTypingMemoryProps
  venomState venomExecSemantics exprSimProps exprLoweringProps exprSimBufferStore vfmConstants words finite_map

Theorem assign_base_local_store_memory_ptr:
  compile_store_memory cenv (Var src) (Var p) ty ty sa = ((),sb) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME entry.type /\
  value_has_type entry.type v /\
  type_memory_bytes cenv ty = type_memory_size entry.type /\
  type_memory_size entry.type + 64 < dimword (:256) /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  lookup_var src s = SOME sw /\
  ptr_covers G tn src s (if is_bytestring_type ty then val_store_size entry.type v
    else type_memory_size entry.type) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory entry.type v (w2n sw) m) /\
  ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    stmt_state_rel ctx fn cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) u /\
    ghost_inv d cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
      Gf tf u /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?dw. lookup_var p s = SOME dw` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  drule_all tuple_store_destination_region >> strip_tac >>
  `ptr_covers G tn p s sz` by metis_tac[ghost_inv_def] >>
  `val_wf entry.type v` by simp[value_has_type_memory_wf] >>
  `local_ptrs_rel fn cenv es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  Cases_on `is_bytestring_type ty`
  >- suspend "bytes" >>
  suspend "flat"
QED

Resume assign_base_local_store_memory_ptr[flat]:
  fs[] >>
  `compile_copy_memory (Var p) (Var src) (type_memory_size entry.type) sa = ((),sb)` by
    fs[compile_store_memory_def] >>
  `ptr_covers G tn p s (type_memory_size entry.type)` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  irule assign_base_flat_local_continuation_ptr >> simp[] >>
  qexistsl_tac [`sw`, `type_memory_size entry.type`, `src`] >> simp[val_footprint_le]
QED

Resume assign_base_local_store_memory_ptr[bytes]:
  drule_all bytestring_compatible_resources_ptr >> strip_tac >>
  `val_in_memory entry.type v (w2n sw) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all buffer_typed_bytestring_header >>
  disch_then (qx_choose_then `len2` strip_assume_tac) >>
  `len2 + 31 < dimword (:256)` by
    (irule buffer_round_no_wrap >>
     `val_store_size entry.type v <= type_memory_size entry.type` by
       metis_tac[val_store_size_le] >> decide_tac) >>
  `len2 = len` by (gvs[] >> fs[word_size_def] >> decide_tac) >>
  gvs[] >>
  `compile_store_bytestring (Var src) (Var p) sa = ((),sb)` by
    fs[compile_store_memory_def] >>
  `ptr_covers G tn src s 32 /\
   ptr_covers G tn src s (32 + 32 * word_size len) /\
   ptr_covers G tn p s (32 + 32 * word_size len)` by
    (fs[ptr_covers_def, word_size_def] >> rpt conj_tac >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  irule assign_base_bytes_local_continuation_ptr >> simp[word_size_def] >>
  goal_assum (drule_at Any) >> simp[word_size_def] >>
  qexists_tac `len` >> fs[word_size_def] >> decide_tac
QED

Finalise assign_base_local_store_memory_ptr
