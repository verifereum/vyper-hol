(* Bytestring local endpoint for independently sized source and destination. *)
Theory assignTuplePtrLocalCoerce
Ancestors
  assignTuplePtrLocalRuntimeHead assignTuplePtrLocalCompat valueCopy
  assignTuplePtrLocalCopyRun tupleLocalStoreRun exprLoweringProps
  bodyPtrDefs compileEnv context venomState venomExecSemantics vyperState
  vyperLookup exprSimBufferStore exprSimProps valueEncodingProps valueTypingMemoryProps

Theorem tuple_local_bytes_compatible_head_ptr:
  compile_store_memory cenv (Var src) (Var p) dt ty sa = ((),sb) /\
  is_bytestring_type ty /\ is_bytestring_type dt /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  evaluate_type (get_tenv cx) dt = SOME entry.type /\
  value_has_type tv v /\ value_has_type entry.type v /\
  type_memory_bytes cenv dt = type_memory_size entry.type /\
  type_memory_size entry.type + 64 < dimword (:256) /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  lookup_var src s = SOME sw /\ lookup_var p s = SOME dw /\
  ptr_covers G tn src s (type_memory_size tv) /\
  ptr_val_ok cx ty v (Var src) G tn s /\
  ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx func cenv cx es s /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u G' tn' written.
    written <= type_memory_size tv /\ written <= type_memory_size entry.type /\
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) u /\
    ghost_inv d cenv cx
      (es with scopes := pre ++
        (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) G' tn' u /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+written) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tn'.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  `~is_word_type ty /\ ~is_word_type dt` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `compile_store_memory cenv (Var src) (Var p) dt dt sa = ((),sb)` by
    metis_tac[compile_store_memory_bytestring_compat_ptr] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n sw) m` by
    (fs[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def] >> metis_tac[]) >>
  drule_all bytestring_compatible_resources_ptr >> strip_tac >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory entry.type v (w2n sw) m` by
    metis_tac[bytestring_robust_representation_compat_ptr] >>
  `val_wf entry.type v` by
    (irule value_has_type_memory_wf >> first_assum ACCEPT_TAC) >>
  `val_in_memory entry.type v (w2n sw) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `ptr_covers G tn src s (32 + 32 * ((len+31) DIV 32))` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `eval_operand (Var src) s = SOME sw /\ eval_operand (Var p) s = SOME dw /\
   (!x. Var src = Var x ==> not_fresh_at sa x) /\
   (!x. Var p = Var x ==> not_fresh_at sa x)` by simp[eval_operand_def] >>
  `if is_word_type dt then sw = typed_val_to_w256 entry.type v
   else val_in_memory entry.type v (w2n sw) s.vs_memory` by simp[] >>
  `if is_bytestring_type dt then val_store_size entry.type v <= type_memory_size entry.type
   else type_memory_size entry.type <= type_memory_size entry.type` by simp[val_store_size_le] >>
  drule_all compile_store_memory_run_frame_with_capacity >> strip_tac >>
  `32 + 32 * ((len+31) DIV 32) = 32 + 32 * ((len+31) DIV 32)` by simp[] >>
  drule_all tuple_local_bytes_runtime_head_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `G'`, `tn'`, `32 + 32 * ((len+31) DIV 32)`] >> simp[]
QED
