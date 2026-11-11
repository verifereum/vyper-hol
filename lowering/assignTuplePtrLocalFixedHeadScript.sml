(* Fixed-size aggregate local head. The source capacity is stated for the
   compiler's whole copy extent, not just the value's live footprint. *)
Theory assignTuplePtrLocalFixedHead
Ancestors
  assignTuplePtrLocalCopyGhost assignTuplePtrLocalCopyPath
  assignTuplePtrLocalCopyRun assignTuplePtrBoundary
  tupleTargetStoreProps tupleLocalStoreRun stmtSimDefs exprLoweringProps
  bodyPtrDefs compileEnv loweringStateRelDefs context venomState venomExecSemantics vyperState
  vyperLookup valueEncodingProps loweringPosts localPtrsProps exprSimProps

Theorem tuple_local_fixed_head_ptr:
  compile_store_memory cenv (Var src) (Var p) ty ty sa = ((),sb) /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME entry.type /\
  value_has_type entry.type v /\ val_wf entry.type v /\
  n = type_memory_size entry.type /\ type_memory_bytes cenv ty = n /\
  n + 64 < dimword (:256) /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  lookup_var src s = SOME sw /\ lookup_var p s = SOME dw /\
  ptr_covers G tn src s n /\
  ptr_val_ok cx ty v (Var src) G tn s /\
  ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx func cenv cx es s /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?tn'.
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) u /\
    ghost_inv d cenv cx
      (es with scopes := pre ++
        (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) G tn' u /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G tn'
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. lookup_var x u = lookup_var x s /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tn'.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  drule_all tuple_store_destination_region >> strip_tac >>
  `ptr_covers G tn p s n` by
    (`ptr_covers G tn p s sz` by metis_tac[ghost_inv_def] >>
     fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `n < dimword (:256)` by decide_tac >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory entry.type v (w2n sw) m` by
    (fs[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def] >> metis_tac[]) >>
  `val_in_memory entry.type v (w2n sw) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `eval_operand (Var src) s = SOME sw` by simp[eval_operand_def] >>
  `!x. Var src = Var x ==> not_fresh_at sa x` by simp[] >>
  `type_memory_bytes cenv ty = type_memory_size entry.type /\
   type_memory_size entry.type + 64 < dimword (:256)` by metis_tac[] >>
  drule_all tuple_local_copy_run_state_ptr >> strip_tac >>
  `n = type_memory_bytes cenv ty` by simp[] >>
  drule_all compile_fixed_copy_path_frames_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  gvs[] >> qexists_tac `tn'` >> simp[] >>
  reverse conj_tac >- (rpt strip_tac >> simp[]) >>
  irule local_copy_ghost_update_ptr >> simp[] >>
  conj_tac
  >- (fs[ghost_inv_def, stor_taint_ok_def] >>
      qpat_x_assum `u with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
      simp[venom_state_component_equality] >> strip_tac >> gvs[]) >>
  qpat_assum `ghost_inv _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`w2n sw`, `sa`, `type_memory_size entry.type`, `func`, `dw`] >>
  simp[val_footprint_le] >>
  conj_tac >- (rpt strip_tac >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `!off k. _` (qspec_then `0` mp_tac) >> simp[]) >>
  fs[stmt_state_rel_def, state_rel_def]
QED
