(* Common local-store boundary.  The source slot and the actual write extent
   stay separate from the destination capacity, including coercing strings. *)
Theory assignTuplePtrLocalSingleton
Ancestors
  assignTuplePtrLocalCoerce assignTuplePtrLocalWordRuntime
  assignTuplePtrLocalFixedHead assignTuplePtrLocalCopyRun
  tupleLocalStoreRun bodyPtrDefs exprSimProps valueCopy exprLoweringProps
  venomState venomExecSemantics compileEnv context vyperState vyperLookup
  valueEncodingProps localPtrsProps stmtSimDeclStore
  assignTuplePtrLocalCompat assignTuplePtrCopyEndpoint

Theorem tuple_local_compatible_head_path_ptr:
  (if is_word_type ty then emit_void MSTORE [Var p; Var src]
   else compile_store_memory cenv (Var src) (Var p) vt ty) sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  (if is_word_type ty then
     sw = typed_val_to_w256 tv v /\ store_lays_out tv entry.type v /\
     op_taint tn (Var src) = {}
   else
     ~is_word_type vt /\ evaluate_type (get_tenv cx) vt = SOME entry.type /\
     value_has_type entry.type v /\ val_wf entry.type v /\
     value_has_type tv v /\ (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
     type_memory_bytes cenv vt = type_memory_size entry.type /\
     type_memory_size entry.type + 64 < dimword (:256) /\
     ptr_covers G tn src s (type_memory_size tv) /\
     ptr_val_ok cx ty v (Var src) G tn s) /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  lookup_var src s = SOME sw /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn' dw written.
    lookup_var p s = SOME dw /\
    local_region cenv es.scopes s id (w2n dw) sz /\
    written <= type_memory_size tv /\ written <= type_memory_size entry.type /\
    written <= sz /\
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) t /\
    ghost_inv d cenv cx
      (es with scopes := pre ++
        (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) G' tn' t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+written) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t)
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?dw. lookup_var p s = SOME dw` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  drule_all tuple_store_destination_region >> strip_tac >>
  Cases_on `is_word_type ty` >> gnvs[]
  >- suspend "word" >>
  Cases_on `is_bytestring_type ty`
  >- suspend "bytes" >>
  `vt = ty` by metis_tac[] >> gvs[] >>
  suspend "fixed"
QED

Resume tuple_local_compatible_head_path_ptr[word]:
  gvs[] >>
  `eval_operand (Var src) s = SOME (typed_val_to_w256 tv v)` by simp[eval_operand_def] >>
  drule_all tuple_local_word_runtime_head_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >>
  `type_memory_size entry.type = 32` by fs[store_lays_out_def] >>
  qexistsl_tac [`t`, `G`, `tn'`, `32`] >> simp[]
QED

Resume tuple_local_compatible_head_path_ptr[bytes]:
  `is_bytestring_type vt` by metis_tac[] >> gvs[] >>
  drule_all tuple_local_bytes_compatible_head_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `compile_store_memory cenv (Var src) (Var p) vt vt sa = ((),sb)` by
    metis_tac[compile_store_memory_bytestring_compat_ptr] >>
  drule tuple_local_copy_code_shape_ptr >> strip_tac >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `u with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`, `G'`, `tn'`, `written`] >>
  simp[stmt_state_rel_inst_idx, ghost_inv_inst_idx, lookup_var_def] >>
  rpt strip_tac >> gvs[lookup_var_def]
QED

Resume tuple_local_compatible_head_path_ptr[fixed]:
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `val_in_memory entry.type v (w2n sw) s.vs_memory` by
    (fs[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def] >>
     metis_tac[mem_agree_outside_def]) >>
  `eval_operand (Var src) s = SOME sw /\ eval_operand (Var p) s = SOME dw /\
   (!x. Var src = Var x ==> not_fresh_at sa x) /\
   (!x. Var p = Var x ==> not_fresh_at sa x)` by simp[eval_operand_def] >>
  `if is_word_type ty then sw = typed_val_to_w256 entry.type v
   else val_in_memory entry.type v (w2n sw) s.vs_memory` by simp[] >>
  `if is_bytestring_type ty then val_store_size entry.type v <= type_memory_size entry.type
   else type_memory_size entry.type <= type_memory_size entry.type` by simp[] >>
  drule_all compile_store_memory_run_frame_with_capacity >> strip_tac >>
  `type_memory_size entry.type = type_memory_size entry.type` by simp[] >>
  drule_all tuple_local_fixed_head_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule tuple_local_copy_code_shape_ptr >> strip_tac >>
  `t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
   t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `G`, `tn'`,
    `type_memory_size entry.type`] >>
  simp[stmt_state_rel_inst_idx, ghost_inv_inst_idx, lookup_var_def] >>
  rpt strip_tac >> gvs[lookup_var_def]
QED

Finalise tuple_local_compatible_head_path_ptr
