(* Aggregate endpoint in the singleton tuple-store interface. Fixed-size and
   rounded bytestring copies share the same run-existence setup. *)
Theory assignTuplePtrFixedSingleton
Ancestors
  assignTuplePtrLocalFixedHead assignTuplePtrLocalBytesHead assignTuplePtrBytesResources
  assignTuplePtrCopyEndpoint tupleTargetStoreRun tupleTargetStoreProps
  tupleLocalStoreRun bodyPtrDefs exprSimProps valueCopy exprLoweringProps
  venomState venomExecSemantics compileEnv context vyperState vyperLookup

Theorem tuple_target_local_aggregate_head_path_ptr:
  compile_tuple_store_all cenv [ty] [BaseTarget (NameTarget id)] [Var src] sa = ((),sb) /\
  assign_tuple_targets cx (BaseTarget (NameTarget id)) v es = (INL (),es') /\
  tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) ty tv /\
  tuple_target_layout es.scopes (BaseTarget (NameTarget id)) ty tv v /\
  value_has_type tv v /\ val_wf tv v /\
  ~is_word_type ty /\
  type_memory_size tv + 64 < dimword (:256) /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  lookup_var src s = SOME sw /\ ptr_covers G tn src s (type_memory_size tv) /\
  ptr_val_ok cx ty v (Var src) G tn s /\ ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx func cenv cx es s /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn' p sz dw.
    stmt_state_rel ctx func cenv cx es' t /\ ghost_inv d cenv cx es' G' tn' t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      op_taint tn' (Var x) = op_taint tn (Var x) /\ FLOOKUP G' x = FLOOKUP G x) /\
    (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
    local_region cenv es.scopes s id (w2n dw) sz /\ lookup_var p s = SOME dw /\
    type_memory_size tv <= sz /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size tv) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t)
Proof
  strip_tac >>
  gvs[tuple_target_aligned_local, tuple_target_layout_local] >>
  drule_all tuple_target_local_assignment >> strip_tac >>
  drule_all tuple_store_local_singleton_code >> simp[] >> strip_tac >>
  `?dw. lookup_var p s = SOME dw` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
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
   else type_memory_size entry.type <= type_memory_size entry.type` by
    simp[val_store_size_le] >>
  drule_all compile_store_memory_run_frame_with_capacity >> strip_tac >>
  suspend "copy"
QED

Resume tuple_target_local_aggregate_head_path_ptr[copy]:
  Cases_on `is_bytestring_type ty`
  >- (drule_all tuple_bytestring_member_resources_ptr >> strip_tac >>
      `ptr_covers G tn src s (32 + 32 * ((len+31) DIV 32))` by
        (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      `32 + 32 * ((len+31) DIV 32) = 32 + 32 * ((len+31) DIV 32)` by simp[] >>
      drule_all tuple_local_bytes_head_ptr >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      suspend "bytes_endpoint") >>
  `type_memory_size entry.type = type_memory_size entry.type` by simp[] >>
  drule_all tuple_local_fixed_head_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "endpoint"
QED

Resume tuple_target_local_aggregate_head_path_ptr[endpoint]:
  drule_all tuple_store_destination_region >> strip_tac >>
  `t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
   t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `G`, `tn'`, `p`, `sz`, `dw`] >>
  simp[stmt_state_rel_inst_idx, ghost_inv_inst_idx, lookup_var_def] >>
  rpt strip_tac >> gvs[lookup_var_def]
QED

Resume tuple_target_local_aggregate_head_path_ptr[bytes_endpoint]:
  drule_all tuple_store_destination_region >> strip_tac >>
  `t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
   t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `G'`, `tn'`, `p`, `sz`, `dw`] >>
  simp[stmt_state_rel_inst_idx, ghost_inv_inst_idx, lookup_var_def] >>
  rpt strip_tac >> gvs[lookup_var_def]
QED

Finalise tuple_target_local_aggregate_head_path_ptr
