(* Scope-stable local compatibility and the singleton callback. *)
Theory assignTuplePtrLocalContract
Ancestors
  assignTuplePtrLocalSingleton tupleTargetStoreProps tupleTargetStoreRun
  stmtLowering exprLowering exprLoweringProps compileEnv context
  bodyPtrDefs stmtSimDeclStore valueTypingMemoryProps vyperState vyperLookup
  venomState venomExecSemantics emitHelper

Theorem tuple_local_compatible_singleton_code_ptr:
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME vt /\ (is_word_type vt = is_word_type ty) /\
  compile_tuple_store_all cenv [ty] [BaseTarget (NameTarget id)] [op] sa = ((),sb) ==>
  (if is_word_type ty then emit_void MSTORE [Var p;op]
   else compile_store_memory cenv op (Var p) vt ty) sa = ((),sb)
Proof
  Cases_on `is_word_type ty` >>
  simp[compile_tuple_store_all_def, compile_get_target_ptr_def,
       compile_assign_value_def, compile_store_at_loc_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt strip_tac >> gvs[comp_return_def, compile_store_at_loc_def,
    compile_assign_value_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[]
QED

Theorem tuple_scope_entry_layout_ptr:
  (!n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n scopes') =
       OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n scopes)) /\
  lookup_scopes id scopes = SOME entry ==>
  ?entry'. lookup_scopes id scopes' = SOME entry' /\
    entry'.type = entry.type /\ entry'.assignable = entry.assignable
Proof
  strip_tac >> first_x_assum (qspec_then `id` mp_tac) >>
  Cases_on `lookup_scopes id scopes'` >> simp[]
QED

Theorem tuple_local_compatibility_scope_ptr:
  (!n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n scopes') =
       OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n scopes)) /\
  (?id p sz vt entry. g = BaseTarget (NameTarget id) /\
    lookup_scopes id scopes = SOME entry /\ entry.assignable /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ cenv.ce_var_type id = SOME vt /\
    (is_word_type vt = is_word_type ty) /\
    (if is_word_type ty then store_lays_out tv entry.type v else
      (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
      evaluate_type (get_tenv cx) vt = SOME entry.type /\ value_has_type entry.type v /\
      type_memory_bytes cenv ty = type_memory_size tv /\
      type_memory_bytes cenv vt = type_memory_size entry.type /\
      0 < type_memory_size entry.type /\ type_memory_size entry.type + 64 < dimword(:256))) ==>
  ?id p sz vt entry. g = BaseTarget (NameTarget id) /\
    lookup_scopes id scopes' = SOME entry /\ entry.assignable /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ cenv.ce_var_type id = SOME vt /\
    (is_word_type vt = is_word_type ty) /\
    (if is_word_type ty then store_lays_out tv entry.type v else
      (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
      evaluate_type (get_tenv cx) vt = SOME entry.type /\ value_has_type entry.type v /\
      type_memory_bytes cenv ty = type_memory_size tv /\
      type_memory_bytes cenv vt = type_memory_size entry.type /\
      0 < type_memory_size entry.type /\ type_memory_size entry.type + 64 < dimword(:256))
Proof
  strip_tac >> drule_all tuple_scope_entry_layout_ptr >> strip_tac >>
  qexistsl_tac [`id`, `p`, `sz`, `vt`, `entry'`] >> simp[]
QED

Theorem tuple_local_compatibility_source_ptr:
  (?id p sz vt entry. g = BaseTarget (NameTarget id) /\
    lookup_scopes id scopes = SOME entry /\ entry.assignable /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ cenv.ce_var_type id = SOME vt /\
    (is_word_type vt = is_word_type ty) /\
    (if is_word_type ty then store_lays_out tv entry.type v else
      (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
      evaluate_type (get_tenv cx) vt = SOME entry.type /\ value_has_type entry.type v /\
      type_memory_bytes cenv ty = type_memory_size tv /\
      type_memory_bytes cenv vt = type_memory_size entry.type /\
      0 < type_memory_size entry.type /\ type_memory_size entry.type + 64 < dimword(:256))) ==>
  (?bt. g = BaseTarget bt) /\ tuple_source_target cx scopes g tv
Proof
  strip_tac >> simp[tuple_source_target_def] >> metis_tac[]
QED

Theorem tuple_local_compatibility_callback_ptr:
  compile_tuple_store_all cenv [ty] [g] [Var src] sa = ((),sb) /\
  assign_tuple_targets cx g v es = (INL (),es') /\
  (?id p sz vt entry. g = BaseTarget (NameTarget id) /\
    lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ cenv.ce_var_type id = SOME vt /\
    (is_word_type vt = is_word_type ty) /\
    (if is_word_type ty then store_lays_out tv entry.type v else
      (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
      evaluate_type (get_tenv cx) vt = SOME entry.type /\ value_has_type entry.type v /\
      type_memory_bytes cenv ty = type_memory_size tv /\
      type_memory_bytes cenv vt = type_memory_size entry.type /\
      0 < type_memory_size entry.type /\ type_memory_size entry.type + 64 < dimword(:256))) /\
  value_has_type tv v /\ val_wf tv v /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  lookup_var src s = SOME sw /\ (is_word_type ty ==> sw = typed_val_to_w256 tv v) /\
  (~is_word_type ty ==> ptr_covers G tn src s (type_memory_size tv)) /\
  ptr_val_ok cx ty v (Var src) G tn s /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'. stmt_state_rel ctx func cenv cx es' t /\ ghost_inv d cenv cx es' G' tn' t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
    ((t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem) \/
     ?id dst dsz written. local_region cenv es.scopes s id dst dsz /\
       written <= type_memory_size tv /\ written <= dsz /\
       (!i. ~(dst <= i /\ i < dst+written) ==>
         mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
         (i IN tn'.t_mem <=> i IN tn.t_mem))) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t)
Proof
  strip_tac >> gvs[] >>
  drule_all tuple_target_local_assignment >> strip_tac >> gvs[] >>
  drule_all tuple_local_compatible_singleton_code_ptr >> strip_tac >>
  `if is_word_type ty then
     sw = typed_val_to_w256 tv v /\ store_lays_out tv entry.type v /\
     op_taint tn (Var src) = {}
   else
     ~is_word_type vt /\ evaluate_type (get_tenv cx) vt = SOME entry.type /\
     value_has_type entry.type v /\ val_wf entry.type v /\
     value_has_type tv v /\ (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
     type_memory_bytes cenv vt = type_memory_size entry.type /\
     type_memory_size entry.type + 64 < dimword (:256) /\
     ptr_covers G tn src s (type_memory_size tv) /\
     ptr_val_ok cx ty v (Var src) G tn s` by
    (Cases_on `is_word_type ty` >> fs[ptr_val_ok_def] >>
     metis_tac[value_has_type_memory_wf]) >>
  drule_all tuple_local_compatible_head_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >>
  disj2_tac >> qexistsl_tac [`id`, `w2n dw`, `sz`, `written`] >> simp[]
QED
