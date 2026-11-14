(* The three canonical snapshot stores share one declared-layout endpoint. *)
Theory bodyIntCallNRStageStoreDispatch
Ancestors
  bodyIntCallNRStageStores

Theorem intcall_stage_declared_snapshot:
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  value_has_type tv v /\ val_wf tv v /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  sa.cs_next_var <= sb.cs_next_var /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,MAX 32 (type_memory_size tv)) /\
  start.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  w2n dw + MAX 32 (type_memory_size tv) <= s.vs_alloca_next /\
  w2n dw + MAX 32 (type_memory_size tv) < dimword (:256) /\
  ((compile_store_memory ce src dst dty sty sa = ((),sb) /\
    is_word_type sty /\ is_word_type dty /\
    evaluate_type tenv dty = SOME tv /\ sw = typed_val_to_w256 tv v /\
    type_memory_bytes ce dty = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256) /\ fn_inst_ids_distinct func /\
    (!name b sz. local_region ce es.scopes s name b sz ==>
      regions_disjoint b sz (w2n dw) (type_memory_size tv)) /\
    (ce.ce_is_ctor ==> !name itv iv off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
      regions_disjoint off (type_memory_size itv) (w2n dw) (type_memory_size tv))) \/
   (compile_store_bytestring src dst sa = ((),sb) /\
    is_bytestring_type dty /\ evaluate_type (get_tenv cx) dty = SOME tv /\
    val_in_memory tv v (w2n sw) s.vs_memory /\
    type_memory_size tv < dimword (:256) /\
    (!name b sz. local_region ce es.scopes s name b sz ==>
      b+sz <= w2n dw \/ w2n dw+MAX 32 (type_memory_size tv) <= b) /\
    (ce.ce_is_ctor ==> !name itv iv off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
      regions_disjoint off (type_memory_size itv) (w2n dw) (MAX 32 (type_memory_size tv)))) \/
   (?stv. compile_store_memory ce src dst dty sty sa = ((),sb) /\
    evaluate_type tenv dty = SOME tv /\ evaluate_type tenv sty = SOME stv /\
    value_has_type stv v /\ type_memory_bytes ce dty = type_memory_size tv /\
    (if is_word_type sty then sw = typed_val_to_w256 stv v
     else val_in_memory stv v (w2n sw) s.vs_memory) /\
    type_memory_size tv + 64 < dimword (:256) /\ fn_inst_ids_distinct func /\
    (!name b sz. local_region ce es.scopes s name b sz ==>
      regions_disjoint b sz (w2n dw) (type_memory_size tv)) /\
    (ce.ce_is_ctor ==> !name itv iv off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
      regions_disjoint off (type_memory_size itv) (w2n dw) (type_memory_size tv)) /\
    (~(dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) ==>
      acyclic_struct_metadata ce.ce_struct_fields /\
      sfields_tenv_consistent ce.ce_struct_fields tenv /\
      (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
        ALL_DISTINCT (MAP FST fields) /\
        EVERY (\(fname,fty,sz). !tv.
          evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
      (!ty tv. evaluate_type tenv ty = SOME tv ==>
        type_memory_bytes ce ty = type_memory_size tv) /\
      type_widens_to tenv sty dty /\ val_wf tv v /\ val_wf stv v /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size tv <= w2n sw) /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size tv < dimword (:256)))) ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    typed_copy_effect ctx func sa sb s u (w2n dw) (MAX 32 (type_memory_size tv)) /\
    stmt_state_rel ctx func ce cx es u /\
    val_in_memory tv v (w2n dw) u.vs_memory /\ val_wf tv v /\
    eval_operand dst u = SOME dw /\
    (!x. dst = Var x ==> not_fresh_at sb x) /\
    FLOOKUP u.vs_allocas aid = SOME (w2n dw,MAX 32 (type_memory_size tv)) /\
    start.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    w2n dw + MAX 32 (type_memory_size tv) <= u.vs_alloca_next /\
    w2n dw + MAX 32 (type_memory_size tv) < dimword (:256) /\
    u.vs_alloca_next = s.vs_alloca_next /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op u = eval_operand op s)
Proof
  strip_tac
  >- (irule intcall_stage_word_snapshot >> simp[] >> metis_tac[])
  >- (irule intcall_stage_bytes_snapshot >> simp[] >> metis_tac[])
  >> drule_all intcall_stage_aggregate_snapshot >> simp[]
QED
