(* A widened aggregate child store, with the control frame that puts the
   statement state relation back at the store's own endpoint. *)
Theory bodyIntCallWidenedChildStore
Ancestors
  bodyIntCallCopySharpRank exprSimAggregateChildren placeMemoryCopyEffect

Theorem intcall_widened_child_store_frame:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  (!ty tv. evaluate_type tenv ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv) /\
  fn_inst_ids_distinct func /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes ce dt = type_memory_size dtv /\
  type_memory_bytes ce st = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw) u.vs_memory /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  compile_store_memory_typed ce dp dt sp st a = ((),b) /\
  (!x. dp = Var x ==> not_fresh_at a x) /\
  (!x. sp = Var x ==> not_fresh_at a x) /\
  eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
  fn_has_code a b func /\ ~u.vs_halted /\
  u.vs_current_bb = a.cs_current_bb /\
  u.vs_inst_idx = LENGTH a.cs_current_insts /\
  stmt_state_rel ctx func ce cx es u /\ local_ptrs_reserved ce a /\
  (!name b0 sz. local_region ce es.scopes u name b0 sz ==>
     b0 + sz <= w2n dw \/ w2n dw + type_memory_size dtv <= b0) /\
  (ce.ce_is_ctor ==> !name tv' v' off.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (tv',v') ==>
     regions_disjoint off (type_memory_size tv') (w2n dw)
       (type_memory_size dtv)) ==>
  ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv) /\
      stmt_state_rel ctx func ce cx es t
Proof
  cheat
QED
