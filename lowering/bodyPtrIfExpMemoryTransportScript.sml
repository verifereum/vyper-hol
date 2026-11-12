Theory bodyPtrIfExpMemoryTransport
Ancestors
  bodyPtrDefs valueCopyBytes

(* Interpretation transport does not follow merely from buffer capacity. *)
Theorem ptr_mem_ok_transport:
  !cx src dst v op G tn s.
    ptr_mem_ok cx src v op G tn s /\
    (!tv. evaluate_type (get_tenv cx) dst = SOME tv ==>
      ?sv. evaluate_type (get_tenv cx) src = SOME sv /\
        (!a mem. val_in_memory sv v a mem ==> val_in_memory tv v a mem)) /\
    (!tv w. evaluate_type (get_tenv cx) dst = SOME tv /\
      eval_operand op s = SOME w /\ val_footprint tv v <> 0 ==>
      ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
        b <= w2n w /\ w2n w + val_store_size tv v <= b + sz) ==>
    ptr_mem_ok cx dst v op G tn s
Proof
  rw[ptr_mem_ok_def] >> metis_tac[]
QED

Theorem ptr_mem_ok_runtime_type:
  !cx src dst v op G tn s.
    ptr_mem_ok cx src v op G tn s /\
    evaluate_type (get_tenv cx) dst = evaluate_type (get_tenv cx) src ==>
    ptr_mem_ok cx dst v op G tn s
Proof
  rpt strip_tac >> irule ptr_mem_ok_transport >> conj_tac
  >- (gvs[ptr_mem_ok_def] >> metis_tac[]) >>
  qexists_tac `src` >> simp[]
QED

Theorem ptr_mem_ok_bytestring_transport:
  !cx src dst sv dv v op G tn s.
    is_bytestring_type src /\ is_bytestring_type dst /\
    evaluate_type (get_tenv cx) src = SOME sv /\
    evaluate_type (get_tenv cx) dst = SOME dv /\
    value_has_type sv v /\ value_has_type dv v /\
    ptr_mem_ok cx src v op G tn s ==>
    ptr_mem_ok cx dst v op G tn s
Proof
  rpt strip_tac >>
  `val_footprint sv v = val_footprint dv v` by
    (metis_tac[bytestring_val_footprint_eq]) >>
  `val_store_size sv v = val_store_size dv v` by
    (metis_tac[bytestring_val_store_size_eq]) >>
  gvs[ptr_mem_ok_def] >> rpt strip_tac
  >- (first_x_assum drule >> strip_tac >>
      metis_tac[bytestring_val_in_memory_transfer]) >>
  metis_tac[]
QED
