Theory bodyPtrIfExpMemoryTransport
Ancestors
  bodyPtrDefs

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
