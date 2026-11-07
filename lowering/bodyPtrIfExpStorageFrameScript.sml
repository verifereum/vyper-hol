Theory bodyPtrIfExpStorageFrame
Ancestors
  slotCopyExecution copyExecution compileEnv valueEncoding vyperValue venomState words finite_map

Theorem ifexp_copy_scratch_not_fresh:
  sa.cs_next_var <= cs.cs_next_var /\ not_fresh_at sa x ==>
  !k. x <> slot_copy_var cs k
Proof
  simp[not_fresh_at_def, slot_copy_var_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `cs.cs_next_var+k` mp_tac) >> simp[]
QED

(* Whole-region bounds are captured before the copy, not recovered from a
   vv_post after memory writes. Only local pointer lookups need transport. *)
Theorem ifexp_copy_live_local_bounds_transport:
  (!name entry v sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) /\
    lookup_var v s = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w + type_memory_size entry.type <= b \/ b+capacity <= w2n w)) /\
  (!name v sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) ==>
    lookup_var v t = lookup_var v s) ==>
  !name entry v sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) /\
    lookup_var v t = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w + type_memory_size entry.type <= b \/ b+capacity <= w2n w)
Proof
  rpt strip_tac >> metis_tac[]
QED
