(* Current-state projections: no preservation of an old local value assumed. *)
Theory bodyPtrSubscriptBoundary
Ancestors
  bodyPtrDefs bodyPtrSubscriptCoverage

Theorem ghost_inv_local_representation:
  ghost_inv d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\
  mem_agree_outside tn.t_mem s.vs_memory mem ==>
  val_in_memory entry.type entry.value (w2n w) mem
Proof
  simp[ghost_inv_def] >> metis_tac[]
QED

Theorem ptr_vv_ok_nonmemory:
  p.ptr_location <> LocMemory ==>
  (ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s <=>
   op_taint tn p.ptr_operand = {} /\
   (p.ptr_location = LocCode ==> op_prov G p.ptr_operand = NONE) /\
   (!w ty k b.
      eval_operand p.ptr_operand s = SOME w /\
      evaluate_type (get_tenv cx) t = SOME ty /\
      w2n w <= w2n k /\ w2n k < w2n w + type_slot_size ty /\ b < 32 ==>
      (p.ptr_location = LocStorage /\ (k,b) IN tn.t_stor ==>
       dead_bytes (s.vs_accounts s.vs_call_ctx.cc_address).storage
         (w2n w) ty (w2n k) b) /\
      (p.ptr_location = LocTransient /\ (k,b) IN tn.t_trans ==>
       dead_bytes (s.vs_transient s.vs_call_ctx.cc_address)
         (w2n w) ty (w2n k) b)))
Proof
  simp[ptr_vv_ok_def]
QED

Theorem mapping_scratch_words:
  !b a sz:num.
    b <= a /\ a + 64 <= b + sz ==>
    (!i. i < 2 ==> b <= a + i * 32 /\ a + i * 32 + 32 <= b + sz)
Proof
  rpt strip_tac >>
  qspecl_then [`b`, `a`, `0`, `2`, `32`, `sz`, `i`]
    mp_tac array_buffer_child_interval >> simp[]
QED
