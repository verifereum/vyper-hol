Theory bodyPtrIfExpStorageFrame
Ancestors
  slotCopyExecution copyExecution compileEnv loweringStateRelDefs valueEncoding vyperValue venomState words finite_map
  bodyPtrDefs ptrDiscipline appendStorageGhostPtr

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

(* ghost_kept_suffix_compose already supplies the no-memory-write kept
   boundary (take sb=sa and use equality to obtain its taint subset).
   Do not duplicate that general monotone-taint theorem here. *)
Theorem ifexp_copy_ghost_inv_transport:
  ghost_inv rty ce cx es G tn s /\
  t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) ==>
  ghost_inv rty ce cx es G' tn' t
Proof
  strip_tac >> fs[ghost_inv_def] >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     `lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)` by metis_tac[] >>
     conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
     metis_tac[]) >>
  conj_tac >-
    (Cases_on `rty` >> simp[return_buf_ptr_def] >>
     rename1 `SOME pair` >> PairCases_on `pair` >>
     gvs[return_buf_ptr_def] >>
     metis_tac[ptr_covers_def]) >>
  gvs[stor_taint_ok_def]
QED
